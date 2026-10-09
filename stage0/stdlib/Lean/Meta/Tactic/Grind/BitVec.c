// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.BitVec
// Imports: import Init.Grind import Init.Data.BitVec.Basic import Lean.Meta.LitValues import Lean.ToExpr import Lean.Meta.Tactic.Grind.Simp public import Lean.Meta.Tactic.Grind.PropagatorAttr
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_rotateRight(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_BitVec_append___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_BitVec_extractLsb___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
lean_object* l_BitVec_not(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* l_BitVec_signExtend(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_setWidth(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_rotateLeft(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_clz(lean_object*, lean_object*);
lean_object* l_BitVec_toInt(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_BitVec_replicate(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_cpop(lean_object*, lean_object*);
lean_object* l_BitVec_extractLsb_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_sshiftRight(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofInt(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 11, .m_data = "eval_congr₁"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(241, 189, 19, 187, 204, 201, 25, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__8_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__9_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 11, .m_data = "eval_congr₂"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 51, 240, 102, 22, 126, 207, 87)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVNot___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVNot___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVNot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Complement"};
static const lean_object* l_Lean_Meta_Grind_propagateBVNot___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVNot___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBVNot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "complement"};
static const lean_object* l_Lean_Meta_Grind_propagateBVNot___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVNot___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVNot___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBVNot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 52, 244, 64, 3, 58, 115, 79)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVNot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVNot___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVNot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(168, 254, 142, 44, 189, 175, 152, 168)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVNot___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVNot___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVNot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVNot___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVNot___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVNot___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVNot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVNot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVNot___regBuiltin_Lean_Meta_Grind_propagateBVNot_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_524020944____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVNot___regBuiltin_Lean_Meta_Grind_propagateBVNot_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_524020944____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVClz___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVClz___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVClz___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "clz"};
static const lean_object* l_Lean_Meta_Grind_propagateBVClz___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVClz___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVClz___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVClz___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVClz___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVClz___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 156, 207, 111, 211, 81, 174, 218)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVClz___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVClz___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVClz___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVClz___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVClz___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVClz___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVClz(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVClz___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVClz___regBuiltin_Lean_Meta_Grind_propagateBVClz_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3163129259____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVClz___regBuiltin_Lean_Meta_Grind_propagateBVClz_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3163129259____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVCpop___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVCpop___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVCpop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cpop"};
static const lean_object* l_Lean_Meta_Grind_propagateBVCpop___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVCpop___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVCpop___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVCpop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVCpop___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVCpop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 25, 40, 162, 224, 189, 205, 182)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVCpop___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVCpop___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVCpop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVCpop___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVCpop___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVCpop___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVCpop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVCpop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVCpop___regBuiltin_Lean_Meta_Grind_propagateBVCpop_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4094280043____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVCpop___regBuiltin_Lean_Meta_Grind_propagateBVCpop_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4094280043____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVMsb___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVMsb___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVMsb___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "msb"};
static const lean_object* l_Lean_Meta_Grind_propagateBVMsb___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVMsb___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVMsb___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVMsb___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVMsb___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVMsb___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 159, 101, 244, 244, 236, 42, 193)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVMsb___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVMsb___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVMsb___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVMsb___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVMsb___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVMsb___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVMsb(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVMsb___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVMsb___regBuiltin_Lean_Meta_Grind_propagateBVMsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1379739246____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVMsb___regBuiltin_Lean_Meta_Grind_propagateBVMsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1379739246____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToNat___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToNat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVToNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNat"};
static const lean_object* l_Lean_Meta_Grind_propagateBVToNat___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVToNat___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVToNat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVToNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVToNat___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVToNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 44, 53, 46, 180, 233, 253, 99)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVToNat___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVToNat___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVToNat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVToNat___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVToNat___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVToNat___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToNat___regBuiltin_Lean_Meta_Grind_propagateBVToNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1265925494____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToNat___regBuiltin_Lean_Meta_Grind_propagateBVToNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1265925494____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToInt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToInt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVToInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toInt"};
static const lean_object* l_Lean_Meta_Grind_propagateBVToInt___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVToInt___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVToInt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVToInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVToInt___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVToInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(36, 9, 44, 71, 206, 78, 188, 190)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVToInt___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVToInt___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVToInt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVToInt___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVToInt___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVToInt___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToInt___regBuiltin_Lean_Meta_Grind_propagateBVToInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2998338308____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToInt___regBuiltin_Lean_Meta_Grind_propagateBVToInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2998338308____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVOfNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Grind_propagateBVOfNat___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVOfNat___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVOfNat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVOfNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVOfNat___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVOfNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVOfNat___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVOfNat___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1693823724____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1693823724____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVOfInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofInt"};
static const lean_object* l_Lean_Meta_Grind_propagateBVOfInt___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVOfInt___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVOfInt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVOfInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVOfInt___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVOfInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 33, 171, 14, 158, 104, 202, 91)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVOfInt___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVOfInt___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_16048587____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_16048587____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVSetWidth___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "setWidth"};
static const lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVSetWidth___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVSetWidth___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVSetWidth___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVSetWidth___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVSetWidth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 6, 252, 142, 19, 176, 54, 12)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVSetWidth___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVSignExtend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "signExtend"};
static const lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVSignExtend___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVSignExtend___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVSignExtend___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVSignExtend___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVSignExtend___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 113, 32, 164, 54, 200, 3, 175)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVSignExtend___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "extractLsb'"};
static const lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 201, 218, 12, 248, 124, 75, 23)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4241407876____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4241407876____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVExtractLsb___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "extractLsb"};
static const lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 192, 253, 234, 186, 255, 105, 184)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3429100332____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3429100332____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVReplicate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "replicate"};
static const lean_object* l_Lean_Meta_Grind_propagateBVReplicate___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVReplicate___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVReplicate___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVReplicate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVReplicate___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVReplicate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 123, 74, 120, 175, 214, 39, 20)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVReplicate___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVReplicate___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3327375609____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3327375609____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAnd___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAnd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVAnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAnd"};
static const lean_object* l_Lean_Meta_Grind_propagateBVAnd___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVAnd___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBVAnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAnd"};
static const lean_object* l_Lean_Meta_Grind_propagateBVAnd___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVAnd___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVAnd___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBVAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 205, 8, 181, 48, 134, 168, 175)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVAnd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVAnd___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 171, 107, 112, 94, 43, 106, 200)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVAnd___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVAnd___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVAnd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVAnd___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVAnd___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVAnd___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAnd___regBuiltin_Lean_Meta_Grind_propagateBVAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_317501673____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAnd___regBuiltin_Lean_Meta_Grind_propagateBVAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_317501673____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVOr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HOr"};
static const lean_object* l_Lean_Meta_Grind_propagateBVOr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVOr___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBVOr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "hOr"};
static const lean_object* l_Lean_Meta_Grind_propagateBVOr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVOr___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVOr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBVOr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 77, 185, 226, 52, 149, 89, 139)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVOr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVOr___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVOr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(45, 86, 165, 237, 21, 139, 25, 132)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVOr___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVOr___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVOr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVOr___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVOr___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVOr___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOr___regBuiltin_Lean_Meta_Grind_propagateBVOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4272827602____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOr___regBuiltin_Lean_Meta_Grind_propagateBVOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4272827602____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVXor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVXor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVXor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HXor"};
static const lean_object* l_Lean_Meta_Grind_propagateBVXor___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVXor___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBVXor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hXor"};
static const lean_object* l_Lean_Meta_Grind_propagateBVXor___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVXor___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVXor___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBVXor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 198, 212, 133, 26, 7, 147, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVXor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVXor___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVXor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 159, 33, 254, 118, 42, 120, 166)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVXor___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVXor___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVXor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVXor___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVXor___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVXor___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVXor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVXor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVXor___regBuiltin_Lean_Meta_Grind_propagateBVXor_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1120302969____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVXor___regBuiltin_Lean_Meta_Grind_propagateBVXor_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1120302969____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAppend___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAppend___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "HAppend"};
static const lean_object* l_Lean_Meta_Grind_propagateBVAppend___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVAppend___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBVAppend___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "hAppend"};
static const lean_object* l_Lean_Meta_Grind_propagateBVAppend___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVAppend___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVAppend___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBVAppend___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 35, 233, 160, 196, 216, 250, 31)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVAppend___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVAppend___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVAppend___closed__1_value),LEAN_SCALAR_PTR_LITERAL(181, 97, 51, 176, 35, 131, 5, 233)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVAppend___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVAppend___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVAppend___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVAppend___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVAppend___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVAppend___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAppend(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAppend___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4057925374____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4057925374____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVShiftLeft___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "shiftLeft"};
static const lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVShiftLeft___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVShiftLeft___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVShiftLeft___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVShiftLeft___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVShiftLeft___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 17, 136, 59, 111, 1, 62, 62)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVShiftLeft___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVShiftLeft___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVShiftLeft___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVShiftLeft___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3262547096____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3262547096____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVUShiftRight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ushiftRight"};
static const lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVUShiftRight___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVUShiftRight___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVUShiftRight___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVUShiftRight___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVUShiftRight___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 43, 145, 207, 67, 123, 27, 127)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVUShiftRight___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVUShiftRight___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVUShiftRight___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVUShiftRight___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVUShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVUShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1878785357____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVUShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVUShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1878785357____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVSShiftRight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "sshiftRight"};
static const lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVSShiftRight___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVSShiftRight___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVSShiftRight___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVSShiftRight___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVSShiftRight___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 65, 29, 246, 207, 155, 165, 148)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVSShiftRight___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVSShiftRight___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVSShiftRight___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVSShiftRight___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVSShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3342532823____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVSShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3342532823____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVRotateLeft___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "rotateLeft"};
static const lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVRotateLeft___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVRotateLeft___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVRotateLeft___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVRotateLeft___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVRotateLeft___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 181, 93, 155, 164, 43, 234, 184)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVRotateLeft___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVRotateLeft___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVRotateLeft___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVRotateLeft___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateLeft___regBuiltin_Lean_Meta_Grind_propagateBVRotateLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1541346404____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateLeft___regBuiltin_Lean_Meta_Grind_propagateBVRotateLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1541346404____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateRight___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateRight___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVRotateRight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "rotateRight"};
static const lean_object* l_Lean_Meta_Grind_propagateBVRotateRight___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVRotateRight___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVRotateRight___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVRotateRight___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVRotateRight___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVRotateRight___closed__0_value),LEAN_SCALAR_PTR_LITERAL(208, 30, 240, 114, 51, 110, 152, 157)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVRotateRight___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVRotateRight___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVRotateRight___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVRotateRight___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVRotateRight___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVRotateRight___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateRight___regBuiltin_Lean_Meta_Grind_propagateBVRotateRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2456321972____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateRight___regBuiltin_Lean_Meta_Grind_propagateBVRotateRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2456321972____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "HShiftLeft"};
static const lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "hShiftLeft"};
static const lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 217, 51, 89, 252, 54, 156, 169)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__1_value),LEAN_SCALAR_PTR_LITERAL(181, 245, 218, 3, 224, 235, 179, 59)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVHShiftLeft___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2458924947____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2458924947____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVHShiftRight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "HShiftRight"};
static const lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftRight___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBVHShiftRight___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hShiftRight"};
static const lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftRight___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVHShiftRight___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftRight___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 35, 163, 146, 1, 76, 65, 75)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVHShiftRight___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftRight___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftRight___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 65, 204, 240, 51, 126, 9, 157)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftRight___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVHShiftRight___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVHShiftRight___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftRight___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVHShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1131064821____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVHShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1131064821____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVGetLsbD___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "getLsbD"};
static const lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetLsbD___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVGetLsbD___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVGetLsbD___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVGetLsbD___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVGetLsbD___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 226, 96, 197, 228, 245, 77)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetLsbD___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVGetLsbD___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVGetLsbD___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetLsbD___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetLsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetLsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1075602488____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetLsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetLsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1075602488____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVGetMsbD___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "getMsbD"};
static const lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetMsbD___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVGetMsbD___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVGetMsbD___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVGetMsbD___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVGetMsbD___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 67, 87, 86, 230, 172, 21, 28)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetMsbD___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_propagateBVGetMsbD___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_propagateBVGetMsbD___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetMsbD___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetMsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetMsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1507361668____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetMsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetMsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1507361668____hygCtx___hyg_9____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVGetElem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "GetElem"};
static const lean_object* l_Lean_Meta_Grind_propagateBVGetElem___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBVGetElem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "getElem"};
static const lean_object* l_Lean_Meta_Grind_propagateBVGetElem___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVGetElem___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 233, 51, 226, 114, 128, 218, 11)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVGetElem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 164, 165, 74, 8, 252, 37, 122)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVGetElem___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBVGetElem___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "instGetElemNatBoolLt"};
static const lean_object* l_Lean_Meta_Grind_propagateBVGetElem___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVGetElem___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVGetElem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__3_value),LEAN_SCALAR_PTR_LITERAL(185, 53, 23, 137, 179, 122, 210, 184)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVGetElem___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBVGetElem___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "w"};
static const lean_object* l_Lean_Meta_Grind_propagateBVGetElem___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVGetElem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__5_value),LEAN_SCALAR_PTR_LITERAL(238, 128, 149, 182, 175, 207, 218, 129)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVGetElem___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBVGetElem___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "getElem_congr"};
static const lean_object* l_Lean_Meta_Grind_propagateBVGetElem___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVGetElem___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVGetElem___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVGetElem___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__7_value),LEAN_SCALAR_PTR_LITERAL(245, 93, 18, 95, 170, 237, 152, 145)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVGetElem___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetElem___regBuiltin_Lean_Meta_Grind_propagateBVGetElem_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2454187461____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetElem___regBuiltin_Lean_Meta_Grind_propagateBVGetElem_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2454187461____hygCtx___hyg_9____boxed(lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__1));
v___x_6_ = l_Lean_mkConst(v___x_5_, v___x_4_);
return v___x_6_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(lean_object* v_n_7_, lean_object* v_v_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_16_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__2);
v___x_17_ = l_Lean_mkNatLit(v_n_7_);
v___x_18_ = l_Lean_Expr_app___override(v___x_16_, v___x_17_);
v___x_19_ = l_Lean_Meta_mkNumeral(v___x_18_, v_v_8_, v_a_11_, v_a_12_, v_a_13_, v_a_14_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_21_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_a_20_);
lean_dec_ref_known(v___x_19_, 1);
v___x_21_ = l_Lean_Meta_Sym_shareCommon(v_a_20_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_);
return v___x_21_;
}
else
{
return v___x_19_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_7_ = stack[0].m_obj;
lean_object* v_v_8_ = stack[1].m_obj;
lean_object* v_a_9_ = stack[2].m_obj;
lean_object* v_a_10_ = stack[3].m_obj;
lean_object* v_a_11_ = stack[4].m_obj;
lean_object* v_a_12_ = stack[5].m_obj;
lean_object* v_a_13_ = stack[6].m_obj;
lean_object* v_a_14_ = stack[7].m_obj;
lean_object* v_res_22_;
v_res_22_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_n_7_, v_v_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_);
stack->m_obj
 = v_res_22_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___boxed(lean_object* v_n_23_, lean_object* v_v_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_n_23_, v_v_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_, v_a_30_);
lean_dec(v_a_30_);
lean_dec_ref(v_a_29_);
lean_dec(v_a_28_);
lean_dec_ref(v_a_27_);
lean_dec(v_a_26_);
lean_dec_ref(v_a_25_);
return v_res_32_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit(lean_object* v_n_33_, lean_object* v_v_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_n_33_, v_v_34_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_);
return v___x_46_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_33_ = stack[0].m_obj;
lean_object* v_v_34_ = stack[1].m_obj;
lean_object* v_a_35_ = stack[2].m_obj;
lean_object* v_a_36_ = stack[3].m_obj;
lean_object* v_a_37_ = stack[4].m_obj;
lean_object* v_a_38_ = stack[5].m_obj;
lean_object* v_a_39_ = stack[6].m_obj;
lean_object* v_a_40_ = stack[7].m_obj;
lean_object* v_a_41_ = stack[8].m_obj;
lean_object* v_a_42_ = stack[9].m_obj;
lean_object* v_a_43_ = stack[10].m_obj;
lean_object* v_a_44_ = stack[11].m_obj;
lean_object* v_res_47_;
v_res_47_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit(v_n_33_, v_v_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_);
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___boxed(lean_object* v_n_48_, lean_object* v_v_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit(v_n_48_, v_v_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
lean_dec(v_a_55_);
lean_dec_ref(v_a_54_);
lean_dec(v_a_53_);
lean_dec_ref(v_a_52_);
lean_dec(v_a_51_);
lean_dec(v_a_50_);
return v_res_61_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__3(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_box(0);
v___x_68_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__2));
v___x_69_ = l_Lean_mkConst(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__6(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_74_ = lean_box(0);
v___x_75_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__5));
v___x_76_ = l_Lean_mkConst(v___x_75_, v___x_74_);
return v___x_76_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(uint8_t v_b_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
if (v_b_77_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__3);
v___x_86_ = l_Lean_Meta_Sym_shareCommon(v___x_85_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
return v___x_86_;
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__6, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__6);
v___x_88_ = l_Lean_Meta_Sym_shareCommon(v___x_87_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
return v___x_88_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_77_ = stack[0].m_num;
lean_object* v_a_78_ = stack[1].m_obj;
lean_object* v_a_79_ = stack[2].m_obj;
lean_object* v_a_80_ = stack[3].m_obj;
lean_object* v_a_81_ = stack[4].m_obj;
lean_object* v_a_82_ = stack[5].m_obj;
lean_object* v_a_83_ = stack[6].m_obj;
lean_object* v_res_89_;
v_res_89_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v_b_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
stack->m_obj
 = v_res_89_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___boxed(lean_object* v_b_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
uint8_t v_b_boxed_98_; lean_object* v_res_99_; 
v_b_boxed_98_ = lean_unbox(v_b_90_);
v_res_99_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v_b_boxed_98_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
return v_res_99_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit(uint8_t v_b_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v_b_100_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
return v___x_112_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_100_ = stack[0].m_num;
lean_object* v_a_101_ = stack[1].m_obj;
lean_object* v_a_102_ = stack[2].m_obj;
lean_object* v_a_103_ = stack[3].m_obj;
lean_object* v_a_104_ = stack[4].m_obj;
lean_object* v_a_105_ = stack[5].m_obj;
lean_object* v_a_106_ = stack[6].m_obj;
lean_object* v_a_107_ = stack[7].m_obj;
lean_object* v_a_108_ = stack[8].m_obj;
lean_object* v_a_109_ = stack[9].m_obj;
lean_object* v_a_110_ = stack[10].m_obj;
lean_object* v_res_113_;
v_res_113_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit(v_b_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
stack->m_obj
 = v_res_113_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___boxed(lean_object* v_b_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
uint8_t v_b_boxed_126_; lean_object* v_res_127_; 
v_b_boxed_126_ = lean_unbox(v_b_114_);
v_res_127_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit(v_b_boxed_126_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec(v_a_115_);
return v_res_127_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f___redArg(lean_object* v_x_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_st_ref_get(v_a_129_);
v___x_136_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_135_, v_x_128_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
lean_dec(v___x_135_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; lean_object* v___x_138_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_137_);
lean_dec_ref_known(v___x_136_, 1);
v___x_138_ = l_Lean_Meta_getBitVecValue_x3f(v_a_137_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
return v___x_138_;
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
v_a_139_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_136_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_136_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_128_ = stack[0].m_obj;
lean_object* v_a_129_ = stack[1].m_obj;
lean_object* v_a_130_ = stack[2].m_obj;
lean_object* v_a_131_ = stack[3].m_obj;
lean_object* v_a_132_ = stack[4].m_obj;
lean_object* v_a_133_ = stack[5].m_obj;
lean_object* v_res_147_;
v_res_147_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f___redArg(v_x_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
stack->m_obj
 = v_res_147_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f___redArg___boxed(lean_object* v_x_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f___redArg(v_x_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
return v_res_155_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f(lean_object* v_x_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f___redArg(v_x_156_, v_a_157_, v_a_163_, v_a_164_, v_a_165_, v_a_166_);
return v___x_168_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_156_ = stack[0].m_obj;
lean_object* v_a_157_ = stack[1].m_obj;
lean_object* v_a_158_ = stack[2].m_obj;
lean_object* v_a_159_ = stack[3].m_obj;
lean_object* v_a_160_ = stack[4].m_obj;
lean_object* v_a_161_ = stack[5].m_obj;
lean_object* v_a_162_ = stack[6].m_obj;
lean_object* v_a_163_ = stack[7].m_obj;
lean_object* v_a_164_ = stack[8].m_obj;
lean_object* v_a_165_ = stack[9].m_obj;
lean_object* v_a_166_ = stack[10].m_obj;
lean_object* v_res_169_;
v_res_169_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f(v_x_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_);
stack->m_obj
 = v_res_169_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f___boxed(lean_object* v_x_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f(v_x_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec(v_a_171_);
return v_res_182_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_191_ = l_Lean_Level_ofNat(v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__5(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_box(0);
v___x_193_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4);
v___x_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__6(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__5, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__5);
v___x_196_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4);
v___x_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___x_195_);
return v___x_197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__7(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__6, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__6);
v___x_199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__3));
v___x_200_ = l_Lean_mkConst(v___x_199_, v___x_198_);
return v___x_200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__5, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__5);
v___x_207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__10));
v___x_208_ = l_Lean_mkConst(v___x_207_, v___x_206_);
return v___x_208_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(lean_object* v_e_209_, lean_object* v_eval_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_a_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_a_222_ = l_Lean_Expr_appArg_x21(v_e_209_);
v___x_223_ = lean_st_ref_get(v_a_211_);
lean_inc_ref(v_a_222_);
v___x_224_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_223_, v_a_222_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
lean_dec(v___x_223_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_226_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc_n(v_a_225_, 2);
lean_dec_ref_known(v___x_224_, 1);
lean_inc(v_a_220_);
lean_inc_ref(v_a_219_);
lean_inc(v_a_218_);
lean_inc_ref(v_a_217_);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
lean_inc(v_a_212_);
lean_inc(v_a_211_);
v___x_226_ = lean_apply_12(v_eval_210_, v_a_225_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, lean_box(0));
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_277_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_277_ == 0)
{
v___x_229_ = v___x_226_;
v_isShared_230_ = v_isSharedCheck_277_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_226_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_277_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
if (lean_obj_tag(v_a_227_) == 1)
{
lean_object* v_val_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
lean_del_object(v___x_229_);
v_val_231_ = lean_ctor_get(v_a_227_, 0);
lean_inc_n(v_val_231_, 2);
lean_dec_ref_known(v_a_227_, 1);
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_box(0);
lean_inc(v_a_220_);
lean_inc_ref(v_a_219_);
lean_inc(v_a_218_);
lean_inc_ref(v_a_217_);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
lean_inc(v_a_212_);
lean_inc(v_a_211_);
v___x_234_ = lean_grind_internalize(v_val_231_, v___x_232_, v___x_233_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v___x_235_; 
lean_dec_ref_known(v___x_234_, 1);
lean_inc(v_a_220_);
lean_inc_ref(v_a_219_);
lean_inc(v_a_218_);
lean_inc_ref(v_a_217_);
lean_inc_ref(v_e_209_);
v___x_235_ = lean_infer_type(v_e_209_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_237_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v___x_235_, 1);
lean_inc(v_a_220_);
lean_inc_ref(v_a_219_);
lean_inc(v_a_218_);
lean_inc_ref(v_a_217_);
lean_inc_ref(v_a_222_);
v___x_237_ = lean_infer_type(v_a_222_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v___x_237_, 1);
v___x_239_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__7, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__7);
v___x_240_ = l_Lean_Expr_appFn_x21(v_e_209_);
lean_inc(v_val_231_);
lean_inc(v_a_225_);
lean_inc_ref(v_a_222_);
lean_inc(v_a_236_);
v___x_241_ = l_Lean_mkApp6(v___x_239_, v_a_238_, v_a_236_, v___x_240_, v_a_222_, v_a_225_, v_val_231_);
lean_inc(v_a_220_);
lean_inc_ref(v_a_219_);
lean_inc(v_a_218_);
lean_inc_ref(v_a_217_);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
lean_inc(v_a_212_);
lean_inc(v_a_211_);
v___x_242_ = lean_grind_mk_eq_proof(v_a_222_, v_a_225_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; lean_object* v___x_248_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_243_);
lean_dec_ref_known(v___x_242_, 1);
v___x_244_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11);
lean_inc(v_val_231_);
v___x_245_ = l_Lean_mkAppB(v___x_244_, v_a_236_, v_val_231_);
v___x_246_ = l_Lean_mkAppB(v___x_241_, v_a_243_, v___x_245_);
v___x_247_ = 0;
v___x_248_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_209_, v_val_231_, v___x_246_, v___x_247_, v_a_211_, v_a_213_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
return v___x_248_;
}
else
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
lean_dec_ref(v___x_241_);
lean_dec(v_a_236_);
lean_dec(v_val_231_);
lean_dec_ref(v_e_209_);
v_a_249_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_242_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_242_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
lean_dec(v_a_236_);
lean_dec(v_val_231_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_222_);
lean_dec_ref(v_e_209_);
v_a_257_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_237_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_237_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec(v_val_231_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_222_);
lean_dec_ref(v_e_209_);
v_a_265_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_235_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_235_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
else
{
lean_dec(v_val_231_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_222_);
lean_dec_ref(v_e_209_);
return v___x_234_;
}
}
else
{
lean_object* v___x_273_; lean_object* v___x_275_; 
lean_dec(v_a_227_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_222_);
lean_dec_ref(v_e_209_);
v___x_273_ = lean_box(0);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_273_);
v___x_275_ = v___x_229_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec(v_a_225_);
lean_dec_ref(v_a_222_);
lean_dec_ref(v_e_209_);
v_a_278_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_226_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_226_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v_a_222_);
lean_dec_ref(v_eval_210_);
lean_dec_ref(v_e_209_);
v_a_286_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_224_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_224_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_209_ = stack[0].m_obj;
lean_object* v_eval_210_ = stack[1].m_obj;
lean_object* v_a_211_ = stack[2].m_obj;
lean_object* v_a_212_ = stack[3].m_obj;
lean_object* v_a_213_ = stack[4].m_obj;
lean_object* v_a_214_ = stack[5].m_obj;
lean_object* v_a_215_ = stack[6].m_obj;
lean_object* v_a_216_ = stack[7].m_obj;
lean_object* v_a_217_ = stack[8].m_obj;
lean_object* v_a_218_ = stack[9].m_obj;
lean_object* v_a_219_ = stack[10].m_obj;
lean_object* v_a_220_ = stack[11].m_obj;
lean_object* v_res_294_;
v_res_294_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_209_, v_eval_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___boxed(lean_object* v_e_295_, lean_object* v_eval_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_295_, v_eval_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec(v_a_297_);
return v_res_308_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__2(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__6, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__6);
v___x_315_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4);
v___x_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
return v___x_316_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__3(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__2, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__2);
v___x_318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__1));
v___x_319_ = l_Lean_mkConst(v___x_318_, v___x_317_);
return v___x_319_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(lean_object* v_e_320_, lean_object* v_eval_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_a_u2082_333_; lean_object* v___x_334_; lean_object* v_a_u2081_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_a_u2082_333_ = l_Lean_Expr_appArg_x21(v_e_320_);
v___x_334_ = l_Lean_Expr_appFn_x21(v_e_320_);
v_a_u2081_335_ = l_Lean_Expr_appArg_x21(v___x_334_);
v___x_336_ = lean_st_ref_get(v_a_322_);
lean_inc_ref(v_a_u2081_335_);
v___x_337_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_336_, v_a_u2081_335_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v___x_336_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
v___x_339_ = lean_st_ref_get(v_a_322_);
lean_inc_ref(v_a_u2082_333_);
v___x_340_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_339_, v_a_u2082_333_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v___x_339_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_342_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc_n(v_a_341_, 2);
lean_dec_ref_known(v___x_340_, 1);
lean_inc(v_a_331_);
lean_inc_ref(v_a_330_);
lean_inc(v_a_329_);
lean_inc_ref(v_a_328_);
lean_inc(v_a_327_);
lean_inc_ref(v_a_326_);
lean_inc(v_a_325_);
lean_inc_ref(v_a_324_);
lean_inc(v_a_323_);
lean_inc(v_a_322_);
lean_inc(v_a_338_);
v___x_342_ = lean_apply_13(v_eval_321_, v_a_338_, v_a_341_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, lean_box(0));
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_413_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_413_ == 0)
{
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_413_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_413_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
if (lean_obj_tag(v_a_343_) == 1)
{
lean_object* v_val_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
lean_del_object(v___x_345_);
v_val_347_ = lean_ctor_get(v_a_343_, 0);
lean_inc_n(v_val_347_, 2);
lean_dec_ref_known(v_a_343_, 1);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_box(0);
lean_inc(v_a_331_);
lean_inc_ref(v_a_330_);
lean_inc(v_a_329_);
lean_inc_ref(v_a_328_);
lean_inc(v_a_327_);
lean_inc_ref(v_a_326_);
lean_inc(v_a_325_);
lean_inc_ref(v_a_324_);
lean_inc(v_a_323_);
lean_inc(v_a_322_);
v___x_350_ = lean_grind_internalize(v_val_347_, v___x_348_, v___x_349_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v___x_351_; 
lean_dec_ref_known(v___x_350_, 1);
lean_inc(v_a_331_);
lean_inc_ref(v_a_330_);
lean_inc(v_a_329_);
lean_inc_ref(v_a_328_);
lean_inc_ref(v_e_320_);
v___x_351_ = lean_infer_type(v_e_320_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_353_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_351_, 1);
lean_inc(v_a_331_);
lean_inc_ref(v_a_330_);
lean_inc(v_a_329_);
lean_inc_ref(v_a_328_);
lean_inc_ref(v_a_u2081_335_);
v___x_353_ = lean_infer_type(v_a_u2081_335_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v___x_355_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref_known(v___x_353_, 1);
lean_inc(v_a_331_);
lean_inc_ref(v_a_330_);
lean_inc(v_a_329_);
lean_inc_ref(v_a_328_);
lean_inc_ref(v_a_u2082_333_);
v___x_355_ = lean_infer_type(v_a_u2082_333_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_355_, 1);
v___x_357_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__3, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__3);
v___x_358_ = l_Lean_Expr_appFn_x21(v___x_334_);
lean_dec_ref(v___x_334_);
lean_inc(v_val_347_);
lean_inc(v_a_341_);
lean_inc_ref(v_a_u2082_333_);
lean_inc(v_a_338_);
lean_inc_ref(v_a_u2081_335_);
lean_inc(v_a_352_);
v___x_359_ = l_Lean_mkApp9(v___x_357_, v_a_354_, v_a_356_, v_a_352_, v___x_358_, v_a_u2081_335_, v_a_338_, v_a_u2082_333_, v_a_341_, v_val_347_);
lean_inc(v_a_331_);
lean_inc_ref(v_a_330_);
lean_inc(v_a_329_);
lean_inc_ref(v_a_328_);
lean_inc(v_a_327_);
lean_inc_ref(v_a_326_);
lean_inc(v_a_325_);
lean_inc_ref(v_a_324_);
lean_inc(v_a_323_);
lean_inc(v_a_322_);
v___x_360_ = lean_grind_mk_eq_proof(v_a_u2081_335_, v_a_338_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_362_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_a_361_);
lean_dec_ref_known(v___x_360_, 1);
lean_inc(v_a_331_);
lean_inc_ref(v_a_330_);
lean_inc(v_a_329_);
lean_inc_ref(v_a_328_);
lean_inc(v_a_327_);
lean_inc_ref(v_a_326_);
lean_inc(v_a_325_);
lean_inc_ref(v_a_324_);
lean_inc(v_a_323_);
lean_inc(v_a_322_);
v___x_362_ = lean_grind_mk_eq_proof(v_a_u2082_333_, v_a_341_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; lean_object* v___x_368_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_362_, 1);
v___x_364_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11);
lean_inc(v_val_347_);
v___x_365_ = l_Lean_mkAppB(v___x_364_, v_a_352_, v_val_347_);
v___x_366_ = l_Lean_mkApp3(v___x_359_, v_a_361_, v_a_363_, v___x_365_);
v___x_367_ = 0;
v___x_368_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_320_, v_val_347_, v___x_366_, v___x_367_, v_a_322_, v_a_324_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
return v___x_368_;
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec(v_a_361_);
lean_dec_ref(v___x_359_);
lean_dec(v_a_352_);
lean_dec(v_val_347_);
lean_dec_ref(v_e_320_);
v_a_369_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_362_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_362_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec_ref(v___x_359_);
lean_dec(v_a_352_);
lean_dec(v_val_347_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_u2082_333_);
lean_dec_ref(v_e_320_);
v_a_377_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_360_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_360_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec(v_a_354_);
lean_dec(v_a_352_);
lean_dec(v_val_347_);
lean_dec(v_a_341_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_u2081_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v_a_u2082_333_);
lean_dec_ref(v_e_320_);
v_a_385_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_355_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_355_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec(v_a_352_);
lean_dec(v_val_347_);
lean_dec(v_a_341_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_u2081_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v_a_u2082_333_);
lean_dec_ref(v_e_320_);
v_a_393_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_353_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_353_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec(v_val_347_);
lean_dec(v_a_341_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_u2081_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v_a_u2082_333_);
lean_dec_ref(v_e_320_);
v_a_401_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_351_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_351_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
else
{
lean_dec(v_val_347_);
lean_dec(v_a_341_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_u2081_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v_a_u2082_333_);
lean_dec_ref(v_e_320_);
return v___x_350_;
}
}
else
{
lean_object* v___x_409_; lean_object* v___x_411_; 
lean_dec(v_a_343_);
lean_dec(v_a_341_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_u2081_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v_a_u2082_333_);
lean_dec_ref(v_e_320_);
v___x_409_ = lean_box(0);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_409_);
v___x_411_ = v___x_345_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_a_341_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_u2081_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v_a_u2082_333_);
lean_dec_ref(v_e_320_);
v_a_414_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_342_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_342_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec(v_a_338_);
lean_dec_ref(v_a_u2081_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v_a_u2082_333_);
lean_dec_ref(v_eval_321_);
lean_dec_ref(v_e_320_);
v_a_422_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_340_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_340_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref(v_a_u2081_335_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v_a_u2082_333_);
lean_dec_ref(v_eval_321_);
lean_dec_ref(v_e_320_);
v_a_430_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_337_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_337_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_320_ = stack[0].m_obj;
lean_object* v_eval_321_ = stack[1].m_obj;
lean_object* v_a_322_ = stack[2].m_obj;
lean_object* v_a_323_ = stack[3].m_obj;
lean_object* v_a_324_ = stack[4].m_obj;
lean_object* v_a_325_ = stack[5].m_obj;
lean_object* v_a_326_ = stack[6].m_obj;
lean_object* v_a_327_ = stack[7].m_obj;
lean_object* v_a_328_ = stack[8].m_obj;
lean_object* v_a_329_ = stack[9].m_obj;
lean_object* v_a_330_ = stack[10].m_obj;
lean_object* v_a_331_ = stack[11].m_obj;
lean_object* v_res_438_;
v_res_438_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_320_, v_eval_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
stack->m_obj
 = v_res_438_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___boxed(lean_object* v_e_439_, lean_object* v_eval_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_439_, v_eval_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec(v_a_441_);
return v_res_452_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV___lam__0(lean_object* v_op_453_, lean_object* v_r_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Meta_getBitVecValue_x3f(v_r_454_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_503_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_503_ == 0)
{
v___x_469_ = v___x_466_;
v_isShared_470_ = v_isSharedCheck_503_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_466_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_503_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
if (lean_obj_tag(v_a_467_) == 1)
{
lean_object* v_val_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_498_; 
lean_del_object(v___x_469_);
v_val_471_ = lean_ctor_get(v_a_467_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v_a_467_);
if (v_isSharedCheck_498_ == 0)
{
v___x_473_ = v_a_467_;
v_isShared_474_ = v_isSharedCheck_498_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_val_471_);
lean_dec(v_a_467_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_498_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v_fst_475_; lean_object* v_snd_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_fst_475_ = lean_ctor_get(v_val_471_, 0);
lean_inc_n(v_fst_475_, 2);
v_snd_476_ = lean_ctor_get(v_val_471_, 1);
lean_inc(v_snd_476_);
lean_dec(v_val_471_);
v___x_477_ = lean_apply_2(v_op_453_, v_fst_475_, v_snd_476_);
v___x_478_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_475_, v___x_477_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_489_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_489_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_489_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_489_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v_a_479_);
v___x_484_ = v___x_473_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_488_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_486_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_484_);
v___x_486_ = v___x_481_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_del_object(v___x_473_);
v_a_490_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_478_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_478_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
else
{
lean_object* v___x_499_; lean_object* v___x_501_; 
lean_dec(v_a_467_);
lean_dec_ref(v_op_453_);
v___x_499_ = lean_box(0);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_499_);
v___x_501_ = v___x_469_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_dec_ref(v_op_453_);
v_a_504_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_466_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_466_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_453_ = stack[0].m_obj;
lean_object* v_r_454_ = stack[1].m_obj;
lean_object* v___y_455_ = stack[2].m_obj;
lean_object* v___y_456_ = stack[3].m_obj;
lean_object* v___y_457_ = stack[4].m_obj;
lean_object* v___y_458_ = stack[5].m_obj;
lean_object* v___y_459_ = stack[6].m_obj;
lean_object* v___y_460_ = stack[7].m_obj;
lean_object* v___y_461_ = stack[8].m_obj;
lean_object* v___y_462_ = stack[9].m_obj;
lean_object* v___y_463_ = stack[10].m_obj;
lean_object* v___y_464_ = stack[11].m_obj;
lean_object* v_res_512_;
v_res_512_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV___lam__0(v_op_453_, v_r_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
stack->m_obj
 = v_res_512_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV___lam__0___boxed(lean_object* v_op_513_, lean_object* v_r_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV___lam__0(v_op_513_, v_r_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec(v___y_515_);
return v_res_526_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV(lean_object* v_declName_527_, lean_object* v_arity_528_, lean_object* v_op_529_, lean_object* v_e_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
uint8_t v___x_542_; 
v___x_542_ = l_Lean_Expr_isAppOfArity(v_e_530_, v_declName_527_, v_arity_528_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec_ref(v_e_530_);
lean_dec_ref(v_op_529_);
v___x_543_ = lean_box(0);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
else
{
lean_object* v___f_545_; lean_object* v___x_546_; 
v___f_545_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV___lam__0___boxed), 13, 1);
lean_closure_set(v___f_545_, 0, v_op_529_);
v___x_546_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_530_, v___f_545_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
return v___x_546_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_527_ = stack[0].m_obj;
lean_object* v_arity_528_ = stack[1].m_obj;
lean_object* v_op_529_ = stack[2].m_obj;
lean_object* v_e_530_ = stack[3].m_obj;
lean_object* v_a_531_ = stack[4].m_obj;
lean_object* v_a_532_ = stack[5].m_obj;
lean_object* v_a_533_ = stack[6].m_obj;
lean_object* v_a_534_ = stack[7].m_obj;
lean_object* v_a_535_ = stack[8].m_obj;
lean_object* v_a_536_ = stack[9].m_obj;
lean_object* v_a_537_ = stack[10].m_obj;
lean_object* v_a_538_ = stack[11].m_obj;
lean_object* v_a_539_ = stack[12].m_obj;
lean_object* v_a_540_ = stack[13].m_obj;
lean_object* v_res_547_;
v_res_547_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV(v_declName_527_, v_arity_528_, v_op_529_, v_e_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
stack->m_obj
 = v_res_547_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV___boxed(lean_object* v_declName_548_, lean_object* v_arity_549_, lean_object* v_op_550_, lean_object* v_e_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV(v_declName_548_, v_arity_549_, v_op_550_, v_e_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec(v_a_552_);
lean_dec(v_declName_548_);
return v_res_563_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV___lam__0(lean_object* v_op_564_, lean_object* v_val_565_, lean_object* v_r_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Meta_getBitVecValue_x3f(v_r_566_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_615_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_615_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_615_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_615_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
if (lean_obj_tag(v_a_579_) == 1)
{
lean_object* v_val_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_610_; 
lean_del_object(v___x_581_);
v_val_583_ = lean_ctor_get(v_a_579_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v_a_579_);
if (v_isSharedCheck_610_ == 0)
{
v___x_585_ = v_a_579_;
v_isShared_586_ = v_isSharedCheck_610_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_val_583_);
lean_dec(v_a_579_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_610_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v_fst_587_; lean_object* v_snd_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_fst_587_ = lean_ctor_get(v_val_583_, 0);
lean_inc(v_fst_587_);
v_snd_588_ = lean_ctor_get(v_val_583_, 1);
lean_inc(v_snd_588_);
lean_dec(v_val_583_);
lean_inc(v_val_565_);
v___x_589_ = lean_apply_3(v_op_564_, v_fst_587_, v_val_565_, v_snd_588_);
v___x_590_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_val_565_, v___x_589_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_601_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_601_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_601_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_601_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v_a_591_);
v___x_596_ = v___x_585_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_600_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_598_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_596_);
v___x_598_ = v___x_593_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_del_object(v___x_585_);
v_a_602_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_590_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_590_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_613_; 
lean_dec(v_a_579_);
lean_dec(v_val_565_);
lean_dec_ref(v_op_564_);
v___x_611_ = lean_box(0);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_611_);
v___x_613_ = v___x_581_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec(v_val_565_);
lean_dec_ref(v_op_564_);
v_a_616_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_578_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_578_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_564_ = stack[0].m_obj;
lean_object* v_val_565_ = stack[1].m_obj;
lean_object* v_r_566_ = stack[2].m_obj;
lean_object* v___y_567_ = stack[3].m_obj;
lean_object* v___y_568_ = stack[4].m_obj;
lean_object* v___y_569_ = stack[5].m_obj;
lean_object* v___y_570_ = stack[6].m_obj;
lean_object* v___y_571_ = stack[7].m_obj;
lean_object* v___y_572_ = stack[8].m_obj;
lean_object* v___y_573_ = stack[9].m_obj;
lean_object* v___y_574_ = stack[10].m_obj;
lean_object* v___y_575_ = stack[11].m_obj;
lean_object* v___y_576_ = stack[12].m_obj;
lean_object* v_res_624_;
v_res_624_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV___lam__0(v_op_564_, v_val_565_, v_r_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
stack->m_obj
 = v_res_624_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV___lam__0___boxed(lean_object* v_op_625_, lean_object* v_val_626_, lean_object* v_r_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV___lam__0(v_op_625_, v_val_626_, v_r_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec(v___y_628_);
return v_res_639_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV(lean_object* v_declName_640_, lean_object* v_op_641_, lean_object* v_e_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_654_ = lean_unsigned_to_nat(3u);
v___x_655_ = l_Lean_Expr_isAppOfArity(v_e_642_, v_declName_640_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec_ref(v_e_642_);
lean_dec_ref(v_op_641_);
v___x_656_ = lean_box(0);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_658_ = lean_unsigned_to_nat(1u);
v___x_659_ = l_Lean_Expr_getAppNumArgs(v_e_642_);
v___x_660_ = lean_nat_sub(v___x_659_, v___x_658_);
lean_dec(v___x_659_);
v___x_661_ = lean_nat_sub(v___x_660_, v___x_658_);
lean_dec(v___x_660_);
v___x_662_ = l_Lean_Expr_getRevArg_x21(v_e_642_, v___x_661_);
v___x_663_ = l_Lean_Meta_getNatValue_x3f(v___x_662_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
lean_dec_ref(v___x_662_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_675_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_675_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_675_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_675_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
if (lean_obj_tag(v_a_664_) == 1)
{
lean_object* v_val_668_; lean_object* v___f_669_; lean_object* v___x_670_; 
lean_del_object(v___x_666_);
v_val_668_ = lean_ctor_get(v_a_664_, 0);
lean_inc(v_val_668_);
lean_dec_ref_known(v_a_664_, 1);
v___f_669_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV___lam__0___boxed), 14, 2);
lean_closure_set(v___f_669_, 0, v_op_641_);
lean_closure_set(v___f_669_, 1, v_val_668_);
v___x_670_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_642_, v___f_669_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
return v___x_670_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_673_; 
lean_dec(v_a_664_);
lean_dec_ref(v_e_642_);
lean_dec_ref(v_op_641_);
v___x_671_ = lean_box(0);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_671_);
v___x_673_ = v___x_666_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v_e_642_);
lean_dec_ref(v_op_641_);
v_a_676_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_663_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_663_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_640_ = stack[0].m_obj;
lean_object* v_op_641_ = stack[1].m_obj;
lean_object* v_e_642_ = stack[2].m_obj;
lean_object* v_a_643_ = stack[3].m_obj;
lean_object* v_a_644_ = stack[4].m_obj;
lean_object* v_a_645_ = stack[5].m_obj;
lean_object* v_a_646_ = stack[6].m_obj;
lean_object* v_a_647_ = stack[7].m_obj;
lean_object* v_a_648_ = stack[8].m_obj;
lean_object* v_a_649_ = stack[9].m_obj;
lean_object* v_a_650_ = stack[10].m_obj;
lean_object* v_a_651_ = stack[11].m_obj;
lean_object* v_a_652_ = stack[12].m_obj;
lean_object* v_res_684_;
v_res_684_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV(v_declName_640_, v_op_641_, v_e_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_);
stack->m_obj
 = v_res_684_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV___boxed(lean_object* v_declName_685_, lean_object* v_op_686_, lean_object* v_e_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV(v_declName_685_, v_op_686_, v_e_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
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
lean_dec(v_declName_685_);
return v_res_699_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0(lean_object* v_op_700_, lean_object* v_val_701_, lean_object* v_val_702_, lean_object* v_r_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Meta_getBitVecValue_x3f(v_r_703_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_754_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_754_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_754_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_754_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
if (lean_obj_tag(v_a_716_) == 1)
{
lean_object* v_val_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_749_; 
lean_del_object(v___x_718_);
v_val_720_ = lean_ctor_get(v_a_716_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v_a_716_);
if (v_isSharedCheck_749_ == 0)
{
v___x_722_ = v_a_716_;
v_isShared_723_ = v_isSharedCheck_749_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_val_720_);
lean_dec(v_a_716_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_749_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_fst_724_; lean_object* v_snd_725_; lean_object* v___x_726_; lean_object* v_fst_727_; lean_object* v_snd_728_; lean_object* v___x_729_; 
v_fst_724_ = lean_ctor_get(v_val_720_, 0);
lean_inc(v_fst_724_);
v_snd_725_ = lean_ctor_get(v_val_720_, 1);
lean_inc(v_snd_725_);
lean_dec(v_val_720_);
v___x_726_ = lean_apply_4(v_op_700_, v_fst_724_, v_val_701_, v_val_702_, v_snd_725_);
v_fst_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_fst_727_);
v_snd_728_ = lean_ctor_get(v___x_726_, 1);
lean_inc(v_snd_728_);
lean_dec_ref(v___x_726_);
v___x_729_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_727_, v_snd_728_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_740_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_740_ == 0)
{
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_740_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_740_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v_a_730_);
v___x_735_ = v___x_722_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_739_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_737_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 0, v___x_735_);
v___x_737_ = v___x_732_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_del_object(v___x_722_);
v_a_741_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_729_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_729_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
else
{
lean_object* v___x_750_; lean_object* v___x_752_; 
lean_dec(v_a_716_);
lean_dec(v_val_702_);
lean_dec(v_val_701_);
lean_dec_ref(v_op_700_);
v___x_750_ = lean_box(0);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_750_);
v___x_752_ = v___x_718_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_val_702_);
lean_dec(v_val_701_);
lean_dec_ref(v_op_700_);
v_a_755_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_715_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_715_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_700_ = stack[0].m_obj;
lean_object* v_val_701_ = stack[1].m_obj;
lean_object* v_val_702_ = stack[2].m_obj;
lean_object* v_r_703_ = stack[3].m_obj;
lean_object* v___y_704_ = stack[4].m_obj;
lean_object* v___y_705_ = stack[5].m_obj;
lean_object* v___y_706_ = stack[6].m_obj;
lean_object* v___y_707_ = stack[7].m_obj;
lean_object* v___y_708_ = stack[8].m_obj;
lean_object* v___y_709_ = stack[9].m_obj;
lean_object* v___y_710_ = stack[10].m_obj;
lean_object* v___y_711_ = stack[11].m_obj;
lean_object* v___y_712_ = stack[12].m_obj;
lean_object* v___y_713_ = stack[13].m_obj;
lean_object* v_res_763_;
v_res_763_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0(v_op_700_, v_val_701_, v_val_702_, v_r_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
stack->m_obj
 = v_res_763_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0___boxed(lean_object* v_op_764_, lean_object* v_val_765_, lean_object* v_val_766_, lean_object* v_r_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0(v_op_764_, v_val_765_, v_val_766_, v_r_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec(v___y_768_);
return v_res_779_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV(lean_object* v_declName_780_, lean_object* v_op_781_, lean_object* v_e_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = lean_unsigned_to_nat(4u);
v___x_795_ = l_Lean_Expr_isAppOfArity(v_e_782_, v_declName_780_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec_ref(v_e_782_);
lean_dec_ref(v_op_781_);
v___x_796_ = lean_box(0);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_798_ = lean_unsigned_to_nat(1u);
v___x_799_ = l_Lean_Expr_getAppNumArgs(v_e_782_);
v___x_800_ = lean_nat_sub(v___x_799_, v___x_798_);
v___x_801_ = lean_nat_sub(v___x_800_, v___x_798_);
lean_dec(v___x_800_);
v___x_802_ = l_Lean_Expr_getRevArg_x21(v_e_782_, v___x_801_);
v___x_803_ = l_Lean_Meta_getNatValue_x3f(v___x_802_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
lean_dec_ref(v___x_802_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_838_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_838_ == 0)
{
v___x_806_ = v___x_803_;
v_isShared_807_ = v_isSharedCheck_838_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_803_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_838_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
if (lean_obj_tag(v_a_804_) == 1)
{
lean_object* v_val_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
lean_del_object(v___x_806_);
v_val_808_ = lean_ctor_get(v_a_804_, 0);
lean_inc(v_val_808_);
lean_dec_ref_known(v_a_804_, 1);
v___x_809_ = lean_unsigned_to_nat(2u);
v___x_810_ = lean_nat_sub(v___x_799_, v___x_809_);
lean_dec(v___x_799_);
v___x_811_ = lean_nat_sub(v___x_810_, v___x_798_);
lean_dec(v___x_810_);
v___x_812_ = l_Lean_Expr_getRevArg_x21(v_e_782_, v___x_811_);
v___x_813_ = l_Lean_Meta_getNatValue_x3f(v___x_812_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
lean_dec_ref(v___x_812_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_825_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_825_ == 0)
{
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_825_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_825_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
if (lean_obj_tag(v_a_814_) == 1)
{
lean_object* v_val_818_; lean_object* v___f_819_; lean_object* v___x_820_; 
lean_del_object(v___x_816_);
v_val_818_ = lean_ctor_get(v_a_814_, 0);
lean_inc(v_val_818_);
lean_dec_ref_known(v_a_814_, 1);
v___f_819_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0___boxed), 15, 3);
lean_closure_set(v___f_819_, 0, v_op_781_);
lean_closure_set(v___f_819_, 1, v_val_808_);
lean_closure_set(v___f_819_, 2, v_val_818_);
v___x_820_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_782_, v___f_819_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
return v___x_820_;
}
else
{
lean_object* v___x_821_; lean_object* v___x_823_; 
lean_dec(v_a_814_);
lean_dec(v_val_808_);
lean_dec_ref(v_e_782_);
lean_dec_ref(v_op_781_);
v___x_821_ = lean_box(0);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_821_);
v___x_823_ = v___x_816_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_val_808_);
lean_dec_ref(v_e_782_);
lean_dec_ref(v_op_781_);
v_a_826_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_813_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_813_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
else
{
lean_object* v___x_834_; lean_object* v___x_836_; 
lean_dec(v_a_804_);
lean_dec(v___x_799_);
lean_dec_ref(v_e_782_);
lean_dec_ref(v_op_781_);
v___x_834_ = lean_box(0);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_834_);
v___x_836_ = v___x_806_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec(v___x_799_);
lean_dec_ref(v_e_782_);
lean_dec_ref(v_op_781_);
v_a_839_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_803_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_803_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_780_ = stack[0].m_obj;
lean_object* v_op_781_ = stack[1].m_obj;
lean_object* v_e_782_ = stack[2].m_obj;
lean_object* v_a_783_ = stack[3].m_obj;
lean_object* v_a_784_ = stack[4].m_obj;
lean_object* v_a_785_ = stack[5].m_obj;
lean_object* v_a_786_ = stack[6].m_obj;
lean_object* v_a_787_ = stack[7].m_obj;
lean_object* v_a_788_ = stack[8].m_obj;
lean_object* v_a_789_ = stack[9].m_obj;
lean_object* v_a_790_ = stack[10].m_obj;
lean_object* v_a_791_ = stack[11].m_obj;
lean_object* v_a_792_ = stack[12].m_obj;
lean_object* v_res_847_;
v_res_847_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV(v_declName_780_, v_op_781_, v_e_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
stack->m_obj
 = v_res_847_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___boxed(lean_object* v_declName_848_, lean_object* v_op_849_, lean_object* v_e_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV(v_declName_848_, v_op_849_, v_e_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
lean_dec(v_a_860_);
lean_dec_ref(v_a_859_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec(v_a_851_);
lean_dec(v_declName_848_);
return v_res_862_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0(lean_object* v_op_863_, lean_object* v_r_u2081_864_, lean_object* v_r_u2082_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_864_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_940_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_940_ == 0)
{
v___x_880_ = v___x_877_;
v_isShared_881_ = v_isSharedCheck_940_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_940_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
if (lean_obj_tag(v_a_878_) == 1)
{
lean_object* v_val_882_; lean_object* v_fst_883_; lean_object* v_snd_884_; lean_object* v___x_885_; 
lean_del_object(v___x_880_);
v_val_882_ = lean_ctor_get(v_a_878_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v_a_878_, 1);
v_fst_883_ = lean_ctor_get(v_val_882_, 0);
lean_inc(v_fst_883_);
v_snd_884_ = lean_ctor_get(v_val_882_, 1);
lean_inc(v_snd_884_);
lean_dec(v_val_882_);
v___x_885_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_865_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_927_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_927_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_927_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_927_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
if (lean_obj_tag(v_a_886_) == 1)
{
lean_object* v_val_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_922_; 
v_val_890_ = lean_ctor_get(v_a_886_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v_a_886_);
if (v_isSharedCheck_922_ == 0)
{
v___x_892_ = v_a_886_;
v_isShared_893_ = v_isSharedCheck_922_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_val_890_);
lean_dec(v_a_886_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_922_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v_fst_894_; lean_object* v_snd_895_; uint8_t v___x_896_; 
v_fst_894_ = lean_ctor_get(v_val_890_, 0);
lean_inc(v_fst_894_);
v_snd_895_ = lean_ctor_get(v_val_890_, 1);
lean_inc(v_snd_895_);
lean_dec(v_val_890_);
v___x_896_ = lean_nat_dec_eq(v_fst_883_, v_fst_894_);
lean_dec(v_fst_894_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_899_; 
lean_dec(v_snd_895_);
lean_del_object(v___x_892_);
lean_dec(v_snd_884_);
lean_dec(v_fst_883_);
lean_dec_ref(v_op_863_);
v___x_897_ = lean_box(0);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_897_);
v___x_899_ = v___x_888_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
else
{
lean_object* v___x_901_; lean_object* v___x_902_; 
lean_del_object(v___x_888_);
lean_inc(v_fst_883_);
v___x_901_ = lean_apply_3(v_op_863_, v_fst_883_, v_snd_884_, v_snd_895_);
v___x_902_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_883_, v___x_901_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_913_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_913_ == 0)
{
v___x_905_ = v___x_902_;
v_isShared_906_ = v_isSharedCheck_913_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_913_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v_a_903_);
v___x_908_ = v___x_892_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_910_; 
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_908_);
v___x_910_ = v___x_905_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_del_object(v___x_892_);
v_a_914_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_902_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_902_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
}
else
{
lean_object* v___x_923_; lean_object* v___x_925_; 
lean_dec(v_a_886_);
lean_dec(v_snd_884_);
lean_dec(v_fst_883_);
lean_dec_ref(v_op_863_);
v___x_923_ = lean_box(0);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_923_);
v___x_925_ = v___x_888_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec(v_snd_884_);
lean_dec(v_fst_883_);
lean_dec_ref(v_op_863_);
v_a_928_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_885_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_885_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_object* v___x_936_; lean_object* v___x_938_; 
lean_dec(v_a_878_);
lean_dec_ref(v_r_u2082_865_);
lean_dec_ref(v_op_863_);
v___x_936_ = lean_box(0);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_936_);
v___x_938_ = v___x_880_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref(v_r_u2082_865_);
lean_dec_ref(v_op_863_);
v_a_941_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_877_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_877_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_863_ = stack[0].m_obj;
lean_object* v_r_u2081_864_ = stack[1].m_obj;
lean_object* v_r_u2082_865_ = stack[2].m_obj;
lean_object* v___y_866_ = stack[3].m_obj;
lean_object* v___y_867_ = stack[4].m_obj;
lean_object* v___y_868_ = stack[5].m_obj;
lean_object* v___y_869_ = stack[6].m_obj;
lean_object* v___y_870_ = stack[7].m_obj;
lean_object* v___y_871_ = stack[8].m_obj;
lean_object* v___y_872_ = stack[9].m_obj;
lean_object* v___y_873_ = stack[10].m_obj;
lean_object* v___y_874_ = stack[11].m_obj;
lean_object* v___y_875_ = stack[12].m_obj;
lean_object* v_res_949_;
v_res_949_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0(v_op_863_, v_r_u2081_864_, v_r_u2082_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
stack->m_obj
 = v_res_949_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0___boxed(lean_object* v_op_950_, lean_object* v_r_u2081_951_, lean_object* v_r_u2082_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0(v_op_950_, v_r_u2081_951_, v_r_u2082_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec(v___y_953_);
return v_res_964_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV(lean_object* v_declName_965_, lean_object* v_arity_966_, lean_object* v_op_967_, lean_object* v_e_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
uint8_t v___x_980_; 
v___x_980_ = l_Lean_Expr_isAppOfArity(v_e_968_, v_declName_965_, v_arity_966_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_982_; 
lean_dec_ref(v_e_968_);
lean_dec_ref(v_op_967_);
v___x_981_ = lean_box(0);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
return v___x_982_;
}
else
{
lean_object* v___f_983_; lean_object* v___x_984_; 
v___f_983_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0___boxed), 14, 1);
lean_closure_set(v___f_983_, 0, v_op_967_);
v___x_984_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_968_, v___f_983_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
return v___x_984_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_965_ = stack[0].m_obj;
lean_object* v_arity_966_ = stack[1].m_obj;
lean_object* v_op_967_ = stack[2].m_obj;
lean_object* v_e_968_ = stack[3].m_obj;
lean_object* v_a_969_ = stack[4].m_obj;
lean_object* v_a_970_ = stack[5].m_obj;
lean_object* v_a_971_ = stack[6].m_obj;
lean_object* v_a_972_ = stack[7].m_obj;
lean_object* v_a_973_ = stack[8].m_obj;
lean_object* v_a_974_ = stack[9].m_obj;
lean_object* v_a_975_ = stack[10].m_obj;
lean_object* v_a_976_ = stack[11].m_obj;
lean_object* v_a_977_ = stack[12].m_obj;
lean_object* v_a_978_ = stack[13].m_obj;
lean_object* v_res_985_;
v_res_985_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV(v_declName_965_, v_arity_966_, v_op_967_, v_e_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
stack->m_obj
 = v_res_985_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___boxed(lean_object* v_declName_986_, lean_object* v_arity_987_, lean_object* v_op_988_, lean_object* v_e_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV(v_declName_986_, v_arity_987_, v_op_988_, v_e_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
lean_dec(v_a_990_);
lean_dec(v_declName_986_);
return v_res_1001_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0(lean_object* v_op_1002_, lean_object* v_r_u2081_1003_, lean_object* v_r_u2082_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_1003_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1072_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1019_ = v___x_1016_;
v_isShared_1020_ = v_isSharedCheck_1072_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1072_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
if (lean_obj_tag(v_a_1017_) == 1)
{
lean_object* v_val_1021_; lean_object* v_fst_1022_; lean_object* v_snd_1023_; lean_object* v___x_1024_; 
lean_del_object(v___x_1019_);
v_val_1021_ = lean_ctor_get(v_a_1017_, 0);
lean_inc(v_val_1021_);
lean_dec_ref_known(v_a_1017_, 1);
v_fst_1022_ = lean_ctor_get(v_val_1021_, 0);
lean_inc(v_fst_1022_);
v_snd_1023_ = lean_ctor_get(v_val_1021_, 1);
lean_inc(v_snd_1023_);
lean_dec(v_val_1021_);
v___x_1024_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_1004_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1059_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1059_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1059_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
if (lean_obj_tag(v_a_1025_) == 1)
{
lean_object* v_val_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1054_; 
lean_del_object(v___x_1027_);
v_val_1029_ = lean_ctor_get(v_a_1025_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_a_1025_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1031_ = v_a_1025_;
v_isShared_1032_ = v_isSharedCheck_1054_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_val_1029_);
lean_dec(v_a_1025_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1054_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_inc(v_fst_1022_);
v___x_1033_ = lean_apply_3(v_op_1002_, v_fst_1022_, v_snd_1023_, v_val_1029_);
v___x_1034_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_1022_, v___x_1033_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1045_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1045_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1045_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v_a_1035_);
v___x_1040_ = v___x_1031_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1042_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1040_);
v___x_1042_ = v___x_1037_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_del_object(v___x_1031_);
v_a_1046_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1034_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1034_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
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
else
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
lean_dec(v_a_1025_);
lean_dec(v_snd_1023_);
lean_dec(v_fst_1022_);
lean_dec_ref(v_op_1002_);
v___x_1055_ = lean_box(0);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1055_);
v___x_1057_ = v___x_1027_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
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
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec(v_snd_1023_);
lean_dec(v_fst_1022_);
lean_dec_ref(v_op_1002_);
v_a_1060_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1024_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1024_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
else
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
lean_dec(v_a_1017_);
lean_dec_ref(v_op_1002_);
v___x_1068_ = lean_box(0);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1068_);
v___x_1070_ = v___x_1019_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref(v_op_1002_);
v_a_1073_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1016_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1016_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_1002_ = stack[0].m_obj;
lean_object* v_r_u2081_1003_ = stack[1].m_obj;
lean_object* v_r_u2082_1004_ = stack[2].m_obj;
lean_object* v___y_1005_ = stack[3].m_obj;
lean_object* v___y_1006_ = stack[4].m_obj;
lean_object* v___y_1007_ = stack[5].m_obj;
lean_object* v___y_1008_ = stack[6].m_obj;
lean_object* v___y_1009_ = stack[7].m_obj;
lean_object* v___y_1010_ = stack[8].m_obj;
lean_object* v___y_1011_ = stack[9].m_obj;
lean_object* v___y_1012_ = stack[10].m_obj;
lean_object* v___y_1013_ = stack[11].m_obj;
lean_object* v___y_1014_ = stack[12].m_obj;
lean_object* v_res_1081_;
v_res_1081_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0(v_op_1002_, v_r_u2081_1003_, v_r_u2082_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
stack->m_obj
 = v_res_1081_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0___boxed(lean_object* v_op_1082_, lean_object* v_r_u2081_1083_, lean_object* v_r_u2082_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0(v_op_1082_, v_r_u2081_1083_, v_r_u2082_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v_r_u2082_1084_);
return v_res_1096_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV(lean_object* v_declName_1097_, lean_object* v_arity_1098_, lean_object* v_op_1099_, lean_object* v_e_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
uint8_t v___x_1112_; 
v___x_1112_ = l_Lean_Expr_isAppOfArity(v_e_1100_, v_declName_1097_, v_arity_1098_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec_ref(v_e_1100_);
lean_dec_ref(v_op_1099_);
v___x_1113_ = lean_box(0);
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
return v___x_1114_;
}
else
{
lean_object* v___f_1115_; lean_object* v___x_1116_; 
v___f_1115_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0___boxed), 14, 1);
lean_closure_set(v___f_1115_, 0, v_op_1099_);
v___x_1116_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_1100_, v___f_1115_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
return v___x_1116_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1097_ = stack[0].m_obj;
lean_object* v_arity_1098_ = stack[1].m_obj;
lean_object* v_op_1099_ = stack[2].m_obj;
lean_object* v_e_1100_ = stack[3].m_obj;
lean_object* v_a_1101_ = stack[4].m_obj;
lean_object* v_a_1102_ = stack[5].m_obj;
lean_object* v_a_1103_ = stack[6].m_obj;
lean_object* v_a_1104_ = stack[7].m_obj;
lean_object* v_a_1105_ = stack[8].m_obj;
lean_object* v_a_1106_ = stack[9].m_obj;
lean_object* v_a_1107_ = stack[10].m_obj;
lean_object* v_a_1108_ = stack[11].m_obj;
lean_object* v_a_1109_ = stack[12].m_obj;
lean_object* v_a_1110_ = stack[13].m_obj;
lean_object* v_res_1117_;
v_res_1117_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV(v_declName_1097_, v_arity_1098_, v_op_1099_, v_e_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
stack->m_obj
 = v_res_1117_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___boxed(lean_object* v_declName_1118_, lean_object* v_arity_1119_, lean_object* v_op_1120_, lean_object* v_e_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV(v_declName_1118_, v_arity_1119_, v_op_1120_, v_e_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec(v_declName_1118_);
return v_res_1133_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___lam__0(lean_object* v_op_1134_, lean_object* v_r_u2081_1135_, lean_object* v_r_u2082_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_1135_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1205_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1205_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1205_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
if (lean_obj_tag(v_a_1149_) == 1)
{
lean_object* v_val_1153_; lean_object* v_fst_1154_; lean_object* v_snd_1155_; lean_object* v___x_1156_; 
lean_del_object(v___x_1151_);
v_val_1153_ = lean_ctor_get(v_a_1149_, 0);
lean_inc(v_val_1153_);
lean_dec_ref_known(v_a_1149_, 1);
v_fst_1154_ = lean_ctor_get(v_val_1153_, 0);
lean_inc(v_fst_1154_);
v_snd_1155_ = lean_ctor_get(v_val_1153_, 1);
lean_inc(v_snd_1155_);
lean_dec(v_val_1153_);
v___x_1156_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_1136_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1192_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1192_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1192_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
if (lean_obj_tag(v_a_1157_) == 1)
{
lean_object* v_val_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1187_; 
lean_del_object(v___x_1159_);
v_val_1161_ = lean_ctor_get(v_a_1157_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_a_1157_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1163_ = v_a_1157_;
v_isShared_1164_ = v_isSharedCheck_1187_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_val_1161_);
lean_dec(v_a_1157_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1187_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = lean_apply_3(v_op_1134_, v_fst_1154_, v_snd_1155_, v_val_1161_);
v___x_1166_ = lean_unbox(v___x_1165_);
v___x_1167_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v___x_1166_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1178_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1178_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1178_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v_a_1168_);
v___x_1173_ = v___x_1163_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1175_; 
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1173_);
v___x_1175_ = v___x_1170_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_del_object(v___x_1163_);
v_a_1179_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1167_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1167_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
else
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
lean_dec(v_a_1157_);
lean_dec(v_snd_1155_);
lean_dec(v_fst_1154_);
lean_dec_ref(v_op_1134_);
v___x_1188_ = lean_box(0);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1188_);
v___x_1190_ = v___x_1159_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v_snd_1155_);
lean_dec(v_fst_1154_);
lean_dec_ref(v_op_1134_);
v_a_1193_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1156_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1156_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
lean_dec(v_a_1149_);
lean_dec_ref(v_op_1134_);
v___x_1201_ = lean_box(0);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1201_);
v___x_1203_ = v___x_1151_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec_ref(v_op_1134_);
v_a_1206_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1148_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1148_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_1134_ = stack[0].m_obj;
lean_object* v_r_u2081_1135_ = stack[1].m_obj;
lean_object* v_r_u2082_1136_ = stack[2].m_obj;
lean_object* v___y_1137_ = stack[3].m_obj;
lean_object* v___y_1138_ = stack[4].m_obj;
lean_object* v___y_1139_ = stack[5].m_obj;
lean_object* v___y_1140_ = stack[6].m_obj;
lean_object* v___y_1141_ = stack[7].m_obj;
lean_object* v___y_1142_ = stack[8].m_obj;
lean_object* v___y_1143_ = stack[9].m_obj;
lean_object* v___y_1144_ = stack[10].m_obj;
lean_object* v___y_1145_ = stack[11].m_obj;
lean_object* v___y_1146_ = stack[12].m_obj;
lean_object* v_res_1214_;
v_res_1214_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___lam__0(v_op_1134_, v_r_u2081_1135_, v_r_u2082_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
stack->m_obj
 = v_res_1214_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___lam__0___boxed(lean_object* v_op_1215_, lean_object* v_r_u2081_1216_, lean_object* v_r_u2082_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___lam__0(v_op_1215_, v_r_u2081_1216_, v_r_u2082_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v_r_u2082_1217_);
return v_res_1229_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV(lean_object* v_declName_1230_, lean_object* v_op_1231_, lean_object* v_e_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1244_ = lean_unsigned_to_nat(3u);
v___x_1245_ = l_Lean_Expr_isAppOfArity(v_e_1232_, v_declName_1230_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_dec_ref(v_e_1232_);
lean_dec_ref(v_op_1231_);
v___x_1246_ = lean_box(0);
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
return v___x_1247_;
}
else
{
lean_object* v___f_1248_; lean_object* v___x_1249_; 
v___f_1248_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___lam__0___boxed), 14, 1);
lean_closure_set(v___f_1248_, 0, v_op_1231_);
v___x_1249_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_1232_, v___f_1248_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
return v___x_1249_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1230_ = stack[0].m_obj;
lean_object* v_op_1231_ = stack[1].m_obj;
lean_object* v_e_1232_ = stack[2].m_obj;
lean_object* v_a_1233_ = stack[3].m_obj;
lean_object* v_a_1234_ = stack[4].m_obj;
lean_object* v_a_1235_ = stack[5].m_obj;
lean_object* v_a_1236_ = stack[6].m_obj;
lean_object* v_a_1237_ = stack[7].m_obj;
lean_object* v_a_1238_ = stack[8].m_obj;
lean_object* v_a_1239_ = stack[9].m_obj;
lean_object* v_a_1240_ = stack[10].m_obj;
lean_object* v_a_1241_ = stack[11].m_obj;
lean_object* v_a_1242_ = stack[12].m_obj;
lean_object* v_res_1250_;
v_res_1250_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV(v_declName_1230_, v_op_1231_, v_e_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
stack->m_obj
 = v_res_1250_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___boxed(lean_object* v_declName_1251_, lean_object* v_op_1252_, lean_object* v_e_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV(v_declName_1251_, v_op_1252_, v_e_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
lean_dec(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec(v_declName_1251_);
return v_res_1265_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVNot___lam__0(lean_object* v_r_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1266_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1315_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1315_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1315_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
if (lean_obj_tag(v_a_1279_) == 1)
{
lean_object* v_val_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1310_; 
lean_del_object(v___x_1281_);
v_val_1283_ = lean_ctor_get(v_a_1279_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_a_1279_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1285_ = v_a_1279_;
v_isShared_1286_ = v_isSharedCheck_1310_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_val_1283_);
lean_dec(v_a_1279_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1310_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_fst_1287_; lean_object* v_snd_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_fst_1287_ = lean_ctor_get(v_val_1283_, 0);
lean_inc(v_fst_1287_);
v_snd_1288_ = lean_ctor_get(v_val_1283_, 1);
lean_inc(v_snd_1288_);
lean_dec(v_val_1283_);
v___x_1289_ = l_BitVec_not(v_fst_1287_, v_snd_1288_);
lean_dec(v_snd_1288_);
v___x_1290_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_1287_, v___x_1289_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1301_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1301_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1301_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v_a_1291_);
v___x_1296_ = v___x_1285_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1298_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1296_);
v___x_1298_ = v___x_1293_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_del_object(v___x_1285_);
v_a_1302_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1290_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1290_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
lean_dec(v_a_1279_);
v___x_1311_ = lean_box(0);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1311_);
v___x_1313_ = v___x_1281_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
v_a_1316_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1278_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1278_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVNot___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1266_ = stack[0].m_obj;
lean_object* v___y_1267_ = stack[1].m_obj;
lean_object* v___y_1268_ = stack[2].m_obj;
lean_object* v___y_1269_ = stack[3].m_obj;
lean_object* v___y_1270_ = stack[4].m_obj;
lean_object* v___y_1271_ = stack[5].m_obj;
lean_object* v___y_1272_ = stack[6].m_obj;
lean_object* v___y_1273_ = stack[7].m_obj;
lean_object* v___y_1274_ = stack[8].m_obj;
lean_object* v___y_1275_ = stack[9].m_obj;
lean_object* v___y_1276_ = stack[10].m_obj;
lean_object* v_res_1324_;
v_res_1324_ = l_Lean_Meta_Grind_propagateBVNot___lam__0(v_r_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
stack->m_obj
 = v_res_1324_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVNot___lam__0___boxed(lean_object* v_r_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_Meta_Grind_propagateBVNot___lam__0(v_r_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec(v___y_1326_);
return v_res_1337_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVNot(lean_object* v_e_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1356_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVNot___closed__2));
v___x_1357_ = lean_unsigned_to_nat(3u);
v___x_1358_ = l_Lean_Expr_isAppOfArity(v_e_1344_, v___x_1356_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec_ref(v_e_1344_);
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
return v___x_1360_;
}
else
{
lean_object* v___f_1361_; lean_object* v___x_1362_; 
v___f_1361_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVNot___closed__3));
v___x_1362_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1344_, v___f_1361_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
return v___x_1362_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVNot_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1344_ = stack[0].m_obj;
lean_object* v_a_1345_ = stack[1].m_obj;
lean_object* v_a_1346_ = stack[2].m_obj;
lean_object* v_a_1347_ = stack[3].m_obj;
lean_object* v_a_1348_ = stack[4].m_obj;
lean_object* v_a_1349_ = stack[5].m_obj;
lean_object* v_a_1350_ = stack[6].m_obj;
lean_object* v_a_1351_ = stack[7].m_obj;
lean_object* v_a_1352_ = stack[8].m_obj;
lean_object* v_a_1353_ = stack[9].m_obj;
lean_object* v_a_1354_ = stack[10].m_obj;
lean_object* v_res_1363_;
v_res_1363_ = l_Lean_Meta_Grind_propagateBVNot(v_e_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
stack->m_obj
 = v_res_1363_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVNot___boxed(lean_object* v_e_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_Meta_Grind_propagateBVNot(v_e_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec(v_a_1365_);
return v_res_1376_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVNot___regBuiltin_Lean_Meta_Grind_propagateBVNot_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_524020944____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1378_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVNot___closed__2));
v___x_1379_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVNot___boxed), 12, 0);
v___x_1380_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1378_, v___x_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVNot___regBuiltin_Lean_Meta_Grind_propagateBVNot_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_524020944____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1381_;
v_res_1381_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVNot___regBuiltin_Lean_Meta_Grind_propagateBVNot_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_524020944____hygCtx___hyg_9_();
stack->m_obj
 = v_res_1381_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVNot___regBuiltin_Lean_Meta_Grind_propagateBVNot_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_524020944____hygCtx___hyg_9____boxed(lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVNot___regBuiltin_Lean_Meta_Grind_propagateBVNot_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_524020944____hygCtx___hyg_9_();
return v_res_1383_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVClz___lam__0(lean_object* v_r_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1384_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1433_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1433_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1433_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
if (lean_obj_tag(v_a_1397_) == 1)
{
lean_object* v_val_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1428_; 
lean_del_object(v___x_1399_);
v_val_1401_ = lean_ctor_get(v_a_1397_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_a_1397_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1403_ = v_a_1397_;
v_isShared_1404_ = v_isSharedCheck_1428_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_val_1401_);
lean_dec(v_a_1397_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1428_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v_fst_1405_; lean_object* v_snd_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v_fst_1405_ = lean_ctor_get(v_val_1401_, 0);
lean_inc(v_fst_1405_);
v_snd_1406_ = lean_ctor_get(v_val_1401_, 1);
lean_inc(v_snd_1406_);
lean_dec(v_val_1401_);
v___x_1407_ = l_BitVec_clz(v_fst_1405_, v_snd_1406_);
lean_dec(v_snd_1406_);
v___x_1408_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_1405_, v___x_1407_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1419_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1419_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1419_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v_a_1409_);
v___x_1414_ = v___x_1403_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1416_; 
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1414_);
v___x_1416_ = v___x_1411_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_del_object(v___x_1403_);
v_a_1420_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1408_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1408_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
lean_dec(v_a_1397_);
v___x_1429_ = lean_box(0);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1429_);
v___x_1431_ = v___x_1399_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
v_a_1434_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1396_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1396_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVClz___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1384_ = stack[0].m_obj;
lean_object* v___y_1385_ = stack[1].m_obj;
lean_object* v___y_1386_ = stack[2].m_obj;
lean_object* v___y_1387_ = stack[3].m_obj;
lean_object* v___y_1388_ = stack[4].m_obj;
lean_object* v___y_1389_ = stack[5].m_obj;
lean_object* v___y_1390_ = stack[6].m_obj;
lean_object* v___y_1391_ = stack[7].m_obj;
lean_object* v___y_1392_ = stack[8].m_obj;
lean_object* v___y_1393_ = stack[9].m_obj;
lean_object* v___y_1394_ = stack[10].m_obj;
lean_object* v_res_1442_;
v_res_1442_ = l_Lean_Meta_Grind_propagateBVClz___lam__0(v_r_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
stack->m_obj
 = v_res_1442_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVClz___lam__0___boxed(lean_object* v_r_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_Meta_Grind_propagateBVClz___lam__0(v_r_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec(v___y_1444_);
return v_res_1455_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVClz(lean_object* v_e_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
v___x_1473_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVClz___closed__1));
v___x_1474_ = lean_unsigned_to_nat(2u);
v___x_1475_ = l_Lean_Expr_isAppOfArity(v_e_1461_, v___x_1473_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
lean_dec_ref(v_e_1461_);
v___x_1476_ = lean_box(0);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
return v___x_1477_;
}
else
{
lean_object* v___f_1478_; lean_object* v___x_1479_; 
v___f_1478_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVClz___closed__2));
v___x_1479_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1461_, v___f_1478_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
return v___x_1479_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVClz_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1461_ = stack[0].m_obj;
lean_object* v_a_1462_ = stack[1].m_obj;
lean_object* v_a_1463_ = stack[2].m_obj;
lean_object* v_a_1464_ = stack[3].m_obj;
lean_object* v_a_1465_ = stack[4].m_obj;
lean_object* v_a_1466_ = stack[5].m_obj;
lean_object* v_a_1467_ = stack[6].m_obj;
lean_object* v_a_1468_ = stack[7].m_obj;
lean_object* v_a_1469_ = stack[8].m_obj;
lean_object* v_a_1470_ = stack[9].m_obj;
lean_object* v_a_1471_ = stack[10].m_obj;
lean_object* v_res_1480_;
v_res_1480_ = l_Lean_Meta_Grind_propagateBVClz(v_e_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
stack->m_obj
 = v_res_1480_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVClz___boxed(lean_object* v_e_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_Meta_Grind_propagateBVClz(v_e_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
lean_dec(v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_a_1487_);
lean_dec_ref(v_a_1486_);
lean_dec(v_a_1485_);
lean_dec_ref(v_a_1484_);
lean_dec(v_a_1483_);
lean_dec(v_a_1482_);
return v_res_1493_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVClz___regBuiltin_Lean_Meta_Grind_propagateBVClz_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3163129259____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1495_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVClz___closed__1));
v___x_1496_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVClz___boxed), 12, 0);
v___x_1497_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1495_, v___x_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVClz___regBuiltin_Lean_Meta_Grind_propagateBVClz_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3163129259____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1498_;
v_res_1498_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVClz___regBuiltin_Lean_Meta_Grind_propagateBVClz_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3163129259____hygCtx___hyg_9_();
stack->m_obj
 = v_res_1498_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVClz___regBuiltin_Lean_Meta_Grind_propagateBVClz_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3163129259____hygCtx___hyg_9____boxed(lean_object* v_a_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVClz___regBuiltin_Lean_Meta_Grind_propagateBVClz_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3163129259____hygCtx___hyg_9_();
return v_res_1500_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVCpop___lam__0(lean_object* v_r_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1501_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1550_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1550_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1550_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
if (lean_obj_tag(v_a_1514_) == 1)
{
lean_object* v_val_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1545_; 
lean_del_object(v___x_1516_);
v_val_1518_ = lean_ctor_get(v_a_1514_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_a_1514_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1520_ = v_a_1514_;
v_isShared_1521_ = v_isSharedCheck_1545_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_val_1518_);
lean_dec(v_a_1514_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1545_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v_fst_1522_; lean_object* v_snd_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_fst_1522_ = lean_ctor_get(v_val_1518_, 0);
lean_inc_n(v_fst_1522_, 2);
v_snd_1523_ = lean_ctor_get(v_val_1518_, 1);
lean_inc(v_snd_1523_);
lean_dec(v_val_1518_);
v___x_1524_ = l_BitVec_cpop(v_fst_1522_, v_snd_1523_);
lean_dec(v_snd_1523_);
v___x_1525_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_1522_, v___x_1524_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1536_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1528_ = v___x_1525_;
v_isShared_1529_ = v_isSharedCheck_1536_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1536_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v_a_1526_);
v___x_1531_ = v___x_1520_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1533_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v___x_1531_);
v___x_1533_ = v___x_1528_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_del_object(v___x_1520_);
v_a_1537_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1525_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1525_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1548_; 
lean_dec(v_a_1514_);
v___x_1546_ = lean_box(0);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1546_);
v___x_1548_ = v___x_1516_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
v_a_1551_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1513_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1513_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVCpop___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1501_ = stack[0].m_obj;
lean_object* v___y_1502_ = stack[1].m_obj;
lean_object* v___y_1503_ = stack[2].m_obj;
lean_object* v___y_1504_ = stack[3].m_obj;
lean_object* v___y_1505_ = stack[4].m_obj;
lean_object* v___y_1506_ = stack[5].m_obj;
lean_object* v___y_1507_ = stack[6].m_obj;
lean_object* v___y_1508_ = stack[7].m_obj;
lean_object* v___y_1509_ = stack[8].m_obj;
lean_object* v___y_1510_ = stack[9].m_obj;
lean_object* v___y_1511_ = stack[10].m_obj;
lean_object* v_res_1559_;
v_res_1559_ = l_Lean_Meta_Grind_propagateBVCpop___lam__0(v_r_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
stack->m_obj
 = v_res_1559_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVCpop___lam__0___boxed(lean_object* v_r_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Meta_Grind_propagateBVCpop___lam__0(v_r_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec(v___y_1561_);
return v_res_1572_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVCpop(lean_object* v_e_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1590_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVCpop___closed__1));
v___x_1591_ = lean_unsigned_to_nat(2u);
v___x_1592_ = l_Lean_Expr_isAppOfArity(v_e_1578_, v___x_1590_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
lean_dec_ref(v_e_1578_);
v___x_1593_ = lean_box(0);
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
return v___x_1594_;
}
else
{
lean_object* v___f_1595_; lean_object* v___x_1596_; 
v___f_1595_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVCpop___closed__2));
v___x_1596_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1578_, v___f_1595_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
return v___x_1596_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVCpop_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1578_ = stack[0].m_obj;
lean_object* v_a_1579_ = stack[1].m_obj;
lean_object* v_a_1580_ = stack[2].m_obj;
lean_object* v_a_1581_ = stack[3].m_obj;
lean_object* v_a_1582_ = stack[4].m_obj;
lean_object* v_a_1583_ = stack[5].m_obj;
lean_object* v_a_1584_ = stack[6].m_obj;
lean_object* v_a_1585_ = stack[7].m_obj;
lean_object* v_a_1586_ = stack[8].m_obj;
lean_object* v_a_1587_ = stack[9].m_obj;
lean_object* v_a_1588_ = stack[10].m_obj;
lean_object* v_res_1597_;
v_res_1597_ = l_Lean_Meta_Grind_propagateBVCpop(v_e_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
stack->m_obj
 = v_res_1597_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVCpop___boxed(lean_object* v_e_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Meta_Grind_propagateBVCpop(v_e_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec(v_a_1599_);
return v_res_1610_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVCpop___regBuiltin_Lean_Meta_Grind_propagateBVCpop_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4094280043____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVCpop___closed__1));
v___x_1613_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVCpop___boxed), 12, 0);
v___x_1614_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1612_, v___x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVCpop___regBuiltin_Lean_Meta_Grind_propagateBVCpop_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4094280043____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1615_;
v_res_1615_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVCpop___regBuiltin_Lean_Meta_Grind_propagateBVCpop_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4094280043____hygCtx___hyg_9_();
stack->m_obj
 = v_res_1615_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVCpop___regBuiltin_Lean_Meta_Grind_propagateBVCpop_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4094280043____hygCtx___hyg_9____boxed(lean_object* v_a_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVCpop___regBuiltin_Lean_Meta_Grind_propagateBVCpop_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4094280043____hygCtx___hyg_9_();
return v_res_1617_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVMsb___lam__0(lean_object* v_r_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1618_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1667_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1667_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1667_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
uint8_t v___y_1636_; 
if (lean_obj_tag(v_a_1631_) == 1)
{
lean_object* v_val_1655_; lean_object* v_fst_1656_; lean_object* v_snd_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
lean_del_object(v___x_1633_);
v_val_1655_ = lean_ctor_get(v_a_1631_, 0);
lean_inc(v_val_1655_);
lean_dec_ref_known(v_a_1631_, 1);
v_fst_1656_ = lean_ctor_get(v_val_1655_, 0);
lean_inc(v_fst_1656_);
v_snd_1657_ = lean_ctor_get(v_val_1655_, 1);
lean_inc(v_snd_1657_);
lean_dec(v_val_1655_);
v___x_1658_ = lean_unsigned_to_nat(0u);
v___x_1659_ = lean_nat_dec_lt(v___x_1658_, v_fst_1656_);
if (v___x_1659_ == 0)
{
lean_dec(v_snd_1657_);
lean_dec(v_fst_1656_);
v___y_1636_ = v___x_1659_;
goto v___jp_1635_;
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v___x_1660_ = lean_unsigned_to_nat(1u);
v___x_1661_ = lean_nat_sub(v_fst_1656_, v___x_1660_);
lean_dec(v_fst_1656_);
v___x_1662_ = l_Nat_testBit(v_snd_1657_, v___x_1661_);
lean_dec(v___x_1661_);
lean_dec(v_snd_1657_);
v___y_1636_ = v___x_1662_;
goto v___jp_1635_;
}
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
lean_dec(v_a_1631_);
v___x_1663_ = lean_box(0);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1663_);
v___x_1665_ = v___x_1633_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
v___jp_1635_:
{
lean_object* v___x_1637_; 
v___x_1637_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v___y_1636_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1646_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1646_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1646_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1642_, 0, v_a_1638_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1642_);
v___x_1644_ = v___x_1640_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
v_a_1647_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1637_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1637_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
v_a_1668_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1630_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1630_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVMsb___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1618_ = stack[0].m_obj;
lean_object* v___y_1619_ = stack[1].m_obj;
lean_object* v___y_1620_ = stack[2].m_obj;
lean_object* v___y_1621_ = stack[3].m_obj;
lean_object* v___y_1622_ = stack[4].m_obj;
lean_object* v___y_1623_ = stack[5].m_obj;
lean_object* v___y_1624_ = stack[6].m_obj;
lean_object* v___y_1625_ = stack[7].m_obj;
lean_object* v___y_1626_ = stack[8].m_obj;
lean_object* v___y_1627_ = stack[9].m_obj;
lean_object* v___y_1628_ = stack[10].m_obj;
lean_object* v_res_1676_;
v_res_1676_ = l_Lean_Meta_Grind_propagateBVMsb___lam__0(v_r_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
stack->m_obj
 = v_res_1676_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVMsb___lam__0___boxed(lean_object* v_r_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_Meta_Grind_propagateBVMsb___lam__0(v_r_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec(v___y_1678_);
return v_res_1689_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVMsb(lean_object* v_e_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1707_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVMsb___closed__1));
v___x_1708_ = lean_unsigned_to_nat(2u);
v___x_1709_ = l_Lean_Expr_isAppOfArity(v_e_1695_, v___x_1707_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
lean_dec_ref(v_e_1695_);
v___x_1710_ = lean_box(0);
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
return v___x_1711_;
}
else
{
lean_object* v___f_1712_; lean_object* v___x_1713_; 
v___f_1712_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVMsb___closed__2));
v___x_1713_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1695_, v___f_1712_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
return v___x_1713_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVMsb_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1695_ = stack[0].m_obj;
lean_object* v_a_1696_ = stack[1].m_obj;
lean_object* v_a_1697_ = stack[2].m_obj;
lean_object* v_a_1698_ = stack[3].m_obj;
lean_object* v_a_1699_ = stack[4].m_obj;
lean_object* v_a_1700_ = stack[5].m_obj;
lean_object* v_a_1701_ = stack[6].m_obj;
lean_object* v_a_1702_ = stack[7].m_obj;
lean_object* v_a_1703_ = stack[8].m_obj;
lean_object* v_a_1704_ = stack[9].m_obj;
lean_object* v_a_1705_ = stack[10].m_obj;
lean_object* v_res_1714_;
v_res_1714_ = l_Lean_Meta_Grind_propagateBVMsb(v_e_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
stack->m_obj
 = v_res_1714_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVMsb___boxed(lean_object* v_e_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_Meta_Grind_propagateBVMsb(v_e_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
lean_dec(v_a_1725_);
lean_dec_ref(v_a_1724_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec(v_a_1716_);
return v_res_1727_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVMsb___regBuiltin_Lean_Meta_Grind_propagateBVMsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1379739246____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVMsb___closed__1));
v___x_1730_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVMsb___boxed), 12, 0);
v___x_1731_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1729_, v___x_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVMsb___regBuiltin_Lean_Meta_Grind_propagateBVMsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1379739246____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1732_;
v_res_1732_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVMsb___regBuiltin_Lean_Meta_Grind_propagateBVMsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1379739246____hygCtx___hyg_9_();
stack->m_obj
 = v_res_1732_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVMsb___regBuiltin_Lean_Meta_Grind_propagateBVMsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1379739246____hygCtx___hyg_9____boxed(lean_object* v_a_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVMsb___regBuiltin_Lean_Meta_Grind_propagateBVMsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1379739246____hygCtx___hyg_9_();
return v_res_1734_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVToNat___lam__0(lean_object* v_r_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1735_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1783_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1783_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1783_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
if (lean_obj_tag(v_a_1748_) == 1)
{
lean_object* v_val_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1778_; 
lean_del_object(v___x_1750_);
v_val_1752_ = lean_ctor_get(v_a_1748_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_a_1748_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1754_ = v_a_1748_;
v_isShared_1755_ = v_isSharedCheck_1778_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_val_1752_);
lean_dec(v_a_1748_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1778_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v_snd_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v_snd_1756_ = lean_ctor_get(v_val_1752_, 1);
lean_inc(v_snd_1756_);
lean_dec(v_val_1752_);
v___x_1757_ = l_Lean_mkNatLit(v_snd_1756_);
v___x_1758_ = l_Lean_Meta_Sym_shareCommon(v___x_1757_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1769_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1769_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1769_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v_a_1759_);
v___x_1764_ = v___x_1754_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1766_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1764_);
v___x_1766_ = v___x_1761_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_del_object(v___x_1754_);
v_a_1770_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1758_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1758_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
lean_dec(v_a_1748_);
v___x_1779_ = lean_box(0);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1779_);
v___x_1781_ = v___x_1750_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_a_1784_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1747_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1747_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVToNat___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1735_ = stack[0].m_obj;
lean_object* v___y_1736_ = stack[1].m_obj;
lean_object* v___y_1737_ = stack[2].m_obj;
lean_object* v___y_1738_ = stack[3].m_obj;
lean_object* v___y_1739_ = stack[4].m_obj;
lean_object* v___y_1740_ = stack[5].m_obj;
lean_object* v___y_1741_ = stack[6].m_obj;
lean_object* v___y_1742_ = stack[7].m_obj;
lean_object* v___y_1743_ = stack[8].m_obj;
lean_object* v___y_1744_ = stack[9].m_obj;
lean_object* v___y_1745_ = stack[10].m_obj;
lean_object* v_res_1792_;
v_res_1792_ = l_Lean_Meta_Grind_propagateBVToNat___lam__0(v_r_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
stack->m_obj
 = v_res_1792_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToNat___lam__0___boxed(lean_object* v_r_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_Meta_Grind_propagateBVToNat___lam__0(v_r_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec(v___y_1794_);
return v_res_1805_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVToNat(lean_object* v_e_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1823_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToNat___closed__1));
v___x_1824_ = lean_unsigned_to_nat(2u);
v___x_1825_ = l_Lean_Expr_isAppOfArity(v_e_1811_, v___x_1823_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_dec_ref(v_e_1811_);
v___x_1826_ = lean_box(0);
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
else
{
lean_object* v___f_1828_; lean_object* v___x_1829_; 
v___f_1828_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToNat___closed__2));
v___x_1829_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1811_, v___f_1828_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
return v___x_1829_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVToNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1811_ = stack[0].m_obj;
lean_object* v_a_1812_ = stack[1].m_obj;
lean_object* v_a_1813_ = stack[2].m_obj;
lean_object* v_a_1814_ = stack[3].m_obj;
lean_object* v_a_1815_ = stack[4].m_obj;
lean_object* v_a_1816_ = stack[5].m_obj;
lean_object* v_a_1817_ = stack[6].m_obj;
lean_object* v_a_1818_ = stack[7].m_obj;
lean_object* v_a_1819_ = stack[8].m_obj;
lean_object* v_a_1820_ = stack[9].m_obj;
lean_object* v_a_1821_ = stack[10].m_obj;
lean_object* v_res_1830_;
v_res_1830_ = l_Lean_Meta_Grind_propagateBVToNat(v_e_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
stack->m_obj
 = v_res_1830_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToNat___boxed(lean_object* v_e_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_Meta_Grind_propagateBVToNat(v_e_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec(v_a_1832_);
return v_res_1843_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToNat___regBuiltin_Lean_Meta_Grind_propagateBVToNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1265925494____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToNat___closed__1));
v___x_1846_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVToNat___boxed), 12, 0);
v___x_1847_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1845_, v___x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToNat___regBuiltin_Lean_Meta_Grind_propagateBVToNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1265925494____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1848_;
v_res_1848_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToNat___regBuiltin_Lean_Meta_Grind_propagateBVToNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1265925494____hygCtx___hyg_9_();
stack->m_obj
 = v_res_1848_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToNat___regBuiltin_Lean_Meta_Grind_propagateBVToNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1265925494____hygCtx___hyg_9____boxed(lean_object* v_a_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToNat___regBuiltin_Lean_Meta_Grind_propagateBVToNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1265925494____hygCtx___hyg_9_();
return v_res_1850_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVToInt___lam__0(lean_object* v_r_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1851_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1901_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1866_ = v___x_1863_;
v_isShared_1867_ = v_isSharedCheck_1901_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1863_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1901_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
if (lean_obj_tag(v_a_1864_) == 1)
{
lean_object* v_val_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1896_; 
lean_del_object(v___x_1866_);
v_val_1868_ = lean_ctor_get(v_a_1864_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_a_1864_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1870_ = v_a_1864_;
v_isShared_1871_ = v_isSharedCheck_1896_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_val_1868_);
lean_dec(v_a_1864_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1896_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v_fst_1872_; lean_object* v_snd_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v_fst_1872_ = lean_ctor_get(v_val_1868_, 0);
lean_inc(v_fst_1872_);
v_snd_1873_ = lean_ctor_get(v_val_1868_, 1);
lean_inc(v_snd_1873_);
lean_dec(v_val_1868_);
v___x_1874_ = l_BitVec_toInt(v_fst_1872_, v_snd_1873_);
lean_dec(v_fst_1872_);
v___x_1875_ = l_Lean_mkIntLit(v___x_1874_);
lean_dec(v___x_1874_);
v___x_1876_ = l_Lean_Meta_Sym_shareCommon(v___x_1875_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1887_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1887_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1887_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v_a_1877_);
v___x_1882_ = v___x_1870_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1884_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1882_);
v___x_1884_ = v___x_1879_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
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
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_del_object(v___x_1870_);
v_a_1888_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1876_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1876_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
lean_dec(v_a_1864_);
v___x_1897_ = lean_box(0);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 0, v___x_1897_);
v___x_1899_ = v___x_1866_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
v_a_1902_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1863_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1863_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVToInt___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1851_ = stack[0].m_obj;
lean_object* v___y_1852_ = stack[1].m_obj;
lean_object* v___y_1853_ = stack[2].m_obj;
lean_object* v___y_1854_ = stack[3].m_obj;
lean_object* v___y_1855_ = stack[4].m_obj;
lean_object* v___y_1856_ = stack[5].m_obj;
lean_object* v___y_1857_ = stack[6].m_obj;
lean_object* v___y_1858_ = stack[7].m_obj;
lean_object* v___y_1859_ = stack[8].m_obj;
lean_object* v___y_1860_ = stack[9].m_obj;
lean_object* v___y_1861_ = stack[10].m_obj;
lean_object* v_res_1910_;
v_res_1910_ = l_Lean_Meta_Grind_propagateBVToInt___lam__0(v_r_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
stack->m_obj
 = v_res_1910_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToInt___lam__0___boxed(lean_object* v_r_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_Meta_Grind_propagateBVToInt___lam__0(v_r_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec(v___y_1912_);
return v_res_1923_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVToInt(lean_object* v_e_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1941_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToInt___closed__1));
v___x_1942_ = lean_unsigned_to_nat(2u);
v___x_1943_ = l_Lean_Expr_isAppOfArity(v_e_1929_, v___x_1941_, v___x_1942_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
lean_dec_ref(v_e_1929_);
v___x_1944_ = lean_box(0);
v___x_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
return v___x_1945_;
}
else
{
lean_object* v___f_1946_; lean_object* v___x_1947_; 
v___f_1946_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToInt___closed__2));
v___x_1947_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1929_, v___f_1946_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
return v___x_1947_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVToInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1929_ = stack[0].m_obj;
lean_object* v_a_1930_ = stack[1].m_obj;
lean_object* v_a_1931_ = stack[2].m_obj;
lean_object* v_a_1932_ = stack[3].m_obj;
lean_object* v_a_1933_ = stack[4].m_obj;
lean_object* v_a_1934_ = stack[5].m_obj;
lean_object* v_a_1935_ = stack[6].m_obj;
lean_object* v_a_1936_ = stack[7].m_obj;
lean_object* v_a_1937_ = stack[8].m_obj;
lean_object* v_a_1938_ = stack[9].m_obj;
lean_object* v_a_1939_ = stack[10].m_obj;
lean_object* v_res_1948_;
v_res_1948_ = l_Lean_Meta_Grind_propagateBVToInt(v_e_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
stack->m_obj
 = v_res_1948_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToInt___boxed(lean_object* v_e_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_Meta_Grind_propagateBVToInt(v_e_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_);
lean_dec(v_a_1959_);
lean_dec_ref(v_a_1958_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec(v_a_1950_);
return v_res_1961_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToInt___regBuiltin_Lean_Meta_Grind_propagateBVToInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2998338308____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToInt___closed__1));
v___x_1964_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVToInt___boxed), 12, 0);
v___x_1965_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1963_, v___x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToInt___regBuiltin_Lean_Meta_Grind_propagateBVToInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2998338308____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1966_;
v_res_1966_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToInt___regBuiltin_Lean_Meta_Grind_propagateBVToInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2998338308____hygCtx___hyg_9_();
stack->m_obj
 = v_res_1966_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToInt___regBuiltin_Lean_Meta_Grind_propagateBVToInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2998338308____hygCtx___hyg_9____boxed(lean_object* v_a_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToInt___regBuiltin_Lean_Meta_Grind_propagateBVToInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2998338308____hygCtx___hyg_9_();
return v_res_1968_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVOfNat___lam__0(lean_object* v_val_1969_, lean_object* v_r_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Lean_Meta_getNatValue_x3f(v_r_1970_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2017_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_2017_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2017_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
if (lean_obj_tag(v_a_1983_) == 1)
{
lean_object* v_val_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2012_; 
lean_del_object(v___x_1985_);
v_val_1987_ = lean_ctor_get(v_a_1983_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_a_1983_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1989_ = v_a_1983_;
v_isShared_1990_ = v_isSharedCheck_2012_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_val_1987_);
lean_dec(v_a_1983_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2012_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = l_BitVec_ofNat(v_val_1969_, v_val_1987_);
lean_dec(v_val_1987_);
v___x_1992_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_val_1969_, v___x_1991_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2003_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2003_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2003_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v_a_1993_);
v___x_1998_ = v___x_1989_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
lean_object* v___x_2000_; 
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_1998_);
v___x_2000_ = v___x_1995_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_del_object(v___x_1989_);
v_a_2004_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1992_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_1992_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2015_; 
lean_dec(v_a_1983_);
lean_dec(v_val_1969_);
v___x_2013_ = lean_box(0);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_2013_);
v___x_2015_ = v___x_1985_;
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
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v_val_1969_);
v_a_2018_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_1982_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_1982_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVOfNat___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1969_ = stack[0].m_obj;
lean_object* v_r_1970_ = stack[1].m_obj;
lean_object* v___y_1971_ = stack[2].m_obj;
lean_object* v___y_1972_ = stack[3].m_obj;
lean_object* v___y_1973_ = stack[4].m_obj;
lean_object* v___y_1974_ = stack[5].m_obj;
lean_object* v___y_1975_ = stack[6].m_obj;
lean_object* v___y_1976_ = stack[7].m_obj;
lean_object* v___y_1977_ = stack[8].m_obj;
lean_object* v___y_1978_ = stack[9].m_obj;
lean_object* v___y_1979_ = stack[10].m_obj;
lean_object* v___y_1980_ = stack[11].m_obj;
lean_object* v_res_2026_;
v_res_2026_ = l_Lean_Meta_Grind_propagateBVOfNat___lam__0(v_val_1969_, v_r_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
stack->m_obj
 = v_res_2026_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat___lam__0___boxed(lean_object* v_val_2027_, lean_object* v_r_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_Meta_Grind_propagateBVOfNat___lam__0(v_val_2027_, v_r_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v_r_2028_);
return v_res_2040_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVOfNat(lean_object* v_e_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2057_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOfNat___closed__1));
v___x_2058_ = lean_unsigned_to_nat(2u);
v___x_2059_ = l_Lean_Expr_isAppOfArity(v_e_2045_, v___x_2057_, v___x_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
lean_dec_ref(v_e_2045_);
v___x_2060_ = lean_box(0);
v___x_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
return v___x_2061_;
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2062_ = l_Lean_Expr_getAppNumArgs(v_e_2045_);
v___x_2063_ = lean_unsigned_to_nat(1u);
v___x_2064_ = lean_nat_sub(v___x_2062_, v___x_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = l_Lean_Expr_getRevArg_x21(v_e_2045_, v___x_2064_);
v___x_2066_ = l_Lean_Meta_getNatValue_x3f(v___x_2065_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
lean_dec_ref(v___x_2065_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2078_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2078_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2078_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
if (lean_obj_tag(v_a_2067_) == 1)
{
lean_object* v_val_2071_; lean_object* v___f_2072_; lean_object* v___x_2073_; 
lean_del_object(v___x_2069_);
v_val_2071_ = lean_ctor_get(v_a_2067_, 0);
lean_inc(v_val_2071_);
lean_dec_ref_known(v_a_2067_, 1);
v___f_2072_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVOfNat___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2072_, 0, v_val_2071_);
v___x_2073_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2045_, v___f_2072_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
return v___x_2073_;
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
lean_dec(v_a_2067_);
lean_dec_ref(v_e_2045_);
v___x_2074_ = lean_box(0);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2074_);
v___x_2076_ = v___x_2069_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec_ref(v_e_2045_);
v_a_2079_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2066_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2066_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVOfNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2045_ = stack[0].m_obj;
lean_object* v_a_2046_ = stack[1].m_obj;
lean_object* v_a_2047_ = stack[2].m_obj;
lean_object* v_a_2048_ = stack[3].m_obj;
lean_object* v_a_2049_ = stack[4].m_obj;
lean_object* v_a_2050_ = stack[5].m_obj;
lean_object* v_a_2051_ = stack[6].m_obj;
lean_object* v_a_2052_ = stack[7].m_obj;
lean_object* v_a_2053_ = stack[8].m_obj;
lean_object* v_a_2054_ = stack[9].m_obj;
lean_object* v_a_2055_ = stack[10].m_obj;
lean_object* v_res_2087_;
v_res_2087_ = l_Lean_Meta_Grind_propagateBVOfNat(v_e_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
stack->m_obj
 = v_res_2087_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat___boxed(lean_object* v_e_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_Meta_Grind_propagateBVOfNat(v_e_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
lean_dec(v_a_2092_);
lean_dec_ref(v_a_2091_);
lean_dec(v_a_2090_);
lean_dec(v_a_2089_);
return v_res_2100_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1693823724____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2102_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOfNat___closed__1));
v___x_2103_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVOfNat___boxed), 12, 0);
v___x_2104_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2102_, v___x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1693823724____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2105_;
v_res_2105_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1693823724____hygCtx___hyg_9_();
stack->m_obj
 = v_res_2105_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1693823724____hygCtx___hyg_9____boxed(lean_object* v_a_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1693823724____hygCtx___hyg_9_();
return v_res_2107_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVOfInt___lam__0(lean_object* v_val_2108_, lean_object* v_r_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_Meta_getIntValue_x3f(v_r_2109_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2156_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2156_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2156_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
if (lean_obj_tag(v_a_2122_) == 1)
{
lean_object* v_val_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2151_; 
lean_del_object(v___x_2124_);
v_val_2126_ = lean_ctor_get(v_a_2122_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_a_2122_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2128_ = v_a_2122_;
v_isShared_2129_ = v_isSharedCheck_2151_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_val_2126_);
lean_dec(v_a_2122_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2151_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = l_BitVec_ofInt(v_val_2108_, v_val_2126_);
lean_dec(v_val_2126_);
v___x_2131_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_val_2108_, v___x_2130_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2142_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2134_ = v___x_2131_;
v_isShared_2135_ = v_isSharedCheck_2142_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2131_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2142_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v_a_2132_);
v___x_2137_ = v___x_2128_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2139_; 
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2137_);
v___x_2139_ = v___x_2134_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
lean_del_object(v___x_2128_);
v_a_2143_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2131_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2131_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2154_; 
lean_dec(v_a_2122_);
lean_dec(v_val_2108_);
v___x_2152_ = lean_box(0);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2152_);
v___x_2154_ = v___x_2124_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2152_);
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
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec(v_val_2108_);
v_a_2157_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2121_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2121_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVOfInt___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2108_ = stack[0].m_obj;
lean_object* v_r_2109_ = stack[1].m_obj;
lean_object* v___y_2110_ = stack[2].m_obj;
lean_object* v___y_2111_ = stack[3].m_obj;
lean_object* v___y_2112_ = stack[4].m_obj;
lean_object* v___y_2113_ = stack[5].m_obj;
lean_object* v___y_2114_ = stack[6].m_obj;
lean_object* v___y_2115_ = stack[7].m_obj;
lean_object* v___y_2116_ = stack[8].m_obj;
lean_object* v___y_2117_ = stack[9].m_obj;
lean_object* v___y_2118_ = stack[10].m_obj;
lean_object* v___y_2119_ = stack[11].m_obj;
lean_object* v_res_2165_;
v_res_2165_ = l_Lean_Meta_Grind_propagateBVOfInt___lam__0(v_val_2108_, v_r_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
stack->m_obj
 = v_res_2165_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt___lam__0___boxed(lean_object* v_val_2166_, lean_object* v_r_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Lean_Meta_Grind_propagateBVOfInt___lam__0(v_val_2166_, v_r_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec(v___y_2168_);
return v_res_2179_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVOfInt(lean_object* v_e_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2196_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOfInt___closed__1));
v___x_2197_ = lean_unsigned_to_nat(2u);
v___x_2198_ = l_Lean_Expr_isAppOfArity(v_e_2184_, v___x_2196_, v___x_2197_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_dec_ref(v_e_2184_);
v___x_2199_ = lean_box(0);
v___x_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
return v___x_2200_;
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2201_ = l_Lean_Expr_getAppNumArgs(v_e_2184_);
v___x_2202_ = lean_unsigned_to_nat(1u);
v___x_2203_ = lean_nat_sub(v___x_2201_, v___x_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = l_Lean_Expr_getRevArg_x21(v_e_2184_, v___x_2203_);
v___x_2205_ = l_Lean_Meta_getNatValue_x3f(v___x_2204_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
lean_dec_ref(v___x_2204_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2217_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2217_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2217_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
if (lean_obj_tag(v_a_2206_) == 1)
{
lean_object* v_val_2210_; lean_object* v___f_2211_; lean_object* v___x_2212_; 
lean_del_object(v___x_2208_);
v_val_2210_ = lean_ctor_get(v_a_2206_, 0);
lean_inc(v_val_2210_);
lean_dec_ref_known(v_a_2206_, 1);
v___f_2211_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVOfInt___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2211_, 0, v_val_2210_);
v___x_2212_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2184_, v___f_2211_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
return v___x_2212_;
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2215_; 
lean_dec(v_a_2206_);
lean_dec_ref(v_e_2184_);
v___x_2213_ = lean_box(0);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2213_);
v___x_2215_ = v___x_2208_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_e_2184_);
v_a_2218_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2205_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2205_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVOfInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2184_ = stack[0].m_obj;
lean_object* v_a_2185_ = stack[1].m_obj;
lean_object* v_a_2186_ = stack[2].m_obj;
lean_object* v_a_2187_ = stack[3].m_obj;
lean_object* v_a_2188_ = stack[4].m_obj;
lean_object* v_a_2189_ = stack[5].m_obj;
lean_object* v_a_2190_ = stack[6].m_obj;
lean_object* v_a_2191_ = stack[7].m_obj;
lean_object* v_a_2192_ = stack[8].m_obj;
lean_object* v_a_2193_ = stack[9].m_obj;
lean_object* v_a_2194_ = stack[10].m_obj;
lean_object* v_res_2226_;
v_res_2226_ = l_Lean_Meta_Grind_propagateBVOfInt(v_e_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
stack->m_obj
 = v_res_2226_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt___boxed(lean_object* v_e_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_Meta_Grind_propagateBVOfInt(v_e_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2232_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec(v_a_2228_);
return v_res_2239_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_16048587____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOfInt___closed__1));
v___x_2242_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVOfInt___boxed), 12, 0);
v___x_2243_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2241_, v___x_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_16048587____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2244_;
v_res_2244_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_16048587____hygCtx___hyg_9_();
stack->m_obj
 = v_res_2244_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_16048587____hygCtx___hyg_9____boxed(lean_object* v_a_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_16048587____hygCtx___hyg_9_();
return v_res_2246_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___lam__0(lean_object* v_val_2247_, lean_object* v_r_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = l_Lean_Meta_getBitVecValue_x3f(v_r_2248_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2297_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2263_ = v___x_2260_;
v_isShared_2264_ = v_isSharedCheck_2297_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2260_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2297_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
if (lean_obj_tag(v_a_2261_) == 1)
{
lean_object* v_val_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2292_; 
lean_del_object(v___x_2263_);
v_val_2265_ = lean_ctor_get(v_a_2261_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v_a_2261_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2267_ = v_a_2261_;
v_isShared_2268_ = v_isSharedCheck_2292_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_val_2265_);
lean_dec(v_a_2261_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2292_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v_fst_2269_; lean_object* v_snd_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_fst_2269_ = lean_ctor_get(v_val_2265_, 0);
lean_inc(v_fst_2269_);
v_snd_2270_ = lean_ctor_get(v_val_2265_, 1);
lean_inc(v_snd_2270_);
lean_dec(v_val_2265_);
v___x_2271_ = l_BitVec_setWidth(v_fst_2269_, v_val_2247_, v_snd_2270_);
lean_dec(v_snd_2270_);
lean_dec(v_fst_2269_);
v___x_2272_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_val_2247_, v___x_2271_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2283_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2283_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2283_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v_a_2273_);
v___x_2278_ = v___x_2267_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2280_; 
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v___x_2278_);
v___x_2280_ = v___x_2275_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_del_object(v___x_2267_);
v_a_2284_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2272_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2272_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2295_; 
lean_dec(v_a_2261_);
lean_dec(v_val_2247_);
v___x_2293_ = lean_box(0);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v___x_2293_);
v___x_2295_ = v___x_2263_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
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
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec(v_val_2247_);
v_a_2298_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2260_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2260_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVSetWidth___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2247_ = stack[0].m_obj;
lean_object* v_r_2248_ = stack[1].m_obj;
lean_object* v___y_2249_ = stack[2].m_obj;
lean_object* v___y_2250_ = stack[3].m_obj;
lean_object* v___y_2251_ = stack[4].m_obj;
lean_object* v___y_2252_ = stack[5].m_obj;
lean_object* v___y_2253_ = stack[6].m_obj;
lean_object* v___y_2254_ = stack[7].m_obj;
lean_object* v___y_2255_ = stack[8].m_obj;
lean_object* v___y_2256_ = stack[9].m_obj;
lean_object* v___y_2257_ = stack[10].m_obj;
lean_object* v___y_2258_ = stack[11].m_obj;
lean_object* v_res_2306_;
v_res_2306_ = l_Lean_Meta_Grind_propagateBVSetWidth___lam__0(v_val_2247_, v_r_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
stack->m_obj
 = v_res_2306_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___lam__0___boxed(lean_object* v_val_2307_, lean_object* v_r_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_Meta_Grind_propagateBVSetWidth___lam__0(v_val_2307_, v_r_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec(v___y_2309_);
return v_res_2320_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVSetWidth(lean_object* v_e_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v___x_2337_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSetWidth___closed__1));
v___x_2338_ = lean_unsigned_to_nat(3u);
v___x_2339_ = l_Lean_Expr_isAppOfArity(v_e_2325_, v___x_2337_, v___x_2338_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
lean_dec_ref(v_e_2325_);
v___x_2340_ = lean_box(0);
v___x_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
return v___x_2341_;
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2342_ = lean_unsigned_to_nat(1u);
v___x_2343_ = l_Lean_Expr_getAppNumArgs(v_e_2325_);
v___x_2344_ = lean_nat_sub(v___x_2343_, v___x_2342_);
lean_dec(v___x_2343_);
v___x_2345_ = lean_nat_sub(v___x_2344_, v___x_2342_);
lean_dec(v___x_2344_);
v___x_2346_ = l_Lean_Expr_getRevArg_x21(v_e_2325_, v___x_2345_);
v___x_2347_ = l_Lean_Meta_getNatValue_x3f(v___x_2346_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec_ref(v___x_2346_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2359_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2359_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2359_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
if (lean_obj_tag(v_a_2348_) == 1)
{
lean_object* v_val_2352_; lean_object* v___f_2353_; lean_object* v___x_2354_; 
lean_del_object(v___x_2350_);
v_val_2352_ = lean_ctor_get(v_a_2348_, 0);
lean_inc(v_val_2352_);
lean_dec_ref_known(v_a_2348_, 1);
v___f_2353_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVSetWidth___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2353_, 0, v_val_2352_);
v___x_2354_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2325_, v___f_2353_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_2354_;
}
else
{
lean_object* v___x_2355_; lean_object* v___x_2357_; 
lean_dec(v_a_2348_);
lean_dec_ref(v_e_2325_);
v___x_2355_ = lean_box(0);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2355_);
v___x_2357_ = v___x_2350_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec_ref(v_e_2325_);
v_a_2360_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2347_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2347_);
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
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVSetWidth_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2325_ = stack[0].m_obj;
lean_object* v_a_2326_ = stack[1].m_obj;
lean_object* v_a_2327_ = stack[2].m_obj;
lean_object* v_a_2328_ = stack[3].m_obj;
lean_object* v_a_2329_ = stack[4].m_obj;
lean_object* v_a_2330_ = stack[5].m_obj;
lean_object* v_a_2331_ = stack[6].m_obj;
lean_object* v_a_2332_ = stack[7].m_obj;
lean_object* v_a_2333_ = stack[8].m_obj;
lean_object* v_a_2334_ = stack[9].m_obj;
lean_object* v_a_2335_ = stack[10].m_obj;
lean_object* v_res_2368_;
v_res_2368_ = l_Lean_Meta_Grind_propagateBVSetWidth(v_e_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
stack->m_obj
 = v_res_2368_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___boxed(lean_object* v_e_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_Meta_Grind_propagateBVSetWidth(v_e_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec(v_a_2371_);
lean_dec(v_a_2370_);
return v_res_2381_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2383_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSetWidth___closed__1));
v___x_2384_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVSetWidth___boxed), 12, 0);
v___x_2385_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2383_, v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2386_;
v_res_2386_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_9_();
stack->m_obj
 = v_res_2386_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_9____boxed(lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_9_();
return v_res_2388_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___lam__0(lean_object* v_val_2389_, lean_object* v_r_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = l_Lean_Meta_getBitVecValue_x3f(v_r_2390_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2439_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2405_ = v___x_2402_;
v_isShared_2406_ = v_isSharedCheck_2439_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2402_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2439_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
if (lean_obj_tag(v_a_2403_) == 1)
{
lean_object* v_val_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2434_; 
lean_del_object(v___x_2405_);
v_val_2407_ = lean_ctor_get(v_a_2403_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v_a_2403_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2409_ = v_a_2403_;
v_isShared_2410_ = v_isSharedCheck_2434_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_val_2407_);
lean_dec(v_a_2403_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2434_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v_fst_2411_; lean_object* v_snd_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v_fst_2411_ = lean_ctor_get(v_val_2407_, 0);
lean_inc(v_fst_2411_);
v_snd_2412_ = lean_ctor_get(v_val_2407_, 1);
lean_inc(v_snd_2412_);
lean_dec(v_val_2407_);
v___x_2413_ = l_BitVec_signExtend(v_fst_2411_, v_val_2389_, v_snd_2412_);
lean_dec(v_fst_2411_);
v___x_2414_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_val_2389_, v___x_2413_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2425_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2417_ = v___x_2414_;
v_isShared_2418_ = v_isSharedCheck_2425_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2414_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2425_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 0, v_a_2415_);
v___x_2420_ = v___x_2409_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
lean_object* v___x_2422_; 
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 0, v___x_2420_);
v___x_2422_ = v___x_2417_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_del_object(v___x_2409_);
v_a_2426_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2414_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2414_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
}
else
{
lean_object* v___x_2435_; lean_object* v___x_2437_; 
lean_dec(v_a_2403_);
lean_dec(v_val_2389_);
v___x_2435_ = lean_box(0);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2435_);
v___x_2437_ = v___x_2405_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2435_);
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
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec(v_val_2389_);
v_a_2440_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2402_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2402_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVSignExtend___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2389_ = stack[0].m_obj;
lean_object* v_r_2390_ = stack[1].m_obj;
lean_object* v___y_2391_ = stack[2].m_obj;
lean_object* v___y_2392_ = stack[3].m_obj;
lean_object* v___y_2393_ = stack[4].m_obj;
lean_object* v___y_2394_ = stack[5].m_obj;
lean_object* v___y_2395_ = stack[6].m_obj;
lean_object* v___y_2396_ = stack[7].m_obj;
lean_object* v___y_2397_ = stack[8].m_obj;
lean_object* v___y_2398_ = stack[9].m_obj;
lean_object* v___y_2399_ = stack[10].m_obj;
lean_object* v___y_2400_ = stack[11].m_obj;
lean_object* v_res_2448_;
v_res_2448_ = l_Lean_Meta_Grind_propagateBVSignExtend___lam__0(v_val_2389_, v_r_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
stack->m_obj
 = v_res_2448_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___lam__0___boxed(lean_object* v_val_2449_, lean_object* v_r_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_Meta_Grind_propagateBVSignExtend___lam__0(v_val_2449_, v_r_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec(v___y_2451_);
return v_res_2462_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVSignExtend(lean_object* v_e_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
v___x_2479_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSignExtend___closed__1));
v___x_2480_ = lean_unsigned_to_nat(3u);
v___x_2481_ = l_Lean_Expr_isAppOfArity(v_e_2467_, v___x_2479_, v___x_2480_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_dec_ref(v_e_2467_);
v___x_2482_ = lean_box(0);
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
return v___x_2483_;
}
else
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2484_ = lean_unsigned_to_nat(1u);
v___x_2485_ = l_Lean_Expr_getAppNumArgs(v_e_2467_);
v___x_2486_ = lean_nat_sub(v___x_2485_, v___x_2484_);
lean_dec(v___x_2485_);
v___x_2487_ = lean_nat_sub(v___x_2486_, v___x_2484_);
lean_dec(v___x_2486_);
v___x_2488_ = l_Lean_Expr_getRevArg_x21(v_e_2467_, v___x_2487_);
v___x_2489_ = l_Lean_Meta_getNatValue_x3f(v___x_2488_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
lean_dec_ref(v___x_2488_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2501_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2492_ = v___x_2489_;
v_isShared_2493_ = v_isSharedCheck_2501_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2489_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2501_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
if (lean_obj_tag(v_a_2490_) == 1)
{
lean_object* v_val_2494_; lean_object* v___f_2495_; lean_object* v___x_2496_; 
lean_del_object(v___x_2492_);
v_val_2494_ = lean_ctor_get(v_a_2490_, 0);
lean_inc(v_val_2494_);
lean_dec_ref_known(v_a_2490_, 1);
v___f_2495_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVSignExtend___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2495_, 0, v_val_2494_);
v___x_2496_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2467_, v___f_2495_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
return v___x_2496_;
}
else
{
lean_object* v___x_2497_; lean_object* v___x_2499_; 
lean_dec(v_a_2490_);
lean_dec_ref(v_e_2467_);
v___x_2497_ = lean_box(0);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v___x_2497_);
v___x_2499_ = v___x_2492_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
lean_dec_ref(v_e_2467_);
v_a_2502_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2489_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2489_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVSignExtend_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2467_ = stack[0].m_obj;
lean_object* v_a_2468_ = stack[1].m_obj;
lean_object* v_a_2469_ = stack[2].m_obj;
lean_object* v_a_2470_ = stack[3].m_obj;
lean_object* v_a_2471_ = stack[4].m_obj;
lean_object* v_a_2472_ = stack[5].m_obj;
lean_object* v_a_2473_ = stack[6].m_obj;
lean_object* v_a_2474_ = stack[7].m_obj;
lean_object* v_a_2475_ = stack[8].m_obj;
lean_object* v_a_2476_ = stack[9].m_obj;
lean_object* v_a_2477_ = stack[10].m_obj;
lean_object* v_res_2510_;
v_res_2510_ = l_Lean_Meta_Grind_propagateBVSignExtend(v_e_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
stack->m_obj
 = v_res_2510_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___boxed(lean_object* v_e_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_Meta_Grind_propagateBVSignExtend(v_e_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
lean_dec(v_a_2512_);
return v_res_2523_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSignExtend___closed__1));
v___x_2526_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVSignExtend___boxed), 12, 0);
v___x_2527_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2525_, v___x_2526_);
return v___x_2527_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2528_;
v_res_2528_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_9_();
stack->m_obj
 = v_res_2528_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_9____boxed(lean_object* v_a_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_9_();
return v_res_2530_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0(lean_object* v_val_2531_, lean_object* v_val_2532_, lean_object* v_r_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lean_Meta_getBitVecValue_x3f(v_r_2533_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2581_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2581_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2581_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
if (lean_obj_tag(v_a_2546_) == 1)
{
lean_object* v_val_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2576_; 
lean_del_object(v___x_2548_);
v_val_2550_ = lean_ctor_get(v_a_2546_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v_a_2546_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2552_ = v_a_2546_;
v_isShared_2553_ = v_isSharedCheck_2576_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_val_2550_);
lean_dec(v_a_2546_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2576_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v_snd_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v_snd_2554_ = lean_ctor_get(v_val_2550_, 1);
lean_inc(v_snd_2554_);
lean_dec(v_val_2550_);
v___x_2555_ = l_BitVec_extractLsb_x27___redArg(v_val_2531_, v_val_2532_, v_snd_2554_);
lean_dec(v_snd_2554_);
v___x_2556_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_val_2532_, v___x_2555_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2567_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2567_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2567_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v_a_2557_);
v___x_2562_ = v___x_2552_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
lean_object* v___x_2564_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2562_);
v___x_2564_ = v___x_2559_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2562_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_del_object(v___x_2552_);
v_a_2568_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2556_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2556_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
else
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
lean_dec(v_a_2546_);
lean_dec(v_val_2532_);
v___x_2577_ = lean_box(0);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v___x_2577_);
v___x_2579_ = v___x_2548_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_dec(v_val_2532_);
v_a_2582_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2545_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2545_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2531_ = stack[0].m_obj;
lean_object* v_val_2532_ = stack[1].m_obj;
lean_object* v_r_2533_ = stack[2].m_obj;
lean_object* v___y_2534_ = stack[3].m_obj;
lean_object* v___y_2535_ = stack[4].m_obj;
lean_object* v___y_2536_ = stack[5].m_obj;
lean_object* v___y_2537_ = stack[6].m_obj;
lean_object* v___y_2538_ = stack[7].m_obj;
lean_object* v___y_2539_ = stack[8].m_obj;
lean_object* v___y_2540_ = stack[9].m_obj;
lean_object* v___y_2541_ = stack[10].m_obj;
lean_object* v___y_2542_ = stack[11].m_obj;
lean_object* v___y_2543_ = stack[12].m_obj;
lean_object* v_res_2590_;
v_res_2590_ = l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0(v_val_2531_, v_val_2532_, v_r_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
stack->m_obj
 = v_res_2590_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0___boxed(lean_object* v_val_2591_, lean_object* v_val_2592_, lean_object* v_r_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0(v_val_2591_, v_val_2592_, v_r_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec(v_val_2591_);
return v_res_2605_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27(lean_object* v_e_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2622_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__1));
v___x_2623_ = lean_unsigned_to_nat(4u);
v___x_2624_ = l_Lean_Expr_isAppOfArity(v_e_2610_, v___x_2622_, v___x_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_dec_ref(v_e_2610_);
v___x_2625_ = lean_box(0);
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
return v___x_2626_;
}
else
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2627_ = lean_unsigned_to_nat(1u);
v___x_2628_ = l_Lean_Expr_getAppNumArgs(v_e_2610_);
v___x_2629_ = lean_nat_sub(v___x_2628_, v___x_2627_);
v___x_2630_ = lean_nat_sub(v___x_2629_, v___x_2627_);
lean_dec(v___x_2629_);
v___x_2631_ = l_Lean_Expr_getRevArg_x21(v_e_2610_, v___x_2630_);
v___x_2632_ = l_Lean_Meta_getNatValue_x3f(v___x_2631_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
lean_dec_ref(v___x_2631_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2667_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2635_ = v___x_2632_;
v_isShared_2636_ = v_isSharedCheck_2667_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2667_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
if (lean_obj_tag(v_a_2633_) == 1)
{
lean_object* v_val_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
lean_del_object(v___x_2635_);
v_val_2637_ = lean_ctor_get(v_a_2633_, 0);
lean_inc(v_val_2637_);
lean_dec_ref_known(v_a_2633_, 1);
v___x_2638_ = lean_unsigned_to_nat(2u);
v___x_2639_ = lean_nat_sub(v___x_2628_, v___x_2638_);
lean_dec(v___x_2628_);
v___x_2640_ = lean_nat_sub(v___x_2639_, v___x_2627_);
lean_dec(v___x_2639_);
v___x_2641_ = l_Lean_Expr_getRevArg_x21(v_e_2610_, v___x_2640_);
v___x_2642_ = l_Lean_Meta_getNatValue_x3f(v___x_2641_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
lean_dec_ref(v___x_2641_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2654_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2645_ = v___x_2642_;
v_isShared_2646_ = v_isSharedCheck_2654_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2642_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2654_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
if (lean_obj_tag(v_a_2643_) == 1)
{
lean_object* v_val_2647_; lean_object* v___f_2648_; lean_object* v___x_2649_; 
lean_del_object(v___x_2645_);
v_val_2647_ = lean_ctor_get(v_a_2643_, 0);
lean_inc(v_val_2647_);
lean_dec_ref_known(v_a_2643_, 1);
v___f_2648_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0___boxed), 14, 2);
lean_closure_set(v___f_2648_, 0, v_val_2637_);
lean_closure_set(v___f_2648_, 1, v_val_2647_);
v___x_2649_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2610_, v___f_2648_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
return v___x_2649_;
}
else
{
lean_object* v___x_2650_; lean_object* v___x_2652_; 
lean_dec(v_a_2643_);
lean_dec(v_val_2637_);
lean_dec_ref(v_e_2610_);
v___x_2650_ = lean_box(0);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2650_);
v___x_2652_ = v___x_2645_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
lean_dec(v_val_2637_);
lean_dec_ref(v_e_2610_);
v_a_2655_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2642_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2642_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2660_; 
if (v_isShared_2658_ == 0)
{
v___x_2660_ = v___x_2657_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
else
{
lean_object* v___x_2663_; lean_object* v___x_2665_; 
lean_dec(v_a_2633_);
lean_dec(v___x_2628_);
lean_dec_ref(v_e_2610_);
v___x_2663_ = lean_box(0);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v___x_2663_);
v___x_2665_ = v___x_2635_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2663_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v___x_2628_);
lean_dec_ref(v_e_2610_);
v_a_2668_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2632_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2632_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVExtractLsb_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2610_ = stack[0].m_obj;
lean_object* v_a_2611_ = stack[1].m_obj;
lean_object* v_a_2612_ = stack[2].m_obj;
lean_object* v_a_2613_ = stack[3].m_obj;
lean_object* v_a_2614_ = stack[4].m_obj;
lean_object* v_a_2615_ = stack[5].m_obj;
lean_object* v_a_2616_ = stack[6].m_obj;
lean_object* v_a_2617_ = stack[7].m_obj;
lean_object* v_a_2618_ = stack[8].m_obj;
lean_object* v_a_2619_ = stack[9].m_obj;
lean_object* v_a_2620_ = stack[10].m_obj;
lean_object* v_res_2676_;
v_res_2676_ = l_Lean_Meta_Grind_propagateBVExtractLsb_x27(v_e_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
stack->m_obj
 = v_res_2676_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___boxed(lean_object* v_e_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l_Lean_Meta_Grind_propagateBVExtractLsb_x27(v_e_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec(v_a_2678_);
return v_res_2689_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4241407876____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2691_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__1));
v___x_2692_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVExtractLsb_x27___boxed), 12, 0);
v___x_2693_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2691_, v___x_2692_);
return v___x_2693_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4241407876____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2694_;
v_res_2694_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4241407876____hygCtx___hyg_9_();
stack->m_obj
 = v_res_2694_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4241407876____hygCtx___hyg_9____boxed(lean_object* v_a_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4241407876____hygCtx___hyg_9_();
return v_res_2696_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0(lean_object* v_val_2697_, lean_object* v_val_2698_, lean_object* v___x_2699_, lean_object* v_r_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l_Lean_Meta_getBitVecValue_x3f(v_r_2700_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2750_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2715_ = v___x_2712_;
v_isShared_2716_ = v_isSharedCheck_2750_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2712_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2750_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
if (lean_obj_tag(v_a_2713_) == 1)
{
lean_object* v_val_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2745_; 
lean_del_object(v___x_2715_);
v_val_2717_ = lean_ctor_get(v_a_2713_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_a_2713_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2719_ = v_a_2713_;
v_isShared_2720_ = v_isSharedCheck_2745_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_val_2717_);
lean_dec(v_a_2713_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2745_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v_snd_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v_snd_2721_ = lean_ctor_get(v_val_2717_, 1);
lean_inc(v_snd_2721_);
lean_dec(v_val_2717_);
v___x_2722_ = lean_nat_sub(v_val_2697_, v_val_2698_);
v___x_2723_ = lean_nat_add(v___x_2722_, v___x_2699_);
lean_dec(v___x_2722_);
v___x_2724_ = l_BitVec_extractLsb___redArg(v_val_2697_, v_val_2698_, v_snd_2721_);
lean_dec(v_snd_2721_);
v___x_2725_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v___x_2723_, v___x_2724_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2736_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2728_ = v___x_2725_;
v_isShared_2729_ = v_isSharedCheck_2736_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2725_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2736_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v_a_2726_);
v___x_2731_ = v___x_2719_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_object* v___x_2733_; 
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2731_);
v___x_2733_ = v___x_2728_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_del_object(v___x_2719_);
v_a_2737_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2725_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2725_);
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
else
{
lean_object* v___x_2746_; lean_object* v___x_2748_; 
lean_dec(v_a_2713_);
v___x_2746_ = lean_box(0);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 0, v___x_2746_);
v___x_2748_ = v___x_2715_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2746_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
v_a_2751_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2712_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2712_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2697_ = stack[0].m_obj;
lean_object* v_val_2698_ = stack[1].m_obj;
lean_object* v___x_2699_ = stack[2].m_obj;
lean_object* v_r_2700_ = stack[3].m_obj;
lean_object* v___y_2701_ = stack[4].m_obj;
lean_object* v___y_2702_ = stack[5].m_obj;
lean_object* v___y_2703_ = stack[6].m_obj;
lean_object* v___y_2704_ = stack[7].m_obj;
lean_object* v___y_2705_ = stack[8].m_obj;
lean_object* v___y_2706_ = stack[9].m_obj;
lean_object* v___y_2707_ = stack[10].m_obj;
lean_object* v___y_2708_ = stack[11].m_obj;
lean_object* v___y_2709_ = stack[12].m_obj;
lean_object* v___y_2710_ = stack[13].m_obj;
lean_object* v_res_2759_;
v_res_2759_ = l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0(v_val_2697_, v_val_2698_, v___x_2699_, v_r_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
stack->m_obj
 = v_res_2759_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0___boxed(lean_object* v_val_2760_, lean_object* v_val_2761_, lean_object* v___x_2762_, lean_object* v_r_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0(v_val_2760_, v_val_2761_, v___x_2762_, v_r_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec(v___x_2762_);
lean_dec(v_val_2761_);
lean_dec(v_val_2760_);
return v_res_2775_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb(lean_object* v_e_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; uint8_t v___x_2794_; 
v___x_2792_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1));
v___x_2793_ = lean_unsigned_to_nat(4u);
v___x_2794_ = l_Lean_Expr_isAppOfArity(v_e_2780_, v___x_2792_, v___x_2793_);
if (v___x_2794_ == 0)
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
lean_dec_ref(v_e_2780_);
v___x_2795_ = lean_box(0);
v___x_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
return v___x_2796_;
}
else
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2797_ = lean_unsigned_to_nat(1u);
v___x_2798_ = l_Lean_Expr_getAppNumArgs(v_e_2780_);
v___x_2799_ = lean_nat_sub(v___x_2798_, v___x_2797_);
v___x_2800_ = lean_nat_sub(v___x_2799_, v___x_2797_);
lean_dec(v___x_2799_);
v___x_2801_ = l_Lean_Expr_getRevArg_x21(v_e_2780_, v___x_2800_);
v___x_2802_ = l_Lean_Meta_getNatValue_x3f(v___x_2801_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_);
lean_dec_ref(v___x_2801_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2837_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2805_ = v___x_2802_;
v_isShared_2806_ = v_isSharedCheck_2837_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2837_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
if (lean_obj_tag(v_a_2803_) == 1)
{
lean_object* v_val_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
lean_del_object(v___x_2805_);
v_val_2807_ = lean_ctor_get(v_a_2803_, 0);
lean_inc(v_val_2807_);
lean_dec_ref_known(v_a_2803_, 1);
v___x_2808_ = lean_unsigned_to_nat(2u);
v___x_2809_ = lean_nat_sub(v___x_2798_, v___x_2808_);
lean_dec(v___x_2798_);
v___x_2810_ = lean_nat_sub(v___x_2809_, v___x_2797_);
lean_dec(v___x_2809_);
v___x_2811_ = l_Lean_Expr_getRevArg_x21(v_e_2780_, v___x_2810_);
v___x_2812_ = l_Lean_Meta_getNatValue_x3f(v___x_2811_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_);
lean_dec_ref(v___x_2811_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2824_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2824_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2824_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
if (lean_obj_tag(v_a_2813_) == 1)
{
lean_object* v_val_2817_; lean_object* v___f_2818_; lean_object* v___x_2819_; 
lean_del_object(v___x_2815_);
v_val_2817_ = lean_ctor_get(v_a_2813_, 0);
lean_inc(v_val_2817_);
lean_dec_ref_known(v_a_2813_, 1);
v___f_2818_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0___boxed), 15, 3);
lean_closure_set(v___f_2818_, 0, v_val_2807_);
lean_closure_set(v___f_2818_, 1, v_val_2817_);
lean_closure_set(v___f_2818_, 2, v___x_2797_);
v___x_2819_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2780_, v___f_2818_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_);
return v___x_2819_;
}
else
{
lean_object* v___x_2820_; lean_object* v___x_2822_; 
lean_dec(v_a_2813_);
lean_dec(v_val_2807_);
lean_dec_ref(v_e_2780_);
v___x_2820_ = lean_box(0);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2820_);
v___x_2822_ = v___x_2815_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec(v_val_2807_);
lean_dec_ref(v_e_2780_);
v_a_2825_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2812_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2812_);
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
else
{
lean_object* v___x_2833_; lean_object* v___x_2835_; 
lean_dec(v_a_2803_);
lean_dec(v___x_2798_);
lean_dec_ref(v_e_2780_);
v___x_2833_ = lean_box(0);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v___x_2833_);
v___x_2835_ = v___x_2805_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2833_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_dec(v___x_2798_);
lean_dec_ref(v_e_2780_);
v_a_2838_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2802_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2802_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVExtractLsb_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2780_ = stack[0].m_obj;
lean_object* v_a_2781_ = stack[1].m_obj;
lean_object* v_a_2782_ = stack[2].m_obj;
lean_object* v_a_2783_ = stack[3].m_obj;
lean_object* v_a_2784_ = stack[4].m_obj;
lean_object* v_a_2785_ = stack[5].m_obj;
lean_object* v_a_2786_ = stack[6].m_obj;
lean_object* v_a_2787_ = stack[7].m_obj;
lean_object* v_a_2788_ = stack[8].m_obj;
lean_object* v_a_2789_ = stack[9].m_obj;
lean_object* v_a_2790_ = stack[10].m_obj;
lean_object* v_res_2846_;
v_res_2846_ = l_Lean_Meta_Grind_propagateBVExtractLsb(v_e_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_);
stack->m_obj
 = v_res_2846_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___boxed(lean_object* v_e_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Lean_Meta_Grind_propagateBVExtractLsb(v_e_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
lean_dec(v_a_2848_);
return v_res_2859_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3429100332____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2861_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1));
v___x_2862_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVExtractLsb___boxed), 12, 0);
v___x_2863_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2861_, v___x_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3429100332____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2864_;
v_res_2864_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3429100332____hygCtx___hyg_9_();
stack->m_obj
 = v_res_2864_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3429100332____hygCtx___hyg_9____boxed(lean_object* v_a_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3429100332____hygCtx___hyg_9_();
return v_res_2866_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVReplicate___lam__0(lean_object* v_val_2867_, lean_object* v_r_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Lean_Meta_getBitVecValue_x3f(v_r_2868_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2918_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2883_ = v___x_2880_;
v_isShared_2884_ = v_isSharedCheck_2918_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2880_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2918_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
if (lean_obj_tag(v_a_2881_) == 1)
{
lean_object* v_val_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2913_; 
lean_del_object(v___x_2883_);
v_val_2885_ = lean_ctor_get(v_a_2881_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_a_2881_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2887_ = v_a_2881_;
v_isShared_2888_ = v_isSharedCheck_2913_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_val_2885_);
lean_dec(v_a_2881_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2913_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v_fst_2889_; lean_object* v_snd_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v_fst_2889_ = lean_ctor_get(v_val_2885_, 0);
lean_inc(v_fst_2889_);
v_snd_2890_ = lean_ctor_get(v_val_2885_, 1);
lean_inc(v_snd_2890_);
lean_dec(v_val_2885_);
v___x_2891_ = lean_nat_mul(v_fst_2889_, v_val_2867_);
v___x_2892_ = l_BitVec_replicate(v_fst_2889_, v_val_2867_, v_snd_2890_);
lean_dec(v_snd_2890_);
lean_dec(v_fst_2889_);
v___x_2893_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v___x_2891_, v___x_2892_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2904_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2896_ = v___x_2893_;
v_isShared_2897_ = v_isSharedCheck_2904_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2893_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2904_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v_a_2894_);
v___x_2899_ = v___x_2887_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2901_; 
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2899_);
v___x_2901_ = v___x_2896_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2899_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_del_object(v___x_2887_);
v_a_2905_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2893_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2893_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
}
else
{
lean_object* v___x_2914_; lean_object* v___x_2916_; 
lean_dec(v_a_2881_);
v___x_2914_ = lean_box(0);
if (v_isShared_2884_ == 0)
{
lean_ctor_set(v___x_2883_, 0, v___x_2914_);
v___x_2916_ = v___x_2883_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2914_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
v_a_2919_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2880_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2880_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVReplicate___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2867_ = stack[0].m_obj;
lean_object* v_r_2868_ = stack[1].m_obj;
lean_object* v___y_2869_ = stack[2].m_obj;
lean_object* v___y_2870_ = stack[3].m_obj;
lean_object* v___y_2871_ = stack[4].m_obj;
lean_object* v___y_2872_ = stack[5].m_obj;
lean_object* v___y_2873_ = stack[6].m_obj;
lean_object* v___y_2874_ = stack[7].m_obj;
lean_object* v___y_2875_ = stack[8].m_obj;
lean_object* v___y_2876_ = stack[9].m_obj;
lean_object* v___y_2877_ = stack[10].m_obj;
lean_object* v___y_2878_ = stack[11].m_obj;
lean_object* v_res_2927_;
v_res_2927_ = l_Lean_Meta_Grind_propagateBVReplicate___lam__0(v_val_2867_, v_r_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
stack->m_obj
 = v_res_2927_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate___lam__0___boxed(lean_object* v_val_2928_, lean_object* v_r_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Lean_Meta_Grind_propagateBVReplicate___lam__0(v_val_2928_, v_r_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec(v_val_2928_);
return v_res_2941_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVReplicate(lean_object* v_e_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v___x_2958_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVReplicate___closed__1));
v___x_2959_ = lean_unsigned_to_nat(3u);
v___x_2960_ = l_Lean_Expr_isAppOfArity(v_e_2946_, v___x_2958_, v___x_2959_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
lean_dec_ref(v_e_2946_);
v___x_2961_ = lean_box(0);
v___x_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
return v___x_2962_;
}
else
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2963_ = lean_unsigned_to_nat(1u);
v___x_2964_ = l_Lean_Expr_getAppNumArgs(v_e_2946_);
v___x_2965_ = lean_nat_sub(v___x_2964_, v___x_2963_);
lean_dec(v___x_2964_);
v___x_2966_ = lean_nat_sub(v___x_2965_, v___x_2963_);
lean_dec(v___x_2965_);
v___x_2967_ = l_Lean_Expr_getRevArg_x21(v_e_2946_, v___x_2966_);
v___x_2968_ = l_Lean_Meta_getNatValue_x3f(v___x_2967_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
lean_dec_ref(v___x_2967_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2980_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2971_ = v___x_2968_;
v_isShared_2972_ = v_isSharedCheck_2980_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2968_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2980_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
if (lean_obj_tag(v_a_2969_) == 1)
{
lean_object* v_val_2973_; lean_object* v___f_2974_; lean_object* v___x_2975_; 
lean_del_object(v___x_2971_);
v_val_2973_ = lean_ctor_get(v_a_2969_, 0);
lean_inc(v_val_2973_);
lean_dec_ref_known(v_a_2969_, 1);
v___f_2974_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVReplicate___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2974_, 0, v_val_2973_);
v___x_2975_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2946_, v___f_2974_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
return v___x_2975_;
}
else
{
lean_object* v___x_2976_; lean_object* v___x_2978_; 
lean_dec(v_a_2969_);
lean_dec_ref(v_e_2946_);
v___x_2976_ = lean_box(0);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 0, v___x_2976_);
v___x_2978_ = v___x_2971_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2976_);
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
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec_ref(v_e_2946_);
v_a_2981_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2968_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2968_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVReplicate_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2946_ = stack[0].m_obj;
lean_object* v_a_2947_ = stack[1].m_obj;
lean_object* v_a_2948_ = stack[2].m_obj;
lean_object* v_a_2949_ = stack[3].m_obj;
lean_object* v_a_2950_ = stack[4].m_obj;
lean_object* v_a_2951_ = stack[5].m_obj;
lean_object* v_a_2952_ = stack[6].m_obj;
lean_object* v_a_2953_ = stack[7].m_obj;
lean_object* v_a_2954_ = stack[8].m_obj;
lean_object* v_a_2955_ = stack[9].m_obj;
lean_object* v_a_2956_ = stack[10].m_obj;
lean_object* v_res_2989_;
v_res_2989_ = l_Lean_Meta_Grind_propagateBVReplicate(v_e_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
stack->m_obj
 = v_res_2989_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate___boxed(lean_object* v_e_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Lean_Meta_Grind_propagateBVReplicate(v_e_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_);
lean_dec(v_a_3000_);
lean_dec_ref(v_a_2999_);
lean_dec(v_a_2998_);
lean_dec_ref(v_a_2997_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec(v_a_2992_);
lean_dec(v_a_2991_);
return v_res_3002_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3327375609____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3004_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVReplicate___closed__1));
v___x_3005_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVReplicate___boxed), 12, 0);
v___x_3006_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3004_, v___x_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3327375609____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3007_;
v_res_3007_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3327375609____hygCtx___hyg_9_();
stack->m_obj
 = v_res_3007_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3327375609____hygCtx___hyg_9____boxed(lean_object* v_a_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3327375609____hygCtx___hyg_9_();
return v_res_3009_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVAnd___lam__0(lean_object* v_r_u2081_3010_, lean_object* v_r_u2082_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v___x_3023_; 
v___x_3023_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3010_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3086_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3086_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3086_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
if (lean_obj_tag(v_a_3024_) == 1)
{
lean_object* v_val_3028_; lean_object* v_fst_3029_; lean_object* v_snd_3030_; lean_object* v___x_3031_; 
lean_del_object(v___x_3026_);
v_val_3028_ = lean_ctor_get(v_a_3024_, 0);
lean_inc(v_val_3028_);
lean_dec_ref_known(v_a_3024_, 1);
v_fst_3029_ = lean_ctor_get(v_val_3028_, 0);
lean_inc(v_fst_3029_);
v_snd_3030_ = lean_ctor_get(v_val_3028_, 1);
lean_inc(v_snd_3030_);
lean_dec(v_val_3028_);
v___x_3031_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_3011_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3073_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3034_ = v___x_3031_;
v_isShared_3035_ = v_isSharedCheck_3073_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3031_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3073_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
if (lean_obj_tag(v_a_3032_) == 1)
{
lean_object* v_val_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3068_; 
v_val_3036_ = lean_ctor_get(v_a_3032_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v_a_3032_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3038_ = v_a_3032_;
v_isShared_3039_ = v_isSharedCheck_3068_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_val_3036_);
lean_dec(v_a_3032_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3068_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v_fst_3040_; lean_object* v_snd_3041_; uint8_t v___x_3042_; 
v_fst_3040_ = lean_ctor_get(v_val_3036_, 0);
lean_inc(v_fst_3040_);
v_snd_3041_ = lean_ctor_get(v_val_3036_, 1);
lean_inc(v_snd_3041_);
lean_dec(v_val_3036_);
v___x_3042_ = lean_nat_dec_eq(v_fst_3029_, v_fst_3040_);
lean_dec(v_fst_3040_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3043_; lean_object* v___x_3045_; 
lean_dec(v_snd_3041_);
lean_del_object(v___x_3038_);
lean_dec(v_snd_3030_);
lean_dec(v_fst_3029_);
v___x_3043_ = lean_box(0);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 0, v___x_3043_);
v___x_3045_ = v___x_3034_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3043_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
else
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
lean_del_object(v___x_3034_);
v___x_3047_ = lean_nat_land(v_snd_3030_, v_snd_3041_);
lean_dec(v_snd_3041_);
lean_dec(v_snd_3030_);
v___x_3048_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3029_, v___x_3047_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3059_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3051_ = v___x_3048_;
v_isShared_3052_ = v_isSharedCheck_3059_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3048_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3059_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v_a_3049_);
v___x_3054_ = v___x_3038_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
lean_object* v___x_3056_; 
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v___x_3054_);
v___x_3056_ = v___x_3051_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_del_object(v___x_3038_);
v_a_3060_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3048_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3048_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
}
else
{
lean_object* v___x_3069_; lean_object* v___x_3071_; 
lean_dec(v_a_3032_);
lean_dec(v_snd_3030_);
lean_dec(v_fst_3029_);
v___x_3069_ = lean_box(0);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 0, v___x_3069_);
v___x_3071_ = v___x_3034_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3069_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec(v_snd_3030_);
lean_dec(v_fst_3029_);
v_a_3074_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3031_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3031_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
else
{
lean_object* v___x_3082_; lean_object* v___x_3084_; 
lean_dec(v_a_3024_);
lean_dec_ref(v_r_u2082_3011_);
v___x_3082_ = lean_box(0);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v___x_3082_);
v___x_3084_ = v___x_3026_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3082_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec_ref(v_r_u2082_3011_);
v_a_3087_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3023_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3023_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVAnd___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_u2081_3010_ = stack[0].m_obj;
lean_object* v_r_u2082_3011_ = stack[1].m_obj;
lean_object* v___y_3012_ = stack[2].m_obj;
lean_object* v___y_3013_ = stack[3].m_obj;
lean_object* v___y_3014_ = stack[4].m_obj;
lean_object* v___y_3015_ = stack[5].m_obj;
lean_object* v___y_3016_ = stack[6].m_obj;
lean_object* v___y_3017_ = stack[7].m_obj;
lean_object* v___y_3018_ = stack[8].m_obj;
lean_object* v___y_3019_ = stack[9].m_obj;
lean_object* v___y_3020_ = stack[10].m_obj;
lean_object* v___y_3021_ = stack[11].m_obj;
lean_object* v_res_3095_;
v_res_3095_ = l_Lean_Meta_Grind_propagateBVAnd___lam__0(v_r_u2081_3010_, v_r_u2082_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
stack->m_obj
 = v_res_3095_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAnd___lam__0___boxed(lean_object* v_r_u2081_3096_, lean_object* v_r_u2082_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lean_Meta_Grind_propagateBVAnd___lam__0(v_r_u2081_3096_, v_r_u2082_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec(v___y_3098_);
return v_res_3109_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVAnd(lean_object* v_e_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; uint8_t v___x_3130_; 
v___x_3128_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAnd___closed__2));
v___x_3129_ = lean_unsigned_to_nat(6u);
v___x_3130_ = l_Lean_Expr_isAppOfArity(v_e_3116_, v___x_3128_, v___x_3129_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
lean_dec_ref(v_e_3116_);
v___x_3131_ = lean_box(0);
v___x_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
return v___x_3132_;
}
else
{
lean_object* v___f_3133_; lean_object* v___x_3134_; 
v___f_3133_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAnd___closed__3));
v___x_3134_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3116_, v___f_3133_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_);
return v___x_3134_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVAnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3116_ = stack[0].m_obj;
lean_object* v_a_3117_ = stack[1].m_obj;
lean_object* v_a_3118_ = stack[2].m_obj;
lean_object* v_a_3119_ = stack[3].m_obj;
lean_object* v_a_3120_ = stack[4].m_obj;
lean_object* v_a_3121_ = stack[5].m_obj;
lean_object* v_a_3122_ = stack[6].m_obj;
lean_object* v_a_3123_ = stack[7].m_obj;
lean_object* v_a_3124_ = stack[8].m_obj;
lean_object* v_a_3125_ = stack[9].m_obj;
lean_object* v_a_3126_ = stack[10].m_obj;
lean_object* v_res_3135_;
v_res_3135_ = l_Lean_Meta_Grind_propagateBVAnd(v_e_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_);
stack->m_obj
 = v_res_3135_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAnd___boxed(lean_object* v_e_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Lean_Meta_Grind_propagateBVAnd(v_e_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_);
lean_dec(v_a_3146_);
lean_dec_ref(v_a_3145_);
lean_dec(v_a_3144_);
lean_dec_ref(v_a_3143_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
lean_dec(v_a_3140_);
lean_dec_ref(v_a_3139_);
lean_dec(v_a_3138_);
lean_dec(v_a_3137_);
return v_res_3148_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAnd___regBuiltin_Lean_Meta_Grind_propagateBVAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_317501673____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3150_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAnd___closed__2));
v___x_3151_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVAnd___boxed), 12, 0);
v___x_3152_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3150_, v___x_3151_);
return v___x_3152_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAnd___regBuiltin_Lean_Meta_Grind_propagateBVAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_317501673____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3153_;
v_res_3153_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAnd___regBuiltin_Lean_Meta_Grind_propagateBVAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_317501673____hygCtx___hyg_9_();
stack->m_obj
 = v_res_3153_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAnd___regBuiltin_Lean_Meta_Grind_propagateBVAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_317501673____hygCtx___hyg_9____boxed(lean_object* v_a_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAnd___regBuiltin_Lean_Meta_Grind_propagateBVAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_317501673____hygCtx___hyg_9_();
return v_res_3155_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVOr___lam__0(lean_object* v_r_u2081_3156_, lean_object* v_r_u2082_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v___x_3169_; 
v___x_3169_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3156_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3232_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3232_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3232_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
if (lean_obj_tag(v_a_3170_) == 1)
{
lean_object* v_val_3174_; lean_object* v_fst_3175_; lean_object* v_snd_3176_; lean_object* v___x_3177_; 
lean_del_object(v___x_3172_);
v_val_3174_ = lean_ctor_get(v_a_3170_, 0);
lean_inc(v_val_3174_);
lean_dec_ref_known(v_a_3170_, 1);
v_fst_3175_ = lean_ctor_get(v_val_3174_, 0);
lean_inc(v_fst_3175_);
v_snd_3176_ = lean_ctor_get(v_val_3174_, 1);
lean_inc(v_snd_3176_);
lean_dec(v_val_3174_);
v___x_3177_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_3157_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3219_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3219_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3219_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
if (lean_obj_tag(v_a_3178_) == 1)
{
lean_object* v_val_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3214_; 
v_val_3182_ = lean_ctor_get(v_a_3178_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_a_3178_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3184_ = v_a_3178_;
v_isShared_3185_ = v_isSharedCheck_3214_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_val_3182_);
lean_dec(v_a_3178_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3214_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v_fst_3186_; lean_object* v_snd_3187_; uint8_t v___x_3188_; 
v_fst_3186_ = lean_ctor_get(v_val_3182_, 0);
lean_inc(v_fst_3186_);
v_snd_3187_ = lean_ctor_get(v_val_3182_, 1);
lean_inc(v_snd_3187_);
lean_dec(v_val_3182_);
v___x_3188_ = lean_nat_dec_eq(v_fst_3175_, v_fst_3186_);
lean_dec(v_fst_3186_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3189_; lean_object* v___x_3191_; 
lean_dec(v_snd_3187_);
lean_del_object(v___x_3184_);
lean_dec(v_snd_3176_);
lean_dec(v_fst_3175_);
v___x_3189_ = lean_box(0);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3189_);
v___x_3191_ = v___x_3180_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3189_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
lean_del_object(v___x_3180_);
v___x_3193_ = lean_nat_lor(v_snd_3176_, v_snd_3187_);
lean_dec(v_snd_3187_);
lean_dec(v_snd_3176_);
v___x_3194_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3175_, v___x_3193_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3205_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3205_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3205_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 0, v_a_3195_);
v___x_3200_ = v___x_3184_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3202_; 
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3200_);
v___x_3202_ = v___x_3197_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_del_object(v___x_3184_);
v_a_3206_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3194_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3194_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
}
}
else
{
lean_object* v___x_3215_; lean_object* v___x_3217_; 
lean_dec(v_a_3178_);
lean_dec(v_snd_3176_);
lean_dec(v_fst_3175_);
v___x_3215_ = lean_box(0);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3215_);
v___x_3217_ = v___x_3180_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3215_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
else
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
lean_dec(v_snd_3176_);
lean_dec(v_fst_3175_);
v_a_3220_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v___x_3177_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3177_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
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
return v___x_3225_;
}
}
}
}
else
{
lean_object* v___x_3228_; lean_object* v___x_3230_; 
lean_dec(v_a_3170_);
lean_dec_ref(v_r_u2082_3157_);
v___x_3228_ = lean_box(0);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v___x_3228_);
v___x_3230_ = v___x_3172_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3228_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
else
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3240_; 
lean_dec_ref(v_r_u2082_3157_);
v_a_3233_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3235_ = v___x_3169_;
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3169_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3238_; 
if (v_isShared_3236_ == 0)
{
v___x_3238_ = v___x_3235_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVOr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_u2081_3156_ = stack[0].m_obj;
lean_object* v_r_u2082_3157_ = stack[1].m_obj;
lean_object* v___y_3158_ = stack[2].m_obj;
lean_object* v___y_3159_ = stack[3].m_obj;
lean_object* v___y_3160_ = stack[4].m_obj;
lean_object* v___y_3161_ = stack[5].m_obj;
lean_object* v___y_3162_ = stack[6].m_obj;
lean_object* v___y_3163_ = stack[7].m_obj;
lean_object* v___y_3164_ = stack[8].m_obj;
lean_object* v___y_3165_ = stack[9].m_obj;
lean_object* v___y_3166_ = stack[10].m_obj;
lean_object* v___y_3167_ = stack[11].m_obj;
lean_object* v_res_3241_;
v_res_3241_ = l_Lean_Meta_Grind_propagateBVOr___lam__0(v_r_u2081_3156_, v_r_u2082_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
stack->m_obj
 = v_res_3241_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOr___lam__0___boxed(lean_object* v_r_u2081_3242_, lean_object* v_r_u2082_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l_Lean_Meta_Grind_propagateBVOr___lam__0(v_r_u2081_3242_, v_r_u2082_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec(v___y_3244_);
return v_res_3255_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVOr(lean_object* v_e_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; uint8_t v___x_3276_; 
v___x_3274_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOr___closed__2));
v___x_3275_ = lean_unsigned_to_nat(6u);
v___x_3276_ = l_Lean_Expr_isAppOfArity(v_e_3262_, v___x_3274_, v___x_3275_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
lean_dec_ref(v_e_3262_);
v___x_3277_ = lean_box(0);
v___x_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3277_);
return v___x_3278_;
}
else
{
lean_object* v___f_3279_; lean_object* v___x_3280_; 
v___f_3279_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOr___closed__3));
v___x_3280_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3262_, v___f_3279_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_);
return v___x_3280_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVOr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3262_ = stack[0].m_obj;
lean_object* v_a_3263_ = stack[1].m_obj;
lean_object* v_a_3264_ = stack[2].m_obj;
lean_object* v_a_3265_ = stack[3].m_obj;
lean_object* v_a_3266_ = stack[4].m_obj;
lean_object* v_a_3267_ = stack[5].m_obj;
lean_object* v_a_3268_ = stack[6].m_obj;
lean_object* v_a_3269_ = stack[7].m_obj;
lean_object* v_a_3270_ = stack[8].m_obj;
lean_object* v_a_3271_ = stack[9].m_obj;
lean_object* v_a_3272_ = stack[10].m_obj;
lean_object* v_res_3281_;
v_res_3281_ = l_Lean_Meta_Grind_propagateBVOr(v_e_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_);
stack->m_obj
 = v_res_3281_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOr___boxed(lean_object* v_e_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Lean_Meta_Grind_propagateBVOr(v_e_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
return v_res_3294_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOr___regBuiltin_Lean_Meta_Grind_propagateBVOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4272827602____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3296_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOr___closed__2));
v___x_3297_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVOr___boxed), 12, 0);
v___x_3298_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3296_, v___x_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOr___regBuiltin_Lean_Meta_Grind_propagateBVOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4272827602____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3299_;
v_res_3299_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOr___regBuiltin_Lean_Meta_Grind_propagateBVOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4272827602____hygCtx___hyg_9_();
stack->m_obj
 = v_res_3299_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOr___regBuiltin_Lean_Meta_Grind_propagateBVOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4272827602____hygCtx___hyg_9____boxed(lean_object* v_a_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOr___regBuiltin_Lean_Meta_Grind_propagateBVOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4272827602____hygCtx___hyg_9_();
return v_res_3301_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVXor___lam__0(lean_object* v_r_u2081_3302_, lean_object* v_r_u2082_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v___x_3315_; 
v___x_3315_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3302_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3378_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3318_ = v___x_3315_;
v_isShared_3319_ = v_isSharedCheck_3378_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3315_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3378_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
if (lean_obj_tag(v_a_3316_) == 1)
{
lean_object* v_val_3320_; lean_object* v_fst_3321_; lean_object* v_snd_3322_; lean_object* v___x_3323_; 
lean_del_object(v___x_3318_);
v_val_3320_ = lean_ctor_get(v_a_3316_, 0);
lean_inc(v_val_3320_);
lean_dec_ref_known(v_a_3316_, 1);
v_fst_3321_ = lean_ctor_get(v_val_3320_, 0);
lean_inc(v_fst_3321_);
v_snd_3322_ = lean_ctor_get(v_val_3320_, 1);
lean_inc(v_snd_3322_);
lean_dec(v_val_3320_);
v___x_3323_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_3303_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3365_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3326_ = v___x_3323_;
v_isShared_3327_ = v_isSharedCheck_3365_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3323_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3365_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
if (lean_obj_tag(v_a_3324_) == 1)
{
lean_object* v_val_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3360_; 
v_val_3328_ = lean_ctor_get(v_a_3324_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v_a_3324_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3330_ = v_a_3324_;
v_isShared_3331_ = v_isSharedCheck_3360_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_val_3328_);
lean_dec(v_a_3324_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3360_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v_fst_3332_; lean_object* v_snd_3333_; uint8_t v___x_3334_; 
v_fst_3332_ = lean_ctor_get(v_val_3328_, 0);
lean_inc(v_fst_3332_);
v_snd_3333_ = lean_ctor_get(v_val_3328_, 1);
lean_inc(v_snd_3333_);
lean_dec(v_val_3328_);
v___x_3334_ = lean_nat_dec_eq(v_fst_3321_, v_fst_3332_);
lean_dec(v_fst_3332_);
if (v___x_3334_ == 0)
{
lean_object* v___x_3335_; lean_object* v___x_3337_; 
lean_dec(v_snd_3333_);
lean_del_object(v___x_3330_);
lean_dec(v_snd_3322_);
lean_dec(v_fst_3321_);
v___x_3335_ = lean_box(0);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 0, v___x_3335_);
v___x_3337_ = v___x_3326_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3335_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
lean_del_object(v___x_3326_);
v___x_3339_ = lean_nat_lxor(v_snd_3322_, v_snd_3333_);
lean_dec(v_snd_3333_);
lean_dec(v_snd_3322_);
v___x_3340_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3321_, v___x_3339_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3351_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3343_ = v___x_3340_;
v_isShared_3344_ = v_isSharedCheck_3351_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3340_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3351_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v_a_3341_);
v___x_3346_ = v___x_3330_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
lean_object* v___x_3348_; 
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 0, v___x_3346_);
v___x_3348_ = v___x_3343_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
else
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
lean_del_object(v___x_3330_);
v_a_3352_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___x_3340_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3340_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
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
}
}
else
{
lean_object* v___x_3361_; lean_object* v___x_3363_; 
lean_dec(v_a_3324_);
lean_dec(v_snd_3322_);
lean_dec(v_fst_3321_);
v___x_3361_ = lean_box(0);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 0, v___x_3361_);
v___x_3363_ = v___x_3326_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3361_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
else
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
lean_dec(v_snd_3322_);
lean_dec(v_fst_3321_);
v_a_3366_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3323_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3323_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
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
return v___x_3371_;
}
}
}
}
else
{
lean_object* v___x_3374_; lean_object* v___x_3376_; 
lean_dec(v_a_3316_);
lean_dec_ref(v_r_u2082_3303_);
v___x_3374_ = lean_box(0);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 0, v___x_3374_);
v___x_3376_ = v___x_3318_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3374_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_dec_ref(v_r_u2082_3303_);
v_a_3379_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3315_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3315_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVXor___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_u2081_3302_ = stack[0].m_obj;
lean_object* v_r_u2082_3303_ = stack[1].m_obj;
lean_object* v___y_3304_ = stack[2].m_obj;
lean_object* v___y_3305_ = stack[3].m_obj;
lean_object* v___y_3306_ = stack[4].m_obj;
lean_object* v___y_3307_ = stack[5].m_obj;
lean_object* v___y_3308_ = stack[6].m_obj;
lean_object* v___y_3309_ = stack[7].m_obj;
lean_object* v___y_3310_ = stack[8].m_obj;
lean_object* v___y_3311_ = stack[9].m_obj;
lean_object* v___y_3312_ = stack[10].m_obj;
lean_object* v___y_3313_ = stack[11].m_obj;
lean_object* v_res_3387_;
v_res_3387_ = l_Lean_Meta_Grind_propagateBVXor___lam__0(v_r_u2081_3302_, v_r_u2082_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
stack->m_obj
 = v_res_3387_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVXor___lam__0___boxed(lean_object* v_r_u2081_3388_, lean_object* v_r_u2082_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Lean_Meta_Grind_propagateBVXor___lam__0(v_r_u2081_3388_, v_r_u2082_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec(v___y_3390_);
return v_res_3401_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVXor(lean_object* v_e_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; uint8_t v___x_3422_; 
v___x_3420_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVXor___closed__2));
v___x_3421_ = lean_unsigned_to_nat(6u);
v___x_3422_ = l_Lean_Expr_isAppOfArity(v_e_3408_, v___x_3420_, v___x_3421_);
if (v___x_3422_ == 0)
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
lean_dec_ref(v_e_3408_);
v___x_3423_ = lean_box(0);
v___x_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3423_);
return v___x_3424_;
}
else
{
lean_object* v___f_3425_; lean_object* v___x_3426_; 
v___f_3425_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVXor___closed__3));
v___x_3426_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3408_, v___f_3425_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
return v___x_3426_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVXor_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3408_ = stack[0].m_obj;
lean_object* v_a_3409_ = stack[1].m_obj;
lean_object* v_a_3410_ = stack[2].m_obj;
lean_object* v_a_3411_ = stack[3].m_obj;
lean_object* v_a_3412_ = stack[4].m_obj;
lean_object* v_a_3413_ = stack[5].m_obj;
lean_object* v_a_3414_ = stack[6].m_obj;
lean_object* v_a_3415_ = stack[7].m_obj;
lean_object* v_a_3416_ = stack[8].m_obj;
lean_object* v_a_3417_ = stack[9].m_obj;
lean_object* v_a_3418_ = stack[10].m_obj;
lean_object* v_res_3427_;
v_res_3427_ = l_Lean_Meta_Grind_propagateBVXor(v_e_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
stack->m_obj
 = v_res_3427_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVXor___boxed(lean_object* v_e_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l_Lean_Meta_Grind_propagateBVXor(v_e_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
lean_dec(v_a_3438_);
lean_dec_ref(v_a_3437_);
lean_dec(v_a_3436_);
lean_dec_ref(v_a_3435_);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3433_);
lean_dec(v_a_3432_);
lean_dec_ref(v_a_3431_);
lean_dec(v_a_3430_);
lean_dec(v_a_3429_);
return v_res_3440_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVXor___regBuiltin_Lean_Meta_Grind_propagateBVXor_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1120302969____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3442_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVXor___closed__2));
v___x_3443_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVXor___boxed), 12, 0);
v___x_3444_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3442_, v___x_3443_);
return v___x_3444_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVXor___regBuiltin_Lean_Meta_Grind_propagateBVXor_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1120302969____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3445_;
v_res_3445_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVXor___regBuiltin_Lean_Meta_Grind_propagateBVXor_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1120302969____hygCtx___hyg_9_();
stack->m_obj
 = v_res_3445_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVXor___regBuiltin_Lean_Meta_Grind_propagateBVXor_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1120302969____hygCtx___hyg_9____boxed(lean_object* v_a_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVXor___regBuiltin_Lean_Meta_Grind_propagateBVXor_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1120302969____hygCtx___hyg_9_();
return v_res_3447_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVAppend___lam__0(lean_object* v_r_u2081_3448_, lean_object* v_r_u2082_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v___x_3461_; 
v___x_3461_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3448_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3520_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3464_ = v___x_3461_;
v_isShared_3465_ = v_isSharedCheck_3520_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3461_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3520_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
if (lean_obj_tag(v_a_3462_) == 1)
{
lean_object* v_val_3466_; lean_object* v_fst_3467_; lean_object* v_snd_3468_; lean_object* v___x_3469_; 
lean_del_object(v___x_3464_);
v_val_3466_ = lean_ctor_get(v_a_3462_, 0);
lean_inc(v_val_3466_);
lean_dec_ref_known(v_a_3462_, 1);
v_fst_3467_ = lean_ctor_get(v_val_3466_, 0);
lean_inc(v_fst_3467_);
v_snd_3468_ = lean_ctor_get(v_val_3466_, 1);
lean_inc(v_snd_3468_);
lean_dec(v_val_3466_);
v___x_3469_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_3449_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3507_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3472_ = v___x_3469_;
v_isShared_3473_ = v_isSharedCheck_3507_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3469_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3507_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
if (lean_obj_tag(v_a_3470_) == 1)
{
lean_object* v_val_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3502_; 
lean_del_object(v___x_3472_);
v_val_3474_ = lean_ctor_get(v_a_3470_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v_a_3470_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3476_ = v_a_3470_;
v_isShared_3477_ = v_isSharedCheck_3502_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_val_3474_);
lean_dec(v_a_3470_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3502_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v_fst_3478_; lean_object* v_snd_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v_fst_3478_ = lean_ctor_get(v_val_3474_, 0);
lean_inc(v_fst_3478_);
v_snd_3479_ = lean_ctor_get(v_val_3474_, 1);
lean_inc(v_snd_3479_);
lean_dec(v_val_3474_);
v___x_3480_ = lean_nat_add(v_fst_3467_, v_fst_3478_);
lean_dec(v_fst_3467_);
v___x_3481_ = l_BitVec_append___redArg(v_fst_3478_, v_snd_3468_, v_snd_3479_);
lean_dec(v_snd_3479_);
lean_dec(v_snd_3468_);
lean_dec(v_fst_3478_);
v___x_3482_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v___x_3480_, v___x_3481_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3493_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3485_ = v___x_3482_;
v_isShared_3486_ = v_isSharedCheck_3493_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3482_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3493_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v_a_3483_);
v___x_3488_ = v___x_3476_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_object* v___x_3490_; 
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v___x_3488_);
v___x_3490_ = v___x_3485_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3488_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_del_object(v___x_3476_);
v_a_3494_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3482_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3482_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
}
else
{
lean_object* v___x_3503_; lean_object* v___x_3505_; 
lean_dec(v_a_3470_);
lean_dec(v_snd_3468_);
lean_dec(v_fst_3467_);
v___x_3503_ = lean_box(0);
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 0, v___x_3503_);
v___x_3505_ = v___x_3472_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v___x_3503_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec(v_snd_3468_);
lean_dec(v_fst_3467_);
v_a_3508_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3469_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3469_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
else
{
lean_object* v___x_3516_; lean_object* v___x_3518_; 
lean_dec(v_a_3462_);
lean_dec_ref(v_r_u2082_3449_);
v___x_3516_ = lean_box(0);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v___x_3516_);
v___x_3518_ = v___x_3464_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3516_);
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
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_dec_ref(v_r_u2082_3449_);
v_a_3521_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3461_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3461_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVAppend___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_u2081_3448_ = stack[0].m_obj;
lean_object* v_r_u2082_3449_ = stack[1].m_obj;
lean_object* v___y_3450_ = stack[2].m_obj;
lean_object* v___y_3451_ = stack[3].m_obj;
lean_object* v___y_3452_ = stack[4].m_obj;
lean_object* v___y_3453_ = stack[5].m_obj;
lean_object* v___y_3454_ = stack[6].m_obj;
lean_object* v___y_3455_ = stack[7].m_obj;
lean_object* v___y_3456_ = stack[8].m_obj;
lean_object* v___y_3457_ = stack[9].m_obj;
lean_object* v___y_3458_ = stack[10].m_obj;
lean_object* v___y_3459_ = stack[11].m_obj;
lean_object* v_res_3529_;
v_res_3529_ = l_Lean_Meta_Grind_propagateBVAppend___lam__0(v_r_u2081_3448_, v_r_u2082_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
stack->m_obj
 = v_res_3529_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAppend___lam__0___boxed(lean_object* v_r_u2081_3530_, lean_object* v_r_u2082_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_Lean_Meta_Grind_propagateBVAppend___lam__0(v_r_u2081_3530_, v_r_u2082_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec(v___y_3532_);
return v_res_3543_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVAppend(lean_object* v_e_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; uint8_t v___x_3564_; 
v___x_3562_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAppend___closed__2));
v___x_3563_ = lean_unsigned_to_nat(6u);
v___x_3564_ = l_Lean_Expr_isAppOfArity(v_e_3550_, v___x_3562_, v___x_3563_);
if (v___x_3564_ == 0)
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
lean_dec_ref(v_e_3550_);
v___x_3565_ = lean_box(0);
v___x_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3565_);
return v___x_3566_;
}
else
{
lean_object* v___f_3567_; lean_object* v___x_3568_; 
v___f_3567_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAppend___closed__3));
lean_inc(v_a_3560_);
lean_inc_ref(v_a_3559_);
lean_inc(v_a_3558_);
lean_inc_ref(v_a_3557_);
lean_inc_ref(v_e_3550_);
v___x_3568_ = lean_infer_type(v_e_3550_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3580_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3571_ = v___x_3568_;
v_isShared_3572_ = v_isSharedCheck_3580_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3568_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3580_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3573_; uint8_t v___x_3574_; 
v___x_3573_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__1));
v___x_3574_ = l_Lean_Expr_isAppOf(v_a_3569_, v___x_3573_);
lean_dec(v_a_3569_);
if (v___x_3574_ == 0)
{
lean_object* v___x_3575_; lean_object* v___x_3577_; 
lean_dec_ref(v_e_3550_);
v___x_3575_ = lean_box(0);
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 0, v___x_3575_);
v___x_3577_ = v___x_3571_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3575_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
else
{
lean_object* v___x_3579_; 
lean_del_object(v___x_3571_);
v___x_3579_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3550_, v___f_3567_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_);
return v___x_3579_;
}
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec_ref(v_e_3550_);
v_a_3581_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3568_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3568_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVAppend_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3550_ = stack[0].m_obj;
lean_object* v_a_3551_ = stack[1].m_obj;
lean_object* v_a_3552_ = stack[2].m_obj;
lean_object* v_a_3553_ = stack[3].m_obj;
lean_object* v_a_3554_ = stack[4].m_obj;
lean_object* v_a_3555_ = stack[5].m_obj;
lean_object* v_a_3556_ = stack[6].m_obj;
lean_object* v_a_3557_ = stack[7].m_obj;
lean_object* v_a_3558_ = stack[8].m_obj;
lean_object* v_a_3559_ = stack[9].m_obj;
lean_object* v_a_3560_ = stack[10].m_obj;
lean_object* v_res_3589_;
v_res_3589_ = l_Lean_Meta_Grind_propagateBVAppend(v_e_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_);
stack->m_obj
 = v_res_3589_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAppend___boxed(lean_object* v_e_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Lean_Meta_Grind_propagateBVAppend(v_e_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_a_3594_);
lean_dec_ref(v_a_3593_);
lean_dec(v_a_3592_);
lean_dec(v_a_3591_);
return v_res_3602_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4057925374____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3604_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAppend___closed__2));
v___x_3605_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVAppend___boxed), 12, 0);
v___x_3606_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3604_, v___x_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4057925374____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3607_;
v_res_3607_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4057925374____hygCtx___hyg_9_();
stack->m_obj
 = v_res_3607_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4057925374____hygCtx___hyg_9____boxed(lean_object* v_a_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4057925374____hygCtx___hyg_9_();
return v_res_3609_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___lam__0(lean_object* v_r_u2081_3610_, lean_object* v_r_u2082_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v___x_3623_; 
v___x_3623_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3610_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3679_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3626_ = v___x_3623_;
v_isShared_3627_ = v_isSharedCheck_3679_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3623_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3679_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
if (lean_obj_tag(v_a_3624_) == 1)
{
lean_object* v_val_3628_; lean_object* v_fst_3629_; lean_object* v_snd_3630_; lean_object* v___x_3631_; 
lean_del_object(v___x_3626_);
v_val_3628_ = lean_ctor_get(v_a_3624_, 0);
lean_inc(v_val_3628_);
lean_dec_ref_known(v_a_3624_, 1);
v_fst_3629_ = lean_ctor_get(v_val_3628_, 0);
lean_inc(v_fst_3629_);
v_snd_3630_ = lean_ctor_get(v_val_3628_, 1);
lean_inc(v_snd_3630_);
lean_dec(v_val_3628_);
v___x_3631_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_3611_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3666_; 
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3634_ = v___x_3631_;
v_isShared_3635_ = v_isSharedCheck_3666_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3631_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3666_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
if (lean_obj_tag(v_a_3632_) == 1)
{
lean_object* v_val_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3661_; 
lean_del_object(v___x_3634_);
v_val_3636_ = lean_ctor_get(v_a_3632_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v_a_3632_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3638_ = v_a_3632_;
v_isShared_3639_ = v_isSharedCheck_3661_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_val_3636_);
lean_dec(v_a_3632_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3661_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3640_ = l_BitVec_shiftLeft(v_fst_3629_, v_snd_3630_, v_val_3636_);
lean_dec(v_val_3636_);
lean_dec(v_snd_3630_);
v___x_3641_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3629_, v___x_3640_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3652_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3644_ = v___x_3641_;
v_isShared_3645_ = v_isSharedCheck_3652_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3641_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3652_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 0, v_a_3642_);
v___x_3647_ = v___x_3638_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3649_; 
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v___x_3647_);
v___x_3649_ = v___x_3644_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3647_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
else
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3660_; 
lean_del_object(v___x_3638_);
v_a_3653_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3655_ = v___x_3641_;
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3641_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3660_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3658_; 
if (v_isShared_3656_ == 0)
{
v___x_3658_ = v___x_3655_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_a_3653_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
}
}
else
{
lean_object* v___x_3662_; lean_object* v___x_3664_; 
lean_dec(v_a_3632_);
lean_dec(v_snd_3630_);
lean_dec(v_fst_3629_);
v___x_3662_ = lean_box(0);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 0, v___x_3662_);
v___x_3664_ = v___x_3634_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3662_);
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
lean_dec(v_snd_3630_);
lean_dec(v_fst_3629_);
v_a_3667_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3631_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3631_);
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
else
{
lean_object* v___x_3675_; lean_object* v___x_3677_; 
lean_dec(v_a_3624_);
v___x_3675_ = lean_box(0);
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 0, v___x_3675_);
v___x_3677_ = v___x_3626_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
v_a_3680_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3623_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3623_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVShiftLeft___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_u2081_3610_ = stack[0].m_obj;
lean_object* v_r_u2082_3611_ = stack[1].m_obj;
lean_object* v___y_3612_ = stack[2].m_obj;
lean_object* v___y_3613_ = stack[3].m_obj;
lean_object* v___y_3614_ = stack[4].m_obj;
lean_object* v___y_3615_ = stack[5].m_obj;
lean_object* v___y_3616_ = stack[6].m_obj;
lean_object* v___y_3617_ = stack[7].m_obj;
lean_object* v___y_3618_ = stack[8].m_obj;
lean_object* v___y_3619_ = stack[9].m_obj;
lean_object* v___y_3620_ = stack[10].m_obj;
lean_object* v___y_3621_ = stack[11].m_obj;
lean_object* v_res_3688_;
v_res_3688_ = l_Lean_Meta_Grind_propagateBVShiftLeft___lam__0(v_r_u2081_3610_, v_r_u2082_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
stack->m_obj
 = v_res_3688_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___lam__0___boxed(lean_object* v_r_u2081_3689_, lean_object* v_r_u2082_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l_Lean_Meta_Grind_propagateBVShiftLeft___lam__0(v_r_u2081_3689_, v_r_u2082_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec(v___y_3692_);
lean_dec(v___y_3691_);
lean_dec_ref(v_r_u2082_3690_);
return v_res_3702_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft(lean_object* v_e_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; uint8_t v___x_3722_; 
v___x_3720_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVShiftLeft___closed__1));
v___x_3721_ = lean_unsigned_to_nat(3u);
v___x_3722_ = l_Lean_Expr_isAppOfArity(v_e_3708_, v___x_3720_, v___x_3721_);
if (v___x_3722_ == 0)
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
lean_dec_ref(v_e_3708_);
v___x_3723_ = lean_box(0);
v___x_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
return v___x_3724_;
}
else
{
lean_object* v___f_3725_; lean_object* v___x_3726_; 
v___f_3725_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVShiftLeft___closed__2));
v___x_3726_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3708_, v___f_3725_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_);
return v___x_3726_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVShiftLeft_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3708_ = stack[0].m_obj;
lean_object* v_a_3709_ = stack[1].m_obj;
lean_object* v_a_3710_ = stack[2].m_obj;
lean_object* v_a_3711_ = stack[3].m_obj;
lean_object* v_a_3712_ = stack[4].m_obj;
lean_object* v_a_3713_ = stack[5].m_obj;
lean_object* v_a_3714_ = stack[6].m_obj;
lean_object* v_a_3715_ = stack[7].m_obj;
lean_object* v_a_3716_ = stack[8].m_obj;
lean_object* v_a_3717_ = stack[9].m_obj;
lean_object* v_a_3718_ = stack[10].m_obj;
lean_object* v_res_3727_;
v_res_3727_ = l_Lean_Meta_Grind_propagateBVShiftLeft(v_e_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_);
stack->m_obj
 = v_res_3727_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___boxed(lean_object* v_e_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l_Lean_Meta_Grind_propagateBVShiftLeft(v_e_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_);
lean_dec(v_a_3738_);
lean_dec_ref(v_a_3737_);
lean_dec(v_a_3736_);
lean_dec_ref(v_a_3735_);
lean_dec(v_a_3734_);
lean_dec_ref(v_a_3733_);
lean_dec(v_a_3732_);
lean_dec_ref(v_a_3731_);
lean_dec(v_a_3730_);
lean_dec(v_a_3729_);
return v_res_3740_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3262547096____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3742_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVShiftLeft___closed__1));
v___x_3743_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVShiftLeft___boxed), 12, 0);
v___x_3744_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3742_, v___x_3743_);
return v___x_3744_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3262547096____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3745_;
v_res_3745_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3262547096____hygCtx___hyg_9_();
stack->m_obj
 = v_res_3745_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3262547096____hygCtx___hyg_9____boxed(lean_object* v_a_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3262547096____hygCtx___hyg_9_();
return v_res_3747_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight___lam__0(lean_object* v_r_u2081_3748_, lean_object* v_r_u2082_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v___x_3761_; 
v___x_3761_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3748_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3817_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3764_ = v___x_3761_;
v_isShared_3765_ = v_isSharedCheck_3817_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3761_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3817_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
if (lean_obj_tag(v_a_3762_) == 1)
{
lean_object* v_val_3766_; lean_object* v_fst_3767_; lean_object* v_snd_3768_; lean_object* v___x_3769_; 
lean_del_object(v___x_3764_);
v_val_3766_ = lean_ctor_get(v_a_3762_, 0);
lean_inc(v_val_3766_);
lean_dec_ref_known(v_a_3762_, 1);
v_fst_3767_ = lean_ctor_get(v_val_3766_, 0);
lean_inc(v_fst_3767_);
v_snd_3768_ = lean_ctor_get(v_val_3766_, 1);
lean_inc(v_snd_3768_);
lean_dec(v_val_3766_);
v___x_3769_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_3749_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3804_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3772_ = v___x_3769_;
v_isShared_3773_ = v_isSharedCheck_3804_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3769_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3804_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
if (lean_obj_tag(v_a_3770_) == 1)
{
lean_object* v_val_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3799_; 
lean_del_object(v___x_3772_);
v_val_3774_ = lean_ctor_get(v_a_3770_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v_a_3770_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3776_ = v_a_3770_;
v_isShared_3777_ = v_isSharedCheck_3799_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_val_3774_);
lean_dec(v_a_3770_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3799_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = lean_nat_shiftr(v_snd_3768_, v_val_3774_);
lean_dec(v_val_3774_);
lean_dec(v_snd_3768_);
v___x_3779_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3767_, v___x_3778_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3790_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3782_ = v___x_3779_;
v_isShared_3783_ = v_isSharedCheck_3790_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3779_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3790_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3777_ == 0)
{
lean_ctor_set(v___x_3776_, 0, v_a_3780_);
v___x_3785_ = v___x_3776_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
lean_object* v___x_3787_; 
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 0, v___x_3785_);
v___x_3787_ = v___x_3782_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3785_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
lean_del_object(v___x_3776_);
v_a_3791_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3779_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3779_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
}
else
{
lean_object* v___x_3800_; lean_object* v___x_3802_; 
lean_dec(v_a_3770_);
lean_dec(v_snd_3768_);
lean_dec(v_fst_3767_);
v___x_3800_ = lean_box(0);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 0, v___x_3800_);
v___x_3802_ = v___x_3772_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3800_);
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
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
lean_dec(v_snd_3768_);
lean_dec(v_fst_3767_);
v_a_3805_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3807_ = v___x_3769_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3769_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
else
{
lean_object* v___x_3813_; lean_object* v___x_3815_; 
lean_dec(v_a_3762_);
v___x_3813_ = lean_box(0);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 0, v___x_3813_);
v___x_3815_ = v___x_3764_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3813_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
v_a_3818_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3761_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3761_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVUShiftRight___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_u2081_3748_ = stack[0].m_obj;
lean_object* v_r_u2082_3749_ = stack[1].m_obj;
lean_object* v___y_3750_ = stack[2].m_obj;
lean_object* v___y_3751_ = stack[3].m_obj;
lean_object* v___y_3752_ = stack[4].m_obj;
lean_object* v___y_3753_ = stack[5].m_obj;
lean_object* v___y_3754_ = stack[6].m_obj;
lean_object* v___y_3755_ = stack[7].m_obj;
lean_object* v___y_3756_ = stack[8].m_obj;
lean_object* v___y_3757_ = stack[9].m_obj;
lean_object* v___y_3758_ = stack[10].m_obj;
lean_object* v___y_3759_ = stack[11].m_obj;
lean_object* v_res_3826_;
v_res_3826_ = l_Lean_Meta_Grind_propagateBVUShiftRight___lam__0(v_r_u2081_3748_, v_r_u2082_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
stack->m_obj
 = v_res_3826_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight___lam__0___boxed(lean_object* v_r_u2081_3827_, lean_object* v_r_u2082_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Lean_Meta_Grind_propagateBVUShiftRight___lam__0(v_r_u2081_3827_, v_r_u2082_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v_r_u2082_3828_);
return v_res_3840_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight(lean_object* v_e_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_){
_start:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; uint8_t v___x_3860_; 
v___x_3858_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVUShiftRight___closed__1));
v___x_3859_ = lean_unsigned_to_nat(3u);
v___x_3860_ = l_Lean_Expr_isAppOfArity(v_e_3846_, v___x_3858_, v___x_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
lean_dec_ref(v_e_3846_);
v___x_3861_ = lean_box(0);
v___x_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
return v___x_3862_;
}
else
{
lean_object* v___f_3863_; lean_object* v___x_3864_; 
v___f_3863_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVUShiftRight___closed__2));
v___x_3864_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3846_, v___f_3863_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_);
return v___x_3864_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVUShiftRight_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3846_ = stack[0].m_obj;
lean_object* v_a_3847_ = stack[1].m_obj;
lean_object* v_a_3848_ = stack[2].m_obj;
lean_object* v_a_3849_ = stack[3].m_obj;
lean_object* v_a_3850_ = stack[4].m_obj;
lean_object* v_a_3851_ = stack[5].m_obj;
lean_object* v_a_3852_ = stack[6].m_obj;
lean_object* v_a_3853_ = stack[7].m_obj;
lean_object* v_a_3854_ = stack[8].m_obj;
lean_object* v_a_3855_ = stack[9].m_obj;
lean_object* v_a_3856_ = stack[10].m_obj;
lean_object* v_res_3865_;
v_res_3865_ = l_Lean_Meta_Grind_propagateBVUShiftRight(v_e_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_);
stack->m_obj
 = v_res_3865_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight___boxed(lean_object* v_e_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Lean_Meta_Grind_propagateBVUShiftRight(v_e_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_);
lean_dec(v_a_3876_);
lean_dec_ref(v_a_3875_);
lean_dec(v_a_3874_);
lean_dec_ref(v_a_3873_);
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec(v_a_3868_);
lean_dec(v_a_3867_);
return v_res_3878_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVUShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVUShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1878785357____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3880_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVUShiftRight___closed__1));
v___x_3881_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVUShiftRight___boxed), 12, 0);
v___x_3882_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3880_, v___x_3881_);
return v___x_3882_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVUShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVUShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1878785357____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3883_;
v_res_3883_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVUShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVUShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1878785357____hygCtx___hyg_9_();
stack->m_obj
 = v_res_3883_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVUShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVUShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1878785357____hygCtx___hyg_9____boxed(lean_object* v_a_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVUShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVUShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1878785357____hygCtx___hyg_9_();
return v_res_3885_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight___lam__0(lean_object* v_r_u2081_3886_, lean_object* v_r_u2082_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3886_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3955_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3902_ = v___x_3899_;
v_isShared_3903_ = v_isSharedCheck_3955_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3899_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3955_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
if (lean_obj_tag(v_a_3900_) == 1)
{
lean_object* v_val_3904_; lean_object* v_fst_3905_; lean_object* v_snd_3906_; lean_object* v___x_3907_; 
lean_del_object(v___x_3902_);
v_val_3904_ = lean_ctor_get(v_a_3900_, 0);
lean_inc(v_val_3904_);
lean_dec_ref_known(v_a_3900_, 1);
v_fst_3905_ = lean_ctor_get(v_val_3904_, 0);
lean_inc(v_fst_3905_);
v_snd_3906_ = lean_ctor_get(v_val_3904_, 1);
lean_inc(v_snd_3906_);
lean_dec(v_val_3904_);
v___x_3907_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_3887_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3942_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3910_ = v___x_3907_;
v_isShared_3911_ = v_isSharedCheck_3942_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3907_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3942_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
if (lean_obj_tag(v_a_3908_) == 1)
{
lean_object* v_val_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3937_; 
lean_del_object(v___x_3910_);
v_val_3912_ = lean_ctor_get(v_a_3908_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_a_3908_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3914_ = v_a_3908_;
v_isShared_3915_ = v_isSharedCheck_3937_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_val_3912_);
lean_dec(v_a_3908_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3937_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3916_ = l_BitVec_sshiftRight(v_fst_3905_, v_snd_3906_, v_val_3912_);
lean_dec(v_val_3912_);
v___x_3917_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3905_, v___x_3916_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3928_; 
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3920_ = v___x_3917_;
v_isShared_3921_ = v_isSharedCheck_3928_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3917_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3928_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 0, v_a_3918_);
v___x_3923_ = v___x_3914_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
lean_object* v___x_3925_; 
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 0, v___x_3923_);
v___x_3925_ = v___x_3920_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3923_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
lean_del_object(v___x_3914_);
v_a_3929_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3917_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3917_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
}
else
{
lean_object* v___x_3938_; lean_object* v___x_3940_; 
lean_dec(v_a_3908_);
lean_dec(v_snd_3906_);
lean_dec(v_fst_3905_);
v___x_3938_ = lean_box(0);
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 0, v___x_3938_);
v___x_3940_ = v___x_3910_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3938_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
lean_dec(v_snd_3906_);
lean_dec(v_fst_3905_);
v_a_3943_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3907_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3907_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
else
{
lean_object* v___x_3951_; lean_object* v___x_3953_; 
lean_dec(v_a_3900_);
v___x_3951_ = lean_box(0);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 0, v___x_3951_);
v___x_3953_ = v___x_3902_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3951_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
v_a_3956_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3899_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3899_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVSShiftRight___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_u2081_3886_ = stack[0].m_obj;
lean_object* v_r_u2082_3887_ = stack[1].m_obj;
lean_object* v___y_3888_ = stack[2].m_obj;
lean_object* v___y_3889_ = stack[3].m_obj;
lean_object* v___y_3890_ = stack[4].m_obj;
lean_object* v___y_3891_ = stack[5].m_obj;
lean_object* v___y_3892_ = stack[6].m_obj;
lean_object* v___y_3893_ = stack[7].m_obj;
lean_object* v___y_3894_ = stack[8].m_obj;
lean_object* v___y_3895_ = stack[9].m_obj;
lean_object* v___y_3896_ = stack[10].m_obj;
lean_object* v___y_3897_ = stack[11].m_obj;
lean_object* v_res_3964_;
v_res_3964_ = l_Lean_Meta_Grind_propagateBVSShiftRight___lam__0(v_r_u2081_3886_, v_r_u2082_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
stack->m_obj
 = v_res_3964_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight___lam__0___boxed(lean_object* v_r_u2081_3965_, lean_object* v_r_u2082_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l_Lean_Meta_Grind_propagateBVSShiftRight___lam__0(v_r_u2081_3965_, v_r_u2082_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec(v___y_3967_);
lean_dec_ref(v_r_u2082_3966_);
return v_res_3978_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight(lean_object* v_e_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_){
_start:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; uint8_t v___x_3998_; 
v___x_3996_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSShiftRight___closed__1));
v___x_3997_ = lean_unsigned_to_nat(3u);
v___x_3998_ = l_Lean_Expr_isAppOfArity(v_e_3984_, v___x_3996_, v___x_3997_);
if (v___x_3998_ == 0)
{
lean_object* v___x_3999_; lean_object* v___x_4000_; 
lean_dec_ref(v_e_3984_);
v___x_3999_ = lean_box(0);
v___x_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
return v___x_4000_;
}
else
{
lean_object* v___f_4001_; lean_object* v___x_4002_; 
v___f_4001_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSShiftRight___closed__2));
v___x_4002_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3984_, v___f_4001_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_);
return v___x_4002_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVSShiftRight_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3984_ = stack[0].m_obj;
lean_object* v_a_3985_ = stack[1].m_obj;
lean_object* v_a_3986_ = stack[2].m_obj;
lean_object* v_a_3987_ = stack[3].m_obj;
lean_object* v_a_3988_ = stack[4].m_obj;
lean_object* v_a_3989_ = stack[5].m_obj;
lean_object* v_a_3990_ = stack[6].m_obj;
lean_object* v_a_3991_ = stack[7].m_obj;
lean_object* v_a_3992_ = stack[8].m_obj;
lean_object* v_a_3993_ = stack[9].m_obj;
lean_object* v_a_3994_ = stack[10].m_obj;
lean_object* v_res_4003_;
v_res_4003_ = l_Lean_Meta_Grind_propagateBVSShiftRight(v_e_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_);
stack->m_obj
 = v_res_4003_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight___boxed(lean_object* v_e_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_Lean_Meta_Grind_propagateBVSShiftRight(v_e_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_);
lean_dec(v_a_4014_);
lean_dec_ref(v_a_4013_);
lean_dec(v_a_4012_);
lean_dec_ref(v_a_4011_);
lean_dec(v_a_4010_);
lean_dec_ref(v_a_4009_);
lean_dec(v_a_4008_);
lean_dec_ref(v_a_4007_);
lean_dec(v_a_4006_);
lean_dec(v_a_4005_);
return v_res_4016_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVSShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3342532823____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4018_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSShiftRight___closed__1));
v___x_4019_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVSShiftRight___boxed), 12, 0);
v___x_4020_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4018_, v___x_4019_);
return v___x_4020_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVSShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3342532823____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4021_;
v_res_4021_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVSShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3342532823____hygCtx___hyg_9_();
stack->m_obj
 = v_res_4021_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVSShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3342532823____hygCtx___hyg_9____boxed(lean_object* v_a_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVSShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3342532823____hygCtx___hyg_9_();
return v_res_4023_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft___lam__0(lean_object* v_r_u2081_4024_, lean_object* v_r_u2082_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v___x_4037_; 
v___x_4037_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4024_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4093_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4040_ = v___x_4037_;
v_isShared_4041_ = v_isSharedCheck_4093_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4037_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4093_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
if (lean_obj_tag(v_a_4038_) == 1)
{
lean_object* v_val_4042_; lean_object* v_fst_4043_; lean_object* v_snd_4044_; lean_object* v___x_4045_; 
lean_del_object(v___x_4040_);
v_val_4042_ = lean_ctor_get(v_a_4038_, 0);
lean_inc(v_val_4042_);
lean_dec_ref_known(v_a_4038_, 1);
v_fst_4043_ = lean_ctor_get(v_val_4042_, 0);
lean_inc(v_fst_4043_);
v_snd_4044_ = lean_ctor_get(v_val_4042_, 1);
lean_inc(v_snd_4044_);
lean_dec(v_val_4042_);
v___x_4045_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4025_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
if (lean_obj_tag(v___x_4045_) == 0)
{
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4080_; 
v_a_4046_ = lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4048_ = v___x_4045_;
v_isShared_4049_ = v_isSharedCheck_4080_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v___x_4045_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4080_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
if (lean_obj_tag(v_a_4046_) == 1)
{
lean_object* v_val_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4075_; 
lean_del_object(v___x_4048_);
v_val_4050_ = lean_ctor_get(v_a_4046_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v_a_4046_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4052_ = v_a_4046_;
v_isShared_4053_ = v_isSharedCheck_4075_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_val_4050_);
lean_dec(v_a_4046_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4075_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = l_BitVec_rotateLeft(v_fst_4043_, v_snd_4044_, v_val_4050_);
lean_dec(v_val_4050_);
lean_dec(v_snd_4044_);
v___x_4055_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4043_, v___x_4054_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4066_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4058_ = v___x_4055_;
v_isShared_4059_ = v_isSharedCheck_4066_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_4055_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4066_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v_a_4056_);
v___x_4061_ = v___x_4052_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4056_);
v___x_4061_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
lean_object* v___x_4063_; 
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 0, v___x_4061_);
v___x_4063_ = v___x_4058_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4061_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
else
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
lean_del_object(v___x_4052_);
v_a_4067_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4055_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4055_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4067_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
}
}
else
{
lean_object* v___x_4076_; lean_object* v___x_4078_; 
lean_dec(v_a_4046_);
lean_dec(v_snd_4044_);
lean_dec(v_fst_4043_);
v___x_4076_ = lean_box(0);
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 0, v___x_4076_);
v___x_4078_ = v___x_4048_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v___x_4076_);
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
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec(v_snd_4044_);
lean_dec(v_fst_4043_);
v_a_4081_ = lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4045_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4045_);
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
else
{
lean_object* v___x_4089_; lean_object* v___x_4091_; 
lean_dec(v_a_4038_);
v___x_4089_ = lean_box(0);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 0, v___x_4089_);
v___x_4091_ = v___x_4040_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_4089_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
else
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4101_; 
v_a_4094_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4096_ = v___x_4037_;
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4037_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4099_; 
if (v_isShared_4097_ == 0)
{
v___x_4099_ = v___x_4096_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_a_4094_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVRotateLeft___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_u2081_4024_ = stack[0].m_obj;
lean_object* v_r_u2082_4025_ = stack[1].m_obj;
lean_object* v___y_4026_ = stack[2].m_obj;
lean_object* v___y_4027_ = stack[3].m_obj;
lean_object* v___y_4028_ = stack[4].m_obj;
lean_object* v___y_4029_ = stack[5].m_obj;
lean_object* v___y_4030_ = stack[6].m_obj;
lean_object* v___y_4031_ = stack[7].m_obj;
lean_object* v___y_4032_ = stack[8].m_obj;
lean_object* v___y_4033_ = stack[9].m_obj;
lean_object* v___y_4034_ = stack[10].m_obj;
lean_object* v___y_4035_ = stack[11].m_obj;
lean_object* v_res_4102_;
v_res_4102_ = l_Lean_Meta_Grind_propagateBVRotateLeft___lam__0(v_r_u2081_4024_, v_r_u2082_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
stack->m_obj
 = v_res_4102_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft___lam__0___boxed(lean_object* v_r_u2081_4103_, lean_object* v_r_u2082_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Lean_Meta_Grind_propagateBVRotateLeft___lam__0(v_r_u2081_4103_, v_r_u2082_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec(v___y_4105_);
lean_dec_ref(v_r_u2082_4104_);
return v_res_4116_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft(lean_object* v_e_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_){
_start:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; uint8_t v___x_4136_; 
v___x_4134_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateLeft___closed__1));
v___x_4135_ = lean_unsigned_to_nat(3u);
v___x_4136_ = l_Lean_Expr_isAppOfArity(v_e_4122_, v___x_4134_, v___x_4135_);
if (v___x_4136_ == 0)
{
lean_object* v___x_4137_; lean_object* v___x_4138_; 
lean_dec_ref(v_e_4122_);
v___x_4137_ = lean_box(0);
v___x_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4137_);
return v___x_4138_;
}
else
{
lean_object* v___f_4139_; lean_object* v___x_4140_; 
v___f_4139_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateLeft___closed__2));
v___x_4140_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4122_, v___f_4139_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
return v___x_4140_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVRotateLeft_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4122_ = stack[0].m_obj;
lean_object* v_a_4123_ = stack[1].m_obj;
lean_object* v_a_4124_ = stack[2].m_obj;
lean_object* v_a_4125_ = stack[3].m_obj;
lean_object* v_a_4126_ = stack[4].m_obj;
lean_object* v_a_4127_ = stack[5].m_obj;
lean_object* v_a_4128_ = stack[6].m_obj;
lean_object* v_a_4129_ = stack[7].m_obj;
lean_object* v_a_4130_ = stack[8].m_obj;
lean_object* v_a_4131_ = stack[9].m_obj;
lean_object* v_a_4132_ = stack[10].m_obj;
lean_object* v_res_4141_;
v_res_4141_ = l_Lean_Meta_Grind_propagateBVRotateLeft(v_e_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
stack->m_obj
 = v_res_4141_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft___boxed(lean_object* v_e_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l_Lean_Meta_Grind_propagateBVRotateLeft(v_e_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
lean_dec(v_a_4152_);
lean_dec_ref(v_a_4151_);
lean_dec(v_a_4150_);
lean_dec_ref(v_a_4149_);
lean_dec(v_a_4148_);
lean_dec_ref(v_a_4147_);
lean_dec(v_a_4146_);
lean_dec_ref(v_a_4145_);
lean_dec(v_a_4144_);
lean_dec(v_a_4143_);
return v_res_4154_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateLeft___regBuiltin_Lean_Meta_Grind_propagateBVRotateLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1541346404____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4156_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateLeft___closed__1));
v___x_4157_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVRotateLeft___boxed), 12, 0);
v___x_4158_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4156_, v___x_4157_);
return v___x_4158_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateLeft___regBuiltin_Lean_Meta_Grind_propagateBVRotateLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1541346404____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4159_;
v_res_4159_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateLeft___regBuiltin_Lean_Meta_Grind_propagateBVRotateLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1541346404____hygCtx___hyg_9_();
stack->m_obj
 = v_res_4159_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateLeft___regBuiltin_Lean_Meta_Grind_propagateBVRotateLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1541346404____hygCtx___hyg_9____boxed(lean_object* v_a_4160_){
_start:
{
lean_object* v_res_4161_; 
v_res_4161_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateLeft___regBuiltin_Lean_Meta_Grind_propagateBVRotateLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1541346404____hygCtx___hyg_9_();
return v_res_4161_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVRotateRight___lam__0(lean_object* v_r_u2081_4162_, lean_object* v_r_u2082_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v___x_4175_; 
v___x_4175_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4162_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4231_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4178_ = v___x_4175_;
v_isShared_4179_ = v_isSharedCheck_4231_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4175_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4231_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
if (lean_obj_tag(v_a_4176_) == 1)
{
lean_object* v_val_4180_; lean_object* v_fst_4181_; lean_object* v_snd_4182_; lean_object* v___x_4183_; 
lean_del_object(v___x_4178_);
v_val_4180_ = lean_ctor_get(v_a_4176_, 0);
lean_inc(v_val_4180_);
lean_dec_ref_known(v_a_4176_, 1);
v_fst_4181_ = lean_ctor_get(v_val_4180_, 0);
lean_inc(v_fst_4181_);
v_snd_4182_ = lean_ctor_get(v_val_4180_, 1);
lean_inc(v_snd_4182_);
lean_dec(v_val_4180_);
v___x_4183_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4163_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4218_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4186_ = v___x_4183_;
v_isShared_4187_ = v_isSharedCheck_4218_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4183_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4218_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
if (lean_obj_tag(v_a_4184_) == 1)
{
lean_object* v_val_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4213_; 
lean_del_object(v___x_4186_);
v_val_4188_ = lean_ctor_get(v_a_4184_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v_a_4184_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4190_ = v_a_4184_;
v_isShared_4191_ = v_isSharedCheck_4213_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_val_4188_);
lean_dec(v_a_4184_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4213_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4192_ = l_BitVec_rotateRight(v_fst_4181_, v_snd_4182_, v_val_4188_);
lean_dec(v_val_4188_);
lean_dec(v_snd_4182_);
v___x_4193_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4181_, v___x_4192_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4204_; 
v_a_4194_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4196_ = v___x_4193_;
v_isShared_4197_ = v_isSharedCheck_4204_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4193_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4204_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4191_ == 0)
{
lean_ctor_set(v___x_4190_, 0, v_a_4194_);
v___x_4199_ = v___x_4190_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4194_);
v___x_4199_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
lean_object* v___x_4201_; 
if (v_isShared_4197_ == 0)
{
lean_ctor_set(v___x_4196_, 0, v___x_4199_);
v___x_4201_ = v___x_4196_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v___x_4199_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
return v___x_4201_;
}
}
}
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
lean_del_object(v___x_4190_);
v_a_4205_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4193_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4193_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
}
}
else
{
lean_object* v___x_4214_; lean_object* v___x_4216_; 
lean_dec(v_a_4184_);
lean_dec(v_snd_4182_);
lean_dec(v_fst_4181_);
v___x_4214_ = lean_box(0);
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 0, v___x_4214_);
v___x_4216_ = v___x_4186_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4214_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
else
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
lean_dec(v_snd_4182_);
lean_dec(v_fst_4181_);
v_a_4219_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4221_ = v___x_4183_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4183_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
else
{
lean_object* v___x_4227_; lean_object* v___x_4229_; 
lean_dec(v_a_4176_);
v___x_4227_ = lean_box(0);
if (v_isShared_4179_ == 0)
{
lean_ctor_set(v___x_4178_, 0, v___x_4227_);
v___x_4229_ = v___x_4178_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4227_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
else
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4239_; 
v_a_4232_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4234_ = v___x_4175_;
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___x_4175_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4237_; 
if (v_isShared_4235_ == 0)
{
v___x_4237_ = v___x_4234_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_a_4232_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVRotateRight___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_u2081_4162_ = stack[0].m_obj;
lean_object* v_r_u2082_4163_ = stack[1].m_obj;
lean_object* v___y_4164_ = stack[2].m_obj;
lean_object* v___y_4165_ = stack[3].m_obj;
lean_object* v___y_4166_ = stack[4].m_obj;
lean_object* v___y_4167_ = stack[5].m_obj;
lean_object* v___y_4168_ = stack[6].m_obj;
lean_object* v___y_4169_ = stack[7].m_obj;
lean_object* v___y_4170_ = stack[8].m_obj;
lean_object* v___y_4171_ = stack[9].m_obj;
lean_object* v___y_4172_ = stack[10].m_obj;
lean_object* v___y_4173_ = stack[11].m_obj;
lean_object* v_res_4240_;
v_res_4240_ = l_Lean_Meta_Grind_propagateBVRotateRight___lam__0(v_r_u2081_4162_, v_r_u2082_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
stack->m_obj
 = v_res_4240_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateRight___lam__0___boxed(lean_object* v_r_u2081_4241_, lean_object* v_r_u2082_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Lean_Meta_Grind_propagateBVRotateRight___lam__0(v_r_u2081_4241_, v_r_u2082_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4251_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4247_);
lean_dec(v___y_4246_);
lean_dec_ref(v___y_4245_);
lean_dec(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v_r_u2082_4242_);
return v_res_4254_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVRotateRight(lean_object* v_e_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_){
_start:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; uint8_t v___x_4274_; 
v___x_4272_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateRight___closed__1));
v___x_4273_ = lean_unsigned_to_nat(3u);
v___x_4274_ = l_Lean_Expr_isAppOfArity(v_e_4260_, v___x_4272_, v___x_4273_);
if (v___x_4274_ == 0)
{
lean_object* v___x_4275_; lean_object* v___x_4276_; 
lean_dec_ref(v_e_4260_);
v___x_4275_ = lean_box(0);
v___x_4276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4275_);
return v___x_4276_;
}
else
{
lean_object* v___f_4277_; lean_object* v___x_4278_; 
v___f_4277_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateRight___closed__2));
v___x_4278_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4260_, v___f_4277_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_);
return v___x_4278_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVRotateRight_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4260_ = stack[0].m_obj;
lean_object* v_a_4261_ = stack[1].m_obj;
lean_object* v_a_4262_ = stack[2].m_obj;
lean_object* v_a_4263_ = stack[3].m_obj;
lean_object* v_a_4264_ = stack[4].m_obj;
lean_object* v_a_4265_ = stack[5].m_obj;
lean_object* v_a_4266_ = stack[6].m_obj;
lean_object* v_a_4267_ = stack[7].m_obj;
lean_object* v_a_4268_ = stack[8].m_obj;
lean_object* v_a_4269_ = stack[9].m_obj;
lean_object* v_a_4270_ = stack[10].m_obj;
lean_object* v_res_4279_;
v_res_4279_ = l_Lean_Meta_Grind_propagateBVRotateRight(v_e_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_);
stack->m_obj
 = v_res_4279_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateRight___boxed(lean_object* v_e_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_Meta_Grind_propagateBVRotateRight(v_e_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_);
lean_dec(v_a_4290_);
lean_dec_ref(v_a_4289_);
lean_dec(v_a_4288_);
lean_dec_ref(v_a_4287_);
lean_dec(v_a_4286_);
lean_dec_ref(v_a_4285_);
lean_dec(v_a_4284_);
lean_dec_ref(v_a_4283_);
lean_dec(v_a_4282_);
lean_dec(v_a_4281_);
return v_res_4292_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateRight___regBuiltin_Lean_Meta_Grind_propagateBVRotateRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2456321972____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4294_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateRight___closed__1));
v___x_4295_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVRotateRight___boxed), 12, 0);
v___x_4296_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4294_, v___x_4295_);
return v___x_4296_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateRight___regBuiltin_Lean_Meta_Grind_propagateBVRotateRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2456321972____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4297_;
v_res_4297_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateRight___regBuiltin_Lean_Meta_Grind_propagateBVRotateRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2456321972____hygCtx___hyg_9_();
stack->m_obj
 = v_res_4297_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateRight___regBuiltin_Lean_Meta_Grind_propagateBVRotateRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2456321972____hygCtx___hyg_9____boxed(lean_object* v_a_4298_){
_start:
{
lean_object* v_res_4299_; 
v_res_4299_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateRight___regBuiltin_Lean_Meta_Grind_propagateBVRotateRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2456321972____hygCtx___hyg_9_();
return v_res_4299_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0(lean_object* v_op_4300_, lean_object* v_r_u2081_4301_, lean_object* v_r_u2082_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v___x_4314_; 
v___x_4314_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4301_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4407_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4317_ = v___x_4314_;
v_isShared_4318_ = v_isSharedCheck_4407_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4314_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4407_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
if (lean_obj_tag(v_a_4315_) == 1)
{
lean_object* v_val_4319_; lean_object* v_fst_4320_; lean_object* v_snd_4321_; lean_object* v___x_4322_; 
lean_del_object(v___x_4317_);
v_val_4319_ = lean_ctor_get(v_a_4315_, 0);
lean_inc(v_val_4319_);
lean_dec_ref_known(v_a_4315_, 1);
v_fst_4320_ = lean_ctor_get(v_val_4319_, 0);
lean_inc(v_fst_4320_);
v_snd_4321_ = lean_ctor_get(v_val_4319_, 1);
lean_inc(v_snd_4321_);
lean_dec(v_val_4319_);
v___x_4322_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4302_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
lean_inc(v_a_4323_);
lean_dec_ref_known(v___x_4322_, 1);
if (lean_obj_tag(v_a_4323_) == 1)
{
lean_object* v_val_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4349_; 
lean_dec_ref(v_r_u2082_4302_);
v_val_4324_ = lean_ctor_get(v_a_4323_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v_a_4323_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4326_ = v_a_4323_;
v_isShared_4327_ = v_isSharedCheck_4349_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_val_4324_);
lean_dec(v_a_4323_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4349_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; 
lean_inc(v_fst_4320_);
v___x_4328_ = lean_apply_3(v_op_4300_, v_fst_4320_, v_snd_4321_, v_val_4324_);
v___x_4329_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4320_, v___x_4328_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
if (lean_obj_tag(v___x_4329_) == 0)
{
lean_object* v_a_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4340_; 
v_a_4330_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4332_ = v___x_4329_;
v_isShared_4333_ = v_isSharedCheck_4340_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_a_4330_);
lean_dec(v___x_4329_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4340_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v___x_4335_; 
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 0, v_a_4330_);
v___x_4335_ = v___x_4326_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_a_4330_);
v___x_4335_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
lean_object* v___x_4337_; 
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 0, v___x_4335_);
v___x_4337_ = v___x_4332_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v___x_4335_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
}
}
else
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4348_; 
lean_del_object(v___x_4326_);
v_a_4341_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4343_ = v___x_4329_;
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v___x_4329_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4346_; 
if (v_isShared_4344_ == 0)
{
v___x_4346_ = v___x_4343_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4341_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
}
}
}
}
}
else
{
lean_object* v___x_4350_; 
lean_dec(v_a_4323_);
v___x_4350_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_4302_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4386_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4353_ = v___x_4350_;
v_isShared_4354_ = v_isSharedCheck_4386_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4350_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4386_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
if (lean_obj_tag(v_a_4351_) == 1)
{
lean_object* v_val_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4381_; 
lean_del_object(v___x_4353_);
v_val_4355_ = lean_ctor_get(v_a_4351_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v_a_4351_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4357_ = v_a_4351_;
v_isShared_4358_ = v_isSharedCheck_4381_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_val_4355_);
lean_dec(v_a_4351_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4381_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v_snd_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
v_snd_4359_ = lean_ctor_get(v_val_4355_, 1);
lean_inc(v_snd_4359_);
lean_dec(v_val_4355_);
lean_inc(v_fst_4320_);
v___x_4360_ = lean_apply_3(v_op_4300_, v_fst_4320_, v_snd_4321_, v_snd_4359_);
v___x_4361_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4320_, v___x_4360_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4372_; 
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4364_ = v___x_4361_;
v_isShared_4365_ = v_isSharedCheck_4372_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v___x_4361_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4372_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4367_; 
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 0, v_a_4362_);
v___x_4367_ = v___x_4357_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4362_);
v___x_4367_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
lean_object* v___x_4369_; 
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 0, v___x_4367_);
v___x_4369_ = v___x_4364_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4367_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_del_object(v___x_4357_);
v_a_4373_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4361_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4361_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
}
else
{
lean_object* v___x_4382_; lean_object* v___x_4384_; 
lean_dec(v_a_4351_);
lean_dec(v_snd_4321_);
lean_dec(v_fst_4320_);
lean_dec_ref(v_op_4300_);
v___x_4382_ = lean_box(0);
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 0, v___x_4382_);
v___x_4384_ = v___x_4353_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4382_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
else
{
lean_object* v_a_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4394_; 
lean_dec(v_snd_4321_);
lean_dec(v_fst_4320_);
lean_dec_ref(v_op_4300_);
v_a_4387_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4389_ = v___x_4350_;
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_a_4387_);
lean_dec(v___x_4350_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4392_; 
if (v_isShared_4390_ == 0)
{
v___x_4392_ = v___x_4389_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_a_4387_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
}
}
}
else
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4402_; 
lean_dec(v_snd_4321_);
lean_dec(v_fst_4320_);
lean_dec_ref(v_r_u2082_4302_);
lean_dec_ref(v_op_4300_);
v_a_4395_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4397_ = v___x_4322_;
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4322_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4400_; 
if (v_isShared_4398_ == 0)
{
v___x_4400_ = v___x_4397_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_a_4395_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
}
else
{
lean_object* v___x_4403_; lean_object* v___x_4405_; 
lean_dec(v_a_4315_);
lean_dec_ref(v_r_u2082_4302_);
lean_dec_ref(v_op_4300_);
v___x_4403_ = lean_box(0);
if (v_isShared_4318_ == 0)
{
lean_ctor_set(v___x_4317_, 0, v___x_4403_);
v___x_4405_ = v___x_4317_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v___x_4403_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
else
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4415_; 
lean_dec_ref(v_r_u2082_4302_);
lean_dec_ref(v_op_4300_);
v_a_4408_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4410_ = v___x_4314_;
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4314_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4413_; 
if (v_isShared_4411_ == 0)
{
v___x_4413_ = v___x_4410_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4408_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
return v___x_4413_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_4300_ = stack[0].m_obj;
lean_object* v_r_u2081_4301_ = stack[1].m_obj;
lean_object* v_r_u2082_4302_ = stack[2].m_obj;
lean_object* v___y_4303_ = stack[3].m_obj;
lean_object* v___y_4304_ = stack[4].m_obj;
lean_object* v___y_4305_ = stack[5].m_obj;
lean_object* v___y_4306_ = stack[6].m_obj;
lean_object* v___y_4307_ = stack[7].m_obj;
lean_object* v___y_4308_ = stack[8].m_obj;
lean_object* v___y_4309_ = stack[9].m_obj;
lean_object* v___y_4310_ = stack[10].m_obj;
lean_object* v___y_4311_ = stack[11].m_obj;
lean_object* v___y_4312_ = stack[12].m_obj;
lean_object* v_res_4416_;
v_res_4416_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0(v_op_4300_, v_r_u2081_4301_, v_r_u2082_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
stack->m_obj
 = v_res_4416_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0___boxed(lean_object* v_op_4417_, lean_object* v_r_u2081_4418_, lean_object* v_r_u2082_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
lean_object* v_res_4431_; 
v_res_4431_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0(v_op_4417_, v_r_u2081_4418_, v_r_u2082_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
lean_dec(v___y_4421_);
lean_dec(v___y_4420_);
return v_res_4431_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV(lean_object* v_declName_4432_, lean_object* v_op_4433_, lean_object* v_e_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_){
_start:
{
lean_object* v___x_4446_; uint8_t v___x_4447_; 
v___x_4446_ = lean_unsigned_to_nat(6u);
v___x_4447_ = l_Lean_Expr_isAppOfArity(v_e_4434_, v_declName_4432_, v___x_4446_);
if (v___x_4447_ == 0)
{
lean_object* v___x_4448_; lean_object* v___x_4449_; 
lean_dec_ref(v_e_4434_);
lean_dec_ref(v_op_4433_);
v___x_4448_ = lean_box(0);
v___x_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4448_);
return v___x_4449_;
}
else
{
lean_object* v___f_4450_; lean_object* v___x_4451_; 
v___f_4450_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0___boxed), 14, 1);
lean_closure_set(v___f_4450_, 0, v_op_4433_);
v___x_4451_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4434_, v___f_4450_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
return v___x_4451_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_4432_ = stack[0].m_obj;
lean_object* v_op_4433_ = stack[1].m_obj;
lean_object* v_e_4434_ = stack[2].m_obj;
lean_object* v_a_4435_ = stack[3].m_obj;
lean_object* v_a_4436_ = stack[4].m_obj;
lean_object* v_a_4437_ = stack[5].m_obj;
lean_object* v_a_4438_ = stack[6].m_obj;
lean_object* v_a_4439_ = stack[7].m_obj;
lean_object* v_a_4440_ = stack[8].m_obj;
lean_object* v_a_4441_ = stack[9].m_obj;
lean_object* v_a_4442_ = stack[10].m_obj;
lean_object* v_a_4443_ = stack[11].m_obj;
lean_object* v_a_4444_ = stack[12].m_obj;
lean_object* v_res_4452_;
v_res_4452_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV(v_declName_4432_, v_op_4433_, v_e_4434_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
stack->m_obj
 = v_res_4452_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___boxed(lean_object* v_declName_4453_, lean_object* v_op_4454_, lean_object* v_e_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_){
_start:
{
lean_object* v_res_4467_; 
v_res_4467_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV(v_declName_4453_, v_op_4454_, v_e_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_, v_a_4465_);
lean_dec(v_a_4465_);
lean_dec_ref(v_a_4464_);
lean_dec(v_a_4463_);
lean_dec_ref(v_a_4462_);
lean_dec(v_a_4461_);
lean_dec_ref(v_a_4460_);
lean_dec(v_a_4459_);
lean_dec_ref(v_a_4458_);
lean_dec(v_a_4457_);
lean_dec(v_a_4456_);
lean_dec(v_declName_4453_);
return v_res_4467_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___lam__0(lean_object* v_r_u2081_4468_, lean_object* v_r_u2082_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_){
_start:
{
lean_object* v___x_4481_; 
v___x_4481_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4468_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4574_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4484_ = v___x_4481_;
v_isShared_4485_ = v_isSharedCheck_4574_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_4481_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4574_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
if (lean_obj_tag(v_a_4482_) == 1)
{
lean_object* v_val_4486_; lean_object* v_fst_4487_; lean_object* v_snd_4488_; lean_object* v___x_4489_; 
lean_del_object(v___x_4484_);
v_val_4486_ = lean_ctor_get(v_a_4482_, 0);
lean_inc(v_val_4486_);
lean_dec_ref_known(v_a_4482_, 1);
v_fst_4487_ = lean_ctor_get(v_val_4486_, 0);
lean_inc(v_fst_4487_);
v_snd_4488_ = lean_ctor_get(v_val_4486_, 1);
lean_inc(v_snd_4488_);
lean_dec(v_val_4486_);
v___x_4489_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4469_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_a_4490_);
lean_dec_ref_known(v___x_4489_, 1);
if (lean_obj_tag(v_a_4490_) == 1)
{
lean_object* v_val_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4516_; 
lean_dec_ref(v_r_u2082_4469_);
v_val_4491_ = lean_ctor_get(v_a_4490_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v_a_4490_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4493_ = v_a_4490_;
v_isShared_4494_ = v_isSharedCheck_4516_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_val_4491_);
lean_dec(v_a_4490_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4516_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4495_ = l_BitVec_shiftLeft(v_fst_4487_, v_snd_4488_, v_val_4491_);
lean_dec(v_val_4491_);
lean_dec(v_snd_4488_);
v___x_4496_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4487_, v___x_4495_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
if (lean_obj_tag(v___x_4496_) == 0)
{
lean_object* v_a_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4507_; 
v_a_4497_ = lean_ctor_get(v___x_4496_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4499_ = v___x_4496_;
v_isShared_4500_ = v_isSharedCheck_4507_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_a_4497_);
lean_dec(v___x_4496_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4507_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4502_; 
if (v_isShared_4494_ == 0)
{
lean_ctor_set(v___x_4493_, 0, v_a_4497_);
v___x_4502_ = v___x_4493_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4497_);
v___x_4502_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
lean_object* v___x_4504_; 
if (v_isShared_4500_ == 0)
{
lean_ctor_set(v___x_4499_, 0, v___x_4502_);
v___x_4504_ = v___x_4499_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4502_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
}
}
}
}
else
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
lean_del_object(v___x_4493_);
v_a_4508_ = lean_ctor_get(v___x_4496_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___x_4496_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4496_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4508_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
}
}
else
{
lean_object* v___x_4517_; 
lean_dec(v_a_4490_);
v___x_4517_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_4469_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4553_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4520_ = v___x_4517_;
v_isShared_4521_ = v_isSharedCheck_4553_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4517_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4553_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
if (lean_obj_tag(v_a_4518_) == 1)
{
lean_object* v_val_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4548_; 
lean_del_object(v___x_4520_);
v_val_4522_ = lean_ctor_get(v_a_4518_, 0);
v_isSharedCheck_4548_ = !lean_is_exclusive(v_a_4518_);
if (v_isSharedCheck_4548_ == 0)
{
v___x_4524_ = v_a_4518_;
v_isShared_4525_ = v_isSharedCheck_4548_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_val_4522_);
lean_dec(v_a_4518_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4548_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v_snd_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
v_snd_4526_ = lean_ctor_get(v_val_4522_, 1);
lean_inc(v_snd_4526_);
lean_dec(v_val_4522_);
v___x_4527_ = l_BitVec_shiftLeft(v_fst_4487_, v_snd_4488_, v_snd_4526_);
lean_dec(v_snd_4526_);
lean_dec(v_snd_4488_);
v___x_4528_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4487_, v___x_4527_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
if (lean_obj_tag(v___x_4528_) == 0)
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4539_; 
v_a_4529_ = lean_ctor_get(v___x_4528_, 0);
v_isSharedCheck_4539_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4531_ = v___x_4528_;
v_isShared_4532_ = v_isSharedCheck_4539_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4528_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4539_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4525_ == 0)
{
lean_ctor_set(v___x_4524_, 0, v_a_4529_);
v___x_4534_ = v___x_4524_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_a_4529_);
v___x_4534_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
lean_object* v___x_4536_; 
if (v_isShared_4532_ == 0)
{
lean_ctor_set(v___x_4531_, 0, v___x_4534_);
v___x_4536_ = v___x_4531_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4534_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
}
else
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4547_; 
lean_del_object(v___x_4524_);
v_a_4540_ = lean_ctor_get(v___x_4528_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4542_ = v___x_4528_;
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4528_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4545_; 
if (v_isShared_4543_ == 0)
{
v___x_4545_ = v___x_4542_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4540_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
}
}
}
}
}
else
{
lean_object* v___x_4549_; lean_object* v___x_4551_; 
lean_dec(v_a_4518_);
lean_dec(v_snd_4488_);
lean_dec(v_fst_4487_);
v___x_4549_ = lean_box(0);
if (v_isShared_4521_ == 0)
{
lean_ctor_set(v___x_4520_, 0, v___x_4549_);
v___x_4551_ = v___x_4520_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v___x_4549_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
lean_dec(v_snd_4488_);
lean_dec(v_fst_4487_);
v_a_4554_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4517_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4517_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
}
else
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4569_; 
lean_dec(v_snd_4488_);
lean_dec(v_fst_4487_);
lean_dec_ref(v_r_u2082_4469_);
v_a_4562_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4564_ = v___x_4489_;
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4489_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4562_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
}
else
{
lean_object* v___x_4570_; lean_object* v___x_4572_; 
lean_dec(v_a_4482_);
lean_dec_ref(v_r_u2082_4469_);
v___x_4570_ = lean_box(0);
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 0, v___x_4570_);
v___x_4572_ = v___x_4484_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4570_);
v___x_4572_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
return v___x_4572_;
}
}
}
}
else
{
lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4582_; 
lean_dec_ref(v_r_u2082_4469_);
v_a_4575_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4577_ = v___x_4481_;
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4481_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4580_; 
if (v_isShared_4578_ == 0)
{
v___x_4580_ = v___x_4577_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4575_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVHShiftLeft___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_u2081_4468_ = stack[0].m_obj;
lean_object* v_r_u2082_4469_ = stack[1].m_obj;
lean_object* v___y_4470_ = stack[2].m_obj;
lean_object* v___y_4471_ = stack[3].m_obj;
lean_object* v___y_4472_ = stack[4].m_obj;
lean_object* v___y_4473_ = stack[5].m_obj;
lean_object* v___y_4474_ = stack[6].m_obj;
lean_object* v___y_4475_ = stack[7].m_obj;
lean_object* v___y_4476_ = stack[8].m_obj;
lean_object* v___y_4477_ = stack[9].m_obj;
lean_object* v___y_4478_ = stack[10].m_obj;
lean_object* v___y_4479_ = stack[11].m_obj;
lean_object* v_res_4583_;
v_res_4583_ = l_Lean_Meta_Grind_propagateBVHShiftLeft___lam__0(v_r_u2081_4468_, v_r_u2082_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
stack->m_obj
 = v_res_4583_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___lam__0___boxed(lean_object* v_r_u2081_4584_, lean_object* v_r_u2082_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_){
_start:
{
lean_object* v_res_4597_; 
v_res_4597_ = l_Lean_Meta_Grind_propagateBVHShiftLeft___lam__0(v_r_u2081_4584_, v_r_u2082_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_);
lean_dec(v___y_4595_);
lean_dec_ref(v___y_4594_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
lean_dec(v___y_4587_);
lean_dec(v___y_4586_);
return v_res_4597_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft(lean_object* v_e_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_){
_start:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; uint8_t v___x_4618_; 
v___x_4616_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__2));
v___x_4617_ = lean_unsigned_to_nat(6u);
v___x_4618_ = l_Lean_Expr_isAppOfArity(v_e_4604_, v___x_4616_, v___x_4617_);
if (v___x_4618_ == 0)
{
lean_object* v___x_4619_; lean_object* v___x_4620_; 
lean_dec_ref(v_e_4604_);
v___x_4619_ = lean_box(0);
v___x_4620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4620_, 0, v___x_4619_);
return v___x_4620_;
}
else
{
lean_object* v___f_4621_; lean_object* v___x_4622_; 
v___f_4621_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__3));
v___x_4622_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4604_, v___f_4621_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_);
return v___x_4622_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVHShiftLeft_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4604_ = stack[0].m_obj;
lean_object* v_a_4605_ = stack[1].m_obj;
lean_object* v_a_4606_ = stack[2].m_obj;
lean_object* v_a_4607_ = stack[3].m_obj;
lean_object* v_a_4608_ = stack[4].m_obj;
lean_object* v_a_4609_ = stack[5].m_obj;
lean_object* v_a_4610_ = stack[6].m_obj;
lean_object* v_a_4611_ = stack[7].m_obj;
lean_object* v_a_4612_ = stack[8].m_obj;
lean_object* v_a_4613_ = stack[9].m_obj;
lean_object* v_a_4614_ = stack[10].m_obj;
lean_object* v_res_4623_;
v_res_4623_ = l_Lean_Meta_Grind_propagateBVHShiftLeft(v_e_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_);
stack->m_obj
 = v_res_4623_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___boxed(lean_object* v_e_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l_Lean_Meta_Grind_propagateBVHShiftLeft(v_e_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_);
lean_dec(v_a_4634_);
lean_dec_ref(v_a_4633_);
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec(v_a_4625_);
return v_res_4636_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2458924947____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4638_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__2));
v___x_4639_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVHShiftLeft___boxed), 12, 0);
v___x_4640_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4638_, v___x_4639_);
return v___x_4640_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2458924947____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4641_;
v_res_4641_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2458924947____hygCtx___hyg_9_();
stack->m_obj
 = v_res_4641_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2458924947____hygCtx___hyg_9____boxed(lean_object* v_a_4642_){
_start:
{
lean_object* v_res_4643_; 
v_res_4643_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2458924947____hygCtx___hyg_9_();
return v_res_4643_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight___lam__0(lean_object* v_r_u2081_4644_, lean_object* v_r_u2082_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
lean_object* v___x_4657_; 
v___x_4657_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4644_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4657_) == 0)
{
lean_object* v_a_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4750_; 
v_a_4658_ = lean_ctor_get(v___x_4657_, 0);
v_isSharedCheck_4750_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4660_ = v___x_4657_;
v_isShared_4661_ = v_isSharedCheck_4750_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_a_4658_);
lean_dec(v___x_4657_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4750_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
if (lean_obj_tag(v_a_4658_) == 1)
{
lean_object* v_val_4662_; lean_object* v_fst_4663_; lean_object* v_snd_4664_; lean_object* v___x_4665_; 
lean_del_object(v___x_4660_);
v_val_4662_ = lean_ctor_get(v_a_4658_, 0);
lean_inc(v_val_4662_);
lean_dec_ref_known(v_a_4658_, 1);
v_fst_4663_ = lean_ctor_get(v_val_4662_, 0);
lean_inc(v_fst_4663_);
v_snd_4664_ = lean_ctor_get(v_val_4662_, 1);
lean_inc(v_snd_4664_);
lean_dec(v_val_4662_);
v___x_4665_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4645_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_a_4666_);
lean_dec_ref_known(v___x_4665_, 1);
if (lean_obj_tag(v_a_4666_) == 1)
{
lean_object* v_val_4667_; lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4692_; 
lean_dec_ref(v_r_u2082_4645_);
v_val_4667_ = lean_ctor_get(v_a_4666_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v_a_4666_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4669_ = v_a_4666_;
v_isShared_4670_ = v_isSharedCheck_4692_;
goto v_resetjp_4668_;
}
else
{
lean_inc(v_val_4667_);
lean_dec(v_a_4666_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4692_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; 
v___x_4671_ = lean_nat_shiftr(v_snd_4664_, v_val_4667_);
lean_dec(v_val_4667_);
lean_dec(v_snd_4664_);
v___x_4672_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4663_, v___x_4671_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4683_; 
v_a_4673_ = lean_ctor_get(v___x_4672_, 0);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4672_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4675_ = v___x_4672_;
v_isShared_4676_ = v_isSharedCheck_4683_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v___x_4672_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4683_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4678_; 
if (v_isShared_4670_ == 0)
{
lean_ctor_set(v___x_4669_, 0, v_a_4673_);
v___x_4678_ = v___x_4669_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v_a_4673_);
v___x_4678_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
lean_object* v___x_4680_; 
if (v_isShared_4676_ == 0)
{
lean_ctor_set(v___x_4675_, 0, v___x_4678_);
v___x_4680_ = v___x_4675_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v___x_4678_);
v___x_4680_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
return v___x_4680_;
}
}
}
}
else
{
lean_object* v_a_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4691_; 
lean_del_object(v___x_4669_);
v_a_4684_ = lean_ctor_get(v___x_4672_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4672_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4686_ = v___x_4672_;
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_a_4684_);
lean_dec(v___x_4672_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4691_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v___x_4689_; 
if (v_isShared_4687_ == 0)
{
v___x_4689_ = v___x_4686_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_a_4684_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
}
}
else
{
lean_object* v___x_4693_; 
lean_dec(v_a_4666_);
v___x_4693_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_4645_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4693_) == 0)
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4729_; 
v_a_4694_ = lean_ctor_get(v___x_4693_, 0);
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4693_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4696_ = v___x_4693_;
v_isShared_4697_ = v_isSharedCheck_4729_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4693_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4729_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
if (lean_obj_tag(v_a_4694_) == 1)
{
lean_object* v_val_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4724_; 
lean_del_object(v___x_4696_);
v_val_4698_ = lean_ctor_get(v_a_4694_, 0);
v_isSharedCheck_4724_ = !lean_is_exclusive(v_a_4694_);
if (v_isSharedCheck_4724_ == 0)
{
v___x_4700_ = v_a_4694_;
v_isShared_4701_ = v_isSharedCheck_4724_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_val_4698_);
lean_dec(v_a_4694_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4724_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v_snd_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v_snd_4702_ = lean_ctor_get(v_val_4698_, 1);
lean_inc(v_snd_4702_);
lean_dec(v_val_4698_);
v___x_4703_ = lean_nat_shiftr(v_snd_4664_, v_snd_4702_);
lean_dec(v_snd_4702_);
lean_dec(v_snd_4664_);
v___x_4704_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4663_, v___x_4703_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4704_) == 0)
{
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4715_; 
v_a_4705_ = lean_ctor_get(v___x_4704_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4707_ = v___x_4704_;
v_isShared_4708_ = v_isSharedCheck_4715_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___x_4704_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4715_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4701_ == 0)
{
lean_ctor_set(v___x_4700_, 0, v_a_4705_);
v___x_4710_ = v___x_4700_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4705_);
v___x_4710_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
lean_object* v___x_4712_; 
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 0, v___x_4710_);
v___x_4712_ = v___x_4707_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v___x_4710_);
v___x_4712_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
return v___x_4712_;
}
}
}
}
else
{
lean_object* v_a_4716_; lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4723_; 
lean_del_object(v___x_4700_);
v_a_4716_ = lean_ctor_get(v___x_4704_, 0);
v_isSharedCheck_4723_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4718_ = v___x_4704_;
v_isShared_4719_ = v_isSharedCheck_4723_;
goto v_resetjp_4717_;
}
else
{
lean_inc(v_a_4716_);
lean_dec(v___x_4704_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4723_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
lean_object* v___x_4721_; 
if (v_isShared_4719_ == 0)
{
v___x_4721_ = v___x_4718_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v_a_4716_);
v___x_4721_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
return v___x_4721_;
}
}
}
}
}
else
{
lean_object* v___x_4725_; lean_object* v___x_4727_; 
lean_dec(v_a_4694_);
lean_dec(v_snd_4664_);
lean_dec(v_fst_4663_);
v___x_4725_ = lean_box(0);
if (v_isShared_4697_ == 0)
{
lean_ctor_set(v___x_4696_, 0, v___x_4725_);
v___x_4727_ = v___x_4696_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v___x_4725_);
v___x_4727_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
return v___x_4727_;
}
}
}
}
else
{
lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4737_; 
lean_dec(v_snd_4664_);
lean_dec(v_fst_4663_);
v_a_4730_ = lean_ctor_get(v___x_4693_, 0);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___x_4693_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4732_ = v___x_4693_;
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___x_4693_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4735_; 
if (v_isShared_4733_ == 0)
{
v___x_4735_ = v___x_4732_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4730_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
}
}
}
else
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4745_; 
lean_dec(v_snd_4664_);
lean_dec(v_fst_4663_);
lean_dec_ref(v_r_u2082_4645_);
v_a_4738_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4740_ = v___x_4665_;
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v___x_4665_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4743_; 
if (v_isShared_4741_ == 0)
{
v___x_4743_ = v___x_4740_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4738_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
}
}
else
{
lean_object* v___x_4746_; lean_object* v___x_4748_; 
lean_dec(v_a_4658_);
lean_dec_ref(v_r_u2082_4645_);
v___x_4746_ = lean_box(0);
if (v_isShared_4661_ == 0)
{
lean_ctor_set(v___x_4660_, 0, v___x_4746_);
v___x_4748_ = v___x_4660_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v___x_4746_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
}
else
{
lean_object* v_a_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4758_; 
lean_dec_ref(v_r_u2082_4645_);
v_a_4751_ = lean_ctor_get(v___x_4657_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4753_ = v___x_4657_;
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_a_4751_);
lean_dec(v___x_4657_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4758_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v___x_4756_; 
if (v_isShared_4754_ == 0)
{
v___x_4756_ = v___x_4753_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_a_4751_);
v___x_4756_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
return v___x_4756_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVHShiftRight___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_u2081_4644_ = stack[0].m_obj;
lean_object* v_r_u2082_4645_ = stack[1].m_obj;
lean_object* v___y_4646_ = stack[2].m_obj;
lean_object* v___y_4647_ = stack[3].m_obj;
lean_object* v___y_4648_ = stack[4].m_obj;
lean_object* v___y_4649_ = stack[5].m_obj;
lean_object* v___y_4650_ = stack[6].m_obj;
lean_object* v___y_4651_ = stack[7].m_obj;
lean_object* v___y_4652_ = stack[8].m_obj;
lean_object* v___y_4653_ = stack[9].m_obj;
lean_object* v___y_4654_ = stack[10].m_obj;
lean_object* v___y_4655_ = stack[11].m_obj;
lean_object* v_res_4759_;
v_res_4759_ = l_Lean_Meta_Grind_propagateBVHShiftRight___lam__0(v_r_u2081_4644_, v_r_u2082_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
stack->m_obj
 = v_res_4759_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight___lam__0___boxed(lean_object* v_r_u2081_4760_, lean_object* v_r_u2082_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_){
_start:
{
lean_object* v_res_4773_; 
v_res_4773_ = l_Lean_Meta_Grind_propagateBVHShiftRight___lam__0(v_r_u2081_4760_, v_r_u2082_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_);
lean_dec(v___y_4771_);
lean_dec_ref(v___y_4770_);
lean_dec(v___y_4769_);
lean_dec_ref(v___y_4768_);
lean_dec(v___y_4767_);
lean_dec_ref(v___y_4766_);
lean_dec(v___y_4765_);
lean_dec_ref(v___y_4764_);
lean_dec(v___y_4763_);
lean_dec(v___y_4762_);
return v_res_4773_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight(lean_object* v_e_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_){
_start:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; uint8_t v___x_4794_; 
v___x_4792_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVHShiftRight___closed__2));
v___x_4793_ = lean_unsigned_to_nat(6u);
v___x_4794_ = l_Lean_Expr_isAppOfArity(v_e_4780_, v___x_4792_, v___x_4793_);
if (v___x_4794_ == 0)
{
lean_object* v___x_4795_; lean_object* v___x_4796_; 
lean_dec_ref(v_e_4780_);
v___x_4795_ = lean_box(0);
v___x_4796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4796_, 0, v___x_4795_);
return v___x_4796_;
}
else
{
lean_object* v___f_4797_; lean_object* v___x_4798_; 
v___f_4797_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVHShiftRight___closed__3));
v___x_4798_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4780_, v___f_4797_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_);
return v___x_4798_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVHShiftRight_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4780_ = stack[0].m_obj;
lean_object* v_a_4781_ = stack[1].m_obj;
lean_object* v_a_4782_ = stack[2].m_obj;
lean_object* v_a_4783_ = stack[3].m_obj;
lean_object* v_a_4784_ = stack[4].m_obj;
lean_object* v_a_4785_ = stack[5].m_obj;
lean_object* v_a_4786_ = stack[6].m_obj;
lean_object* v_a_4787_ = stack[7].m_obj;
lean_object* v_a_4788_ = stack[8].m_obj;
lean_object* v_a_4789_ = stack[9].m_obj;
lean_object* v_a_4790_ = stack[10].m_obj;
lean_object* v_res_4799_;
v_res_4799_ = l_Lean_Meta_Grind_propagateBVHShiftRight(v_e_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_);
stack->m_obj
 = v_res_4799_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight___boxed(lean_object* v_e_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l_Lean_Meta_Grind_propagateBVHShiftRight(v_e_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_);
lean_dec(v_a_4810_);
lean_dec_ref(v_a_4809_);
lean_dec(v_a_4808_);
lean_dec_ref(v_a_4807_);
lean_dec(v_a_4806_);
lean_dec_ref(v_a_4805_);
lean_dec(v_a_4804_);
lean_dec_ref(v_a_4803_);
lean_dec(v_a_4802_);
lean_dec(v_a_4801_);
return v_res_4812_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVHShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1131064821____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; 
v___x_4814_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVHShiftRight___closed__2));
v___x_4815_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVHShiftRight___boxed), 12, 0);
v___x_4816_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4814_, v___x_4815_);
return v___x_4816_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVHShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1131064821____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4817_;
v_res_4817_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVHShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1131064821____hygCtx___hyg_9_();
stack->m_obj
 = v_res_4817_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVHShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1131064821____hygCtx___hyg_9____boxed(lean_object* v_a_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVHShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1131064821____hygCtx___hyg_9_();
return v_res_4819_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD___lam__0(lean_object* v_r_u2081_4820_, lean_object* v_r_u2082_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_){
_start:
{
lean_object* v___x_4833_; 
v___x_4833_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4820_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_);
if (lean_obj_tag(v___x_4833_) == 0)
{
lean_object* v_a_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4888_; 
v_a_4834_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4836_ = v___x_4833_;
v_isShared_4837_ = v_isSharedCheck_4888_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_a_4834_);
lean_dec(v___x_4833_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4888_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
if (lean_obj_tag(v_a_4834_) == 1)
{
lean_object* v_val_4838_; lean_object* v_snd_4839_; lean_object* v___x_4840_; 
lean_del_object(v___x_4836_);
v_val_4838_ = lean_ctor_get(v_a_4834_, 0);
lean_inc(v_val_4838_);
lean_dec_ref_known(v_a_4834_, 1);
v_snd_4839_ = lean_ctor_get(v_val_4838_, 1);
lean_inc(v_snd_4839_);
lean_dec(v_val_4838_);
v___x_4840_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4821_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_);
if (lean_obj_tag(v___x_4840_) == 0)
{
lean_object* v_a_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4875_; 
v_a_4841_ = lean_ctor_get(v___x_4840_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4840_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4843_ = v___x_4840_;
v_isShared_4844_ = v_isSharedCheck_4875_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_a_4841_);
lean_dec(v___x_4840_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4875_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
if (lean_obj_tag(v_a_4841_) == 1)
{
lean_object* v_val_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4870_; 
lean_del_object(v___x_4843_);
v_val_4845_ = lean_ctor_get(v_a_4841_, 0);
v_isSharedCheck_4870_ = !lean_is_exclusive(v_a_4841_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4847_ = v_a_4841_;
v_isShared_4848_ = v_isSharedCheck_4870_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_val_4845_);
lean_dec(v_a_4841_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4870_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
uint8_t v___x_4849_; lean_object* v___x_4850_; 
v___x_4849_ = l_Nat_testBit(v_snd_4839_, v_val_4845_);
lean_dec(v_val_4845_);
lean_dec(v_snd_4839_);
v___x_4850_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v___x_4849_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_a_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4861_; 
v_a_4851_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4853_ = v___x_4850_;
v_isShared_4854_ = v_isSharedCheck_4861_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_a_4851_);
lean_dec(v___x_4850_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4861_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
lean_object* v___x_4856_; 
if (v_isShared_4848_ == 0)
{
lean_ctor_set(v___x_4847_, 0, v_a_4851_);
v___x_4856_ = v___x_4847_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_a_4851_);
v___x_4856_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
lean_object* v___x_4858_; 
if (v_isShared_4854_ == 0)
{
lean_ctor_set(v___x_4853_, 0, v___x_4856_);
v___x_4858_ = v___x_4853_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v___x_4856_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
}
else
{
lean_object* v_a_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4869_; 
lean_del_object(v___x_4847_);
v_a_4862_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4869_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4869_ == 0)
{
v___x_4864_ = v___x_4850_;
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_a_4862_);
lean_dec(v___x_4850_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4869_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
lean_object* v___x_4867_; 
if (v_isShared_4865_ == 0)
{
v___x_4867_ = v___x_4864_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v_a_4862_);
v___x_4867_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
return v___x_4867_;
}
}
}
}
}
else
{
lean_object* v___x_4871_; lean_object* v___x_4873_; 
lean_dec(v_a_4841_);
lean_dec(v_snd_4839_);
v___x_4871_ = lean_box(0);
if (v_isShared_4844_ == 0)
{
lean_ctor_set(v___x_4843_, 0, v___x_4871_);
v___x_4873_ = v___x_4843_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v___x_4871_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
}
else
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4883_; 
lean_dec(v_snd_4839_);
v_a_4876_ = lean_ctor_get(v___x_4840_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4840_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4878_ = v___x_4840_;
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4840_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4881_; 
if (v_isShared_4879_ == 0)
{
v___x_4881_ = v___x_4878_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v_a_4876_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
}
else
{
lean_object* v___x_4884_; lean_object* v___x_4886_; 
lean_dec(v_a_4834_);
v___x_4884_ = lean_box(0);
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 0, v___x_4884_);
v___x_4886_ = v___x_4836_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v___x_4884_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
}
else
{
lean_object* v_a_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4896_; 
v_a_4889_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4891_ = v___x_4833_;
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_a_4889_);
lean_dec(v___x_4833_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4894_; 
if (v_isShared_4892_ == 0)
{
v___x_4894_ = v___x_4891_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_a_4889_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVGetLsbD___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_u2081_4820_ = stack[0].m_obj;
lean_object* v_r_u2082_4821_ = stack[1].m_obj;
lean_object* v___y_4822_ = stack[2].m_obj;
lean_object* v___y_4823_ = stack[3].m_obj;
lean_object* v___y_4824_ = stack[4].m_obj;
lean_object* v___y_4825_ = stack[5].m_obj;
lean_object* v___y_4826_ = stack[6].m_obj;
lean_object* v___y_4827_ = stack[7].m_obj;
lean_object* v___y_4828_ = stack[8].m_obj;
lean_object* v___y_4829_ = stack[9].m_obj;
lean_object* v___y_4830_ = stack[10].m_obj;
lean_object* v___y_4831_ = stack[11].m_obj;
lean_object* v_res_4897_;
v_res_4897_ = l_Lean_Meta_Grind_propagateBVGetLsbD___lam__0(v_r_u2081_4820_, v_r_u2082_4821_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_);
stack->m_obj
 = v_res_4897_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD___lam__0___boxed(lean_object* v_r_u2081_4898_, lean_object* v_r_u2082_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l_Lean_Meta_Grind_propagateBVGetLsbD___lam__0(v_r_u2081_4898_, v_r_u2082_4899_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_);
lean_dec(v___y_4909_);
lean_dec_ref(v___y_4908_);
lean_dec(v___y_4907_);
lean_dec_ref(v___y_4906_);
lean_dec(v___y_4905_);
lean_dec_ref(v___y_4904_);
lean_dec(v___y_4903_);
lean_dec_ref(v___y_4902_);
lean_dec(v___y_4901_);
lean_dec(v___y_4900_);
lean_dec_ref(v_r_u2082_4899_);
return v_res_4911_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD(lean_object* v_e_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_){
_start:
{
lean_object* v___x_4929_; lean_object* v___x_4930_; uint8_t v___x_4931_; 
v___x_4929_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetLsbD___closed__1));
v___x_4930_ = lean_unsigned_to_nat(3u);
v___x_4931_ = l_Lean_Expr_isAppOfArity(v_e_4917_, v___x_4929_, v___x_4930_);
if (v___x_4931_ == 0)
{
lean_object* v___x_4932_; lean_object* v___x_4933_; 
lean_dec_ref(v_e_4917_);
v___x_4932_ = lean_box(0);
v___x_4933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4933_, 0, v___x_4932_);
return v___x_4933_;
}
else
{
lean_object* v___f_4934_; lean_object* v___x_4935_; 
v___f_4934_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetLsbD___closed__2));
v___x_4935_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4917_, v___f_4934_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
return v___x_4935_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVGetLsbD_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4917_ = stack[0].m_obj;
lean_object* v_a_4918_ = stack[1].m_obj;
lean_object* v_a_4919_ = stack[2].m_obj;
lean_object* v_a_4920_ = stack[3].m_obj;
lean_object* v_a_4921_ = stack[4].m_obj;
lean_object* v_a_4922_ = stack[5].m_obj;
lean_object* v_a_4923_ = stack[6].m_obj;
lean_object* v_a_4924_ = stack[7].m_obj;
lean_object* v_a_4925_ = stack[8].m_obj;
lean_object* v_a_4926_ = stack[9].m_obj;
lean_object* v_a_4927_ = stack[10].m_obj;
lean_object* v_res_4936_;
v_res_4936_ = l_Lean_Meta_Grind_propagateBVGetLsbD(v_e_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_, v_a_4926_, v_a_4927_);
stack->m_obj
 = v_res_4936_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD___boxed(lean_object* v_e_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_){
_start:
{
lean_object* v_res_4949_; 
v_res_4949_ = l_Lean_Meta_Grind_propagateBVGetLsbD(v_e_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_);
lean_dec(v_a_4947_);
lean_dec_ref(v_a_4946_);
lean_dec(v_a_4945_);
lean_dec_ref(v_a_4944_);
lean_dec(v_a_4943_);
lean_dec_ref(v_a_4942_);
lean_dec(v_a_4941_);
lean_dec_ref(v_a_4940_);
lean_dec(v_a_4939_);
lean_dec(v_a_4938_);
return v_res_4949_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetLsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetLsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1075602488____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4951_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetLsbD___closed__1));
v___x_4952_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVGetLsbD___boxed), 12, 0);
v___x_4953_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4951_, v___x_4952_);
return v___x_4953_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetLsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetLsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1075602488____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4954_;
v_res_4954_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetLsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetLsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1075602488____hygCtx___hyg_9_();
stack->m_obj
 = v_res_4954_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetLsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetLsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1075602488____hygCtx___hyg_9____boxed(lean_object* v_a_4955_){
_start:
{
lean_object* v_res_4956_; 
v_res_4956_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetLsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetLsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1075602488____hygCtx___hyg_9_();
return v_res_4956_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD___lam__0(lean_object* v_r_u2081_4957_, lean_object* v_r_u2082_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_){
_start:
{
lean_object* v___x_4970_; 
v___x_4970_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4957_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
if (lean_obj_tag(v___x_4970_) == 0)
{
lean_object* v_a_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_5032_; 
v_a_4971_ = lean_ctor_get(v___x_4970_, 0);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_4970_);
if (v_isSharedCheck_5032_ == 0)
{
v___x_4973_ = v___x_4970_;
v_isShared_4974_ = v_isSharedCheck_5032_;
goto v_resetjp_4972_;
}
else
{
lean_inc(v_a_4971_);
lean_dec(v___x_4970_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_5032_;
goto v_resetjp_4972_;
}
v_resetjp_4972_:
{
if (lean_obj_tag(v_a_4971_) == 1)
{
lean_object* v_val_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_5027_; 
lean_del_object(v___x_4973_);
v_val_4975_ = lean_ctor_get(v_a_4971_, 0);
v_isSharedCheck_5027_ = !lean_is_exclusive(v_a_4971_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_4977_ = v_a_4971_;
v_isShared_4978_ = v_isSharedCheck_5027_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_val_4975_);
lean_dec(v_a_4971_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_5027_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
lean_object* v_fst_4979_; lean_object* v_snd_4980_; lean_object* v___x_4981_; 
v_fst_4979_ = lean_ctor_get(v_val_4975_, 0);
lean_inc(v_fst_4979_);
v_snd_4980_ = lean_ctor_get(v_val_4975_, 1);
lean_inc(v_snd_4980_);
lean_dec(v_val_4975_);
v___x_4981_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4958_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v_a_4982_; lean_object* v___x_4984_; uint8_t v_isShared_4985_; uint8_t v_isSharedCheck_5018_; 
v_a_4982_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_5018_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_5018_ == 0)
{
v___x_4984_ = v___x_4981_;
v_isShared_4985_ = v_isSharedCheck_5018_;
goto v_resetjp_4983_;
}
else
{
lean_inc(v_a_4982_);
lean_dec(v___x_4981_);
v___x_4984_ = lean_box(0);
v_isShared_4985_ = v_isSharedCheck_5018_;
goto v_resetjp_4983_;
}
v_resetjp_4983_:
{
uint8_t v___y_4987_; 
if (lean_obj_tag(v_a_4982_) == 1)
{
lean_object* v_val_5008_; uint8_t v___x_5009_; 
lean_del_object(v___x_4984_);
v_val_5008_ = lean_ctor_get(v_a_4982_, 0);
lean_inc(v_val_5008_);
lean_dec_ref_known(v_a_4982_, 1);
v___x_5009_ = lean_nat_dec_lt(v_val_5008_, v_fst_4979_);
if (v___x_5009_ == 0)
{
lean_dec(v_val_5008_);
lean_dec(v_snd_4980_);
lean_dec(v_fst_4979_);
v___y_4987_ = v___x_5009_;
goto v___jp_4986_;
}
else
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; uint8_t v___x_5013_; 
v___x_5010_ = lean_unsigned_to_nat(1u);
v___x_5011_ = lean_nat_sub(v_fst_4979_, v___x_5010_);
lean_dec(v_fst_4979_);
v___x_5012_ = lean_nat_sub(v___x_5011_, v_val_5008_);
lean_dec(v_val_5008_);
lean_dec(v___x_5011_);
v___x_5013_ = l_Nat_testBit(v_snd_4980_, v___x_5012_);
lean_dec(v___x_5012_);
lean_dec(v_snd_4980_);
v___y_4987_ = v___x_5013_;
goto v___jp_4986_;
}
}
else
{
lean_object* v___x_5014_; lean_object* v___x_5016_; 
lean_dec(v_a_4982_);
lean_dec(v_snd_4980_);
lean_dec(v_fst_4979_);
lean_del_object(v___x_4977_);
v___x_5014_ = lean_box(0);
if (v_isShared_4985_ == 0)
{
lean_ctor_set(v___x_4984_, 0, v___x_5014_);
v___x_5016_ = v___x_4984_;
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
v___jp_4986_:
{
lean_object* v___x_4988_; 
v___x_4988_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v___y_4987_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
if (lean_obj_tag(v___x_4988_) == 0)
{
lean_object* v_a_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4999_; 
v_a_4989_ = lean_ctor_get(v___x_4988_, 0);
v_isSharedCheck_4999_ = !lean_is_exclusive(v___x_4988_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4991_ = v___x_4988_;
v_isShared_4992_ = v_isSharedCheck_4999_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_a_4989_);
lean_dec(v___x_4988_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_4999_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4978_ == 0)
{
lean_ctor_set(v___x_4977_, 0, v_a_4989_);
v___x_4994_ = v___x_4977_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_a_4989_);
v___x_4994_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
lean_object* v___x_4996_; 
if (v_isShared_4992_ == 0)
{
lean_ctor_set(v___x_4991_, 0, v___x_4994_);
v___x_4996_ = v___x_4991_;
goto v_reusejp_4995_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v___x_4994_);
v___x_4996_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4995_;
}
v_reusejp_4995_:
{
return v___x_4996_;
}
}
}
}
else
{
lean_object* v_a_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5007_; 
lean_del_object(v___x_4977_);
v_a_5000_ = lean_ctor_get(v___x_4988_, 0);
v_isSharedCheck_5007_ = !lean_is_exclusive(v___x_4988_);
if (v_isSharedCheck_5007_ == 0)
{
v___x_5002_ = v___x_4988_;
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_a_5000_);
lean_dec(v___x_4988_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5005_; 
if (v_isShared_5003_ == 0)
{
v___x_5005_ = v___x_5002_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v_a_5000_);
v___x_5005_ = v_reuseFailAlloc_5006_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
return v___x_5005_;
}
}
}
}
}
}
else
{
lean_object* v_a_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5026_; 
lean_dec(v_snd_4980_);
lean_dec(v_fst_4979_);
lean_del_object(v___x_4977_);
v_a_5019_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5021_ = v___x_4981_;
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_a_5019_);
lean_dec(v___x_4981_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5024_; 
if (v_isShared_5022_ == 0)
{
v___x_5024_ = v___x_5021_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v_a_5019_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
}
}
else
{
lean_object* v___x_5028_; lean_object* v___x_5030_; 
lean_dec(v_a_4971_);
v___x_5028_ = lean_box(0);
if (v_isShared_4974_ == 0)
{
lean_ctor_set(v___x_4973_, 0, v___x_5028_);
v___x_5030_ = v___x_4973_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v___x_5028_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
return v___x_5030_;
}
}
}
}
else
{
lean_object* v_a_5033_; lean_object* v___x_5035_; uint8_t v_isShared_5036_; uint8_t v_isSharedCheck_5040_; 
v_a_5033_ = lean_ctor_get(v___x_4970_, 0);
v_isSharedCheck_5040_ = !lean_is_exclusive(v___x_4970_);
if (v_isSharedCheck_5040_ == 0)
{
v___x_5035_ = v___x_4970_;
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
else
{
lean_inc(v_a_5033_);
lean_dec(v___x_4970_);
v___x_5035_ = lean_box(0);
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
v_resetjp_5034_:
{
lean_object* v___x_5038_; 
if (v_isShared_5036_ == 0)
{
v___x_5038_ = v___x_5035_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_a_5033_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVGetMsbD___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_u2081_4957_ = stack[0].m_obj;
lean_object* v_r_u2082_4958_ = stack[1].m_obj;
lean_object* v___y_4959_ = stack[2].m_obj;
lean_object* v___y_4960_ = stack[3].m_obj;
lean_object* v___y_4961_ = stack[4].m_obj;
lean_object* v___y_4962_ = stack[5].m_obj;
lean_object* v___y_4963_ = stack[6].m_obj;
lean_object* v___y_4964_ = stack[7].m_obj;
lean_object* v___y_4965_ = stack[8].m_obj;
lean_object* v___y_4966_ = stack[9].m_obj;
lean_object* v___y_4967_ = stack[10].m_obj;
lean_object* v___y_4968_ = stack[11].m_obj;
lean_object* v_res_5041_;
v_res_5041_ = l_Lean_Meta_Grind_propagateBVGetMsbD___lam__0(v_r_u2081_4957_, v_r_u2082_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
stack->m_obj
 = v_res_5041_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD___lam__0___boxed(lean_object* v_r_u2081_5042_, lean_object* v_r_u2082_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_){
_start:
{
lean_object* v_res_5055_; 
v_res_5055_ = l_Lean_Meta_Grind_propagateBVGetMsbD___lam__0(v_r_u2081_5042_, v_r_u2082_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
lean_dec(v___y_5049_);
lean_dec_ref(v___y_5048_);
lean_dec(v___y_5047_);
lean_dec_ref(v___y_5046_);
lean_dec(v___y_5045_);
lean_dec(v___y_5044_);
lean_dec_ref(v_r_u2082_5043_);
return v_res_5055_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD(lean_object* v_e_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_){
_start:
{
lean_object* v___x_5073_; lean_object* v___x_5074_; uint8_t v___x_5075_; 
v___x_5073_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetMsbD___closed__1));
v___x_5074_ = lean_unsigned_to_nat(3u);
v___x_5075_ = l_Lean_Expr_isAppOfArity(v_e_5061_, v___x_5073_, v___x_5074_);
if (v___x_5075_ == 0)
{
lean_object* v___x_5076_; lean_object* v___x_5077_; 
lean_dec_ref(v_e_5061_);
v___x_5076_ = lean_box(0);
v___x_5077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5077_, 0, v___x_5076_);
return v___x_5077_;
}
else
{
lean_object* v___f_5078_; lean_object* v___x_5079_; 
v___f_5078_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetMsbD___closed__2));
v___x_5079_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_5061_, v___f_5078_, v_a_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
return v___x_5079_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVGetMsbD_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5061_ = stack[0].m_obj;
lean_object* v_a_5062_ = stack[1].m_obj;
lean_object* v_a_5063_ = stack[2].m_obj;
lean_object* v_a_5064_ = stack[3].m_obj;
lean_object* v_a_5065_ = stack[4].m_obj;
lean_object* v_a_5066_ = stack[5].m_obj;
lean_object* v_a_5067_ = stack[6].m_obj;
lean_object* v_a_5068_ = stack[7].m_obj;
lean_object* v_a_5069_ = stack[8].m_obj;
lean_object* v_a_5070_ = stack[9].m_obj;
lean_object* v_a_5071_ = stack[10].m_obj;
lean_object* v_res_5080_;
v_res_5080_ = l_Lean_Meta_Grind_propagateBVGetMsbD(v_e_5061_, v_a_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
stack->m_obj
 = v_res_5080_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD___boxed(lean_object* v_e_5081_, lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_, lean_object* v_a_5088_, lean_object* v_a_5089_, lean_object* v_a_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_){
_start:
{
lean_object* v_res_5093_; 
v_res_5093_ = l_Lean_Meta_Grind_propagateBVGetMsbD(v_e_5081_, v_a_5082_, v_a_5083_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_, v_a_5088_, v_a_5089_, v_a_5090_, v_a_5091_);
lean_dec(v_a_5091_);
lean_dec_ref(v_a_5090_);
lean_dec(v_a_5089_);
lean_dec_ref(v_a_5088_);
lean_dec(v_a_5087_);
lean_dec_ref(v_a_5086_);
lean_dec(v_a_5085_);
lean_dec_ref(v_a_5084_);
lean_dec(v_a_5083_);
lean_dec(v_a_5082_);
return v_res_5093_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetMsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetMsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1507361668____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___x_5095_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetMsbD___closed__1));
v___x_5096_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVGetMsbD___boxed), 12, 0);
v___x_5097_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_5095_, v___x_5096_);
return v___x_5097_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetMsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetMsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1507361668____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5098_;
v_res_5098_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetMsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetMsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1507361668____hygCtx___hyg_9_();
stack->m_obj
 = v_res_5098_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetMsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetMsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1507361668____hygCtx___hyg_9____boxed(lean_object* v_a_5099_){
_start:
{
lean_object* v_res_5100_; 
v_res_5100_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetMsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetMsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1507361668____hygCtx___hyg_9_();
return v_res_5100_;
}
}
lean_object* l_Lean_Meta_Grind_propagateBVGetElem(lean_object* v_e_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_){
_start:
{
lean_object* v___x_5133_; uint8_t v___x_5134_; 
lean_inc_ref(v_e_5118_);
v___x_5133_ = l_Lean_Expr_cleanupAnnotations(v_e_5118_);
v___x_5134_ = l_Lean_Expr_isApp(v___x_5133_);
if (v___x_5134_ == 0)
{
lean_dec_ref(v___x_5133_);
lean_dec_ref(v_e_5118_);
goto v___jp_5130_;
}
else
{
lean_object* v_arg_5135_; lean_object* v___x_5136_; uint8_t v___x_5137_; 
v_arg_5135_ = lean_ctor_get(v___x_5133_, 1);
lean_inc_ref(v_arg_5135_);
v___x_5136_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5133_);
v___x_5137_ = l_Lean_Expr_isApp(v___x_5136_);
if (v___x_5137_ == 0)
{
lean_dec_ref(v___x_5136_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
goto v___jp_5130_;
}
else
{
lean_object* v_arg_5138_; lean_object* v___x_5139_; uint8_t v___x_5140_; 
v_arg_5138_ = lean_ctor_get(v___x_5136_, 1);
lean_inc_ref(v_arg_5138_);
v___x_5139_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5136_);
v___x_5140_ = l_Lean_Expr_isApp(v___x_5139_);
if (v___x_5140_ == 0)
{
lean_dec_ref(v___x_5139_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
goto v___jp_5130_;
}
else
{
lean_object* v_arg_5141_; lean_object* v___x_5142_; uint8_t v___x_5143_; 
v_arg_5141_ = lean_ctor_get(v___x_5139_, 1);
lean_inc_ref(v_arg_5141_);
v___x_5142_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5139_);
v___x_5143_ = l_Lean_Expr_isApp(v___x_5142_);
if (v___x_5143_ == 0)
{
lean_dec_ref(v___x_5142_);
lean_dec_ref(v_arg_5141_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
goto v___jp_5130_;
}
else
{
lean_object* v_arg_5144_; lean_object* v___x_5145_; uint8_t v___x_5146_; 
v_arg_5144_ = lean_ctor_get(v___x_5142_, 1);
lean_inc_ref(v_arg_5144_);
v___x_5145_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5142_);
v___x_5146_ = l_Lean_Expr_isApp(v___x_5145_);
if (v___x_5146_ == 0)
{
lean_dec_ref(v___x_5145_);
lean_dec_ref(v_arg_5144_);
lean_dec_ref(v_arg_5141_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
goto v___jp_5130_;
}
else
{
lean_object* v_arg_5147_; lean_object* v___x_5148_; uint8_t v___x_5149_; 
v_arg_5147_ = lean_ctor_get(v___x_5145_, 1);
lean_inc_ref(v_arg_5147_);
v___x_5148_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5145_);
v___x_5149_ = l_Lean_Expr_isApp(v___x_5148_);
if (v___x_5149_ == 0)
{
lean_dec_ref(v___x_5148_);
lean_dec_ref(v_arg_5147_);
lean_dec_ref(v_arg_5144_);
lean_dec_ref(v_arg_5141_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
goto v___jp_5130_;
}
else
{
lean_object* v_arg_5150_; lean_object* v___x_5151_; uint8_t v___x_5152_; 
v_arg_5150_ = lean_ctor_get(v___x_5148_, 1);
lean_inc_ref(v_arg_5150_);
v___x_5151_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5148_);
v___x_5152_ = l_Lean_Expr_isApp(v___x_5151_);
if (v___x_5152_ == 0)
{
lean_dec_ref(v___x_5151_);
lean_dec_ref(v_arg_5150_);
lean_dec_ref(v_arg_5147_);
lean_dec_ref(v_arg_5144_);
lean_dec_ref(v_arg_5141_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
goto v___jp_5130_;
}
else
{
lean_object* v_arg_5153_; lean_object* v___x_5154_; uint8_t v___x_5155_; 
v_arg_5153_ = lean_ctor_get(v___x_5151_, 1);
lean_inc_ref(v_arg_5153_);
v___x_5154_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5151_);
v___x_5155_ = l_Lean_Expr_isApp(v___x_5154_);
if (v___x_5155_ == 0)
{
lean_dec_ref(v___x_5154_);
lean_dec_ref(v_arg_5153_);
lean_dec_ref(v_arg_5150_);
lean_dec_ref(v_arg_5147_);
lean_dec_ref(v_arg_5144_);
lean_dec_ref(v_arg_5141_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
goto v___jp_5130_;
}
else
{
lean_object* v_arg_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; uint8_t v___x_5159_; 
v_arg_5156_ = lean_ctor_get(v___x_5154_, 1);
lean_inc_ref(v_arg_5156_);
v___x_5157_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5154_);
v___x_5158_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetElem___closed__2));
v___x_5159_ = l_Lean_Expr_isConstOf(v___x_5157_, v___x_5158_);
if (v___x_5159_ == 0)
{
lean_dec_ref(v___x_5157_);
lean_dec_ref(v_arg_5156_);
lean_dec_ref(v_arg_5153_);
lean_dec_ref(v_arg_5150_);
lean_dec_ref(v_arg_5147_);
lean_dec_ref(v_arg_5144_);
lean_dec_ref(v_arg_5141_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
goto v___jp_5130_;
}
else
{
lean_object* v___x_5160_; uint8_t v___x_5161_; 
v___x_5160_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetElem___closed__4));
v___x_5161_ = l_Lean_Expr_isAppOf(v_arg_5144_, v___x_5160_);
if (v___x_5161_ == 0)
{
lean_object* v___x_5162_; lean_object* v___x_5163_; 
lean_dec_ref(v___x_5157_);
lean_dec_ref(v_arg_5156_);
lean_dec_ref(v_arg_5153_);
lean_dec_ref(v_arg_5150_);
lean_dec_ref(v_arg_5147_);
lean_dec_ref(v_arg_5144_);
lean_dec_ref(v_arg_5141_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
v___x_5162_ = lean_box(0);
v___x_5163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5163_, 0, v___x_5162_);
return v___x_5163_;
}
else
{
lean_object* v___x_5164_; lean_object* v___x_5165_; 
v___x_5164_ = lean_st_ref_get(v_a_5119_);
lean_inc_ref(v_arg_5138_);
v___x_5165_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_5164_, v_arg_5138_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_);
lean_dec(v___x_5164_);
if (lean_obj_tag(v___x_5165_) == 0)
{
lean_object* v_a_5166_; lean_object* v___x_5167_; 
v_a_5166_ = lean_ctor_get(v___x_5165_, 0);
lean_inc(v_a_5166_);
lean_dec_ref_known(v___x_5165_, 1);
v___x_5167_ = l_Lean_Meta_getNatValue_x3f(v_a_5166_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v_a_5168_; lean_object* v___x_5170_; uint8_t v_isShared_5171_; uint8_t v_isSharedCheck_5263_; 
v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5263_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5263_ == 0)
{
v___x_5170_ = v___x_5167_;
v_isShared_5171_ = v_isSharedCheck_5263_;
goto v_resetjp_5169_;
}
else
{
lean_inc(v_a_5168_);
lean_dec(v___x_5167_);
v___x_5170_ = lean_box(0);
v_isShared_5171_ = v_isSharedCheck_5263_;
goto v_resetjp_5169_;
}
v_resetjp_5169_:
{
if (lean_obj_tag(v_a_5168_) == 1)
{
lean_object* v_val_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; 
lean_del_object(v___x_5170_);
v_val_5172_ = lean_ctor_get(v_a_5168_, 0);
lean_inc(v_val_5172_);
lean_dec_ref_known(v_a_5168_, 1);
v___x_5173_ = lean_st_ref_get(v_a_5119_);
lean_inc_ref(v_arg_5141_);
v___x_5174_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_5173_, v_arg_5141_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_);
lean_dec(v___x_5173_);
if (lean_obj_tag(v___x_5174_) == 0)
{
lean_object* v_a_5175_; lean_object* v___x_5176_; 
v_a_5175_ = lean_ctor_get(v___x_5174_, 0);
lean_inc_n(v_a_5175_, 2);
lean_dec_ref_known(v___x_5174_, 1);
v___x_5176_ = l_Lean_Meta_getBitVecValue_x3f(v_a_5175_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_);
if (lean_obj_tag(v___x_5176_) == 0)
{
lean_object* v_a_5177_; lean_object* v___x_5179_; uint8_t v_isShared_5180_; uint8_t v_isSharedCheck_5242_; 
v_a_5177_ = lean_ctor_get(v___x_5176_, 0);
v_isSharedCheck_5242_ = !lean_is_exclusive(v___x_5176_);
if (v_isSharedCheck_5242_ == 0)
{
v___x_5179_ = v___x_5176_;
v_isShared_5180_ = v_isSharedCheck_5242_;
goto v_resetjp_5178_;
}
else
{
lean_inc(v_a_5177_);
lean_dec(v___x_5176_);
v___x_5179_ = lean_box(0);
v_isShared_5180_ = v_isSharedCheck_5242_;
goto v_resetjp_5178_;
}
v_resetjp_5178_:
{
if (lean_obj_tag(v_a_5177_) == 1)
{
lean_object* v_val_5181_; lean_object* v_fst_5182_; lean_object* v_snd_5183_; uint8_t v___x_5184_; 
v_val_5181_ = lean_ctor_get(v_a_5177_, 0);
lean_inc(v_val_5181_);
lean_dec_ref_known(v_a_5177_, 1);
v_fst_5182_ = lean_ctor_get(v_val_5181_, 0);
lean_inc(v_fst_5182_);
v_snd_5183_ = lean_ctor_get(v_val_5181_, 1);
lean_inc(v_snd_5183_);
lean_dec(v_val_5181_);
v___x_5184_ = lean_nat_dec_lt(v_val_5172_, v_fst_5182_);
lean_dec(v_fst_5182_);
if (v___x_5184_ == 0)
{
lean_object* v___x_5185_; lean_object* v___x_5187_; 
lean_dec(v_snd_5183_);
lean_dec(v_a_5175_);
lean_dec(v_val_5172_);
lean_dec(v_a_5166_);
lean_dec_ref(v___x_5157_);
lean_dec_ref(v_arg_5156_);
lean_dec_ref(v_arg_5153_);
lean_dec_ref(v_arg_5150_);
lean_dec_ref(v_arg_5147_);
lean_dec_ref(v_arg_5144_);
lean_dec_ref(v_arg_5141_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
v___x_5185_ = lean_box(0);
if (v_isShared_5180_ == 0)
{
lean_ctor_set(v___x_5179_, 0, v___x_5185_);
v___x_5187_ = v___x_5179_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v___x_5185_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
else
{
uint8_t v___x_5189_; lean_object* v___x_5190_; 
lean_del_object(v___x_5179_);
v___x_5189_ = l_Nat_testBit(v_snd_5183_, v_val_5172_);
lean_dec(v_val_5172_);
lean_dec(v_snd_5183_);
v___x_5190_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v___x_5189_, v_a_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_);
if (lean_obj_tag(v___x_5190_) == 0)
{
lean_object* v_a_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; 
v_a_5191_ = lean_ctor_get(v___x_5190_, 0);
lean_inc_n(v_a_5191_, 2);
lean_dec_ref_known(v___x_5190_, 1);
v___x_5192_ = lean_unsigned_to_nat(0u);
v___x_5193_ = lean_box(0);
lean_inc(v_a_5128_);
lean_inc_ref(v_a_5127_);
lean_inc(v_a_5126_);
lean_inc_ref(v_a_5125_);
lean_inc(v_a_5124_);
lean_inc_ref(v_a_5123_);
lean_inc(v_a_5122_);
lean_inc_ref(v_a_5121_);
lean_inc(v_a_5120_);
lean_inc(v_a_5119_);
v___x_5194_ = lean_grind_internalize(v_a_5191_, v___x_5192_, v___x_5193_, v_a_5119_, v_a_5120_, v_a_5121_, v_a_5122_, v_a_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_);
if (lean_obj_tag(v___x_5194_) == 0)
{
lean_object* v___x_5195_; uint8_t v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; 
lean_dec_ref_known(v___x_5194_, 1);
v___x_5195_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetElem___closed__6));
v___x_5196_ = 0;
lean_inc_n(v_a_5166_, 2);
lean_inc_n(v_a_5175_, 2);
lean_inc_ref(v_arg_5147_);
v___x_5197_ = l_Lean_mkAppB(v_arg_5147_, v_a_5175_, v_a_5166_);
v___x_5198_ = l_Lean_Expr_headBeta(v___x_5197_);
v___x_5199_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11);
lean_inc_n(v_a_5191_, 2);
lean_inc_ref(v_arg_5150_);
v___x_5200_ = l_Lean_mkAppB(v___x_5199_, v_arg_5150_, v_a_5191_);
v___x_5201_ = l_Lean_mkLambda(v___x_5195_, v___x_5196_, v___x_5198_, v___x_5200_);
v___x_5202_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetElem___closed__8));
v___x_5203_ = l_Lean_Expr_constLevels_x21(v___x_5157_);
lean_dec_ref(v___x_5157_);
v___x_5204_ = l_Lean_mkConst(v___x_5202_, v___x_5203_);
lean_inc_ref(v_arg_5141_);
v___x_5205_ = l_Lean_mkApp6(v___x_5204_, v_arg_5156_, v_arg_5153_, v_arg_5150_, v_arg_5147_, v_arg_5144_, v_arg_5141_);
lean_inc_ref(v_arg_5138_);
v___x_5206_ = l_Lean_mkApp5(v___x_5205_, v_a_5175_, v_arg_5138_, v_a_5166_, v_arg_5135_, v_a_5191_);
lean_inc(v_a_5128_);
lean_inc_ref(v_a_5127_);
lean_inc(v_a_5126_);
lean_inc_ref(v_a_5125_);
lean_inc(v_a_5124_);
lean_inc_ref(v_a_5123_);
lean_inc(v_a_5122_);
lean_inc_ref(v_a_5121_);
lean_inc(v_a_5120_);
lean_inc(v_a_5119_);
v___x_5207_ = lean_grind_mk_eq_proof(v_arg_5141_, v_a_5175_, v_a_5119_, v_a_5120_, v_a_5121_, v_a_5122_, v_a_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_);
if (lean_obj_tag(v___x_5207_) == 0)
{
lean_object* v_a_5208_; lean_object* v___x_5209_; 
v_a_5208_ = lean_ctor_get(v___x_5207_, 0);
lean_inc(v_a_5208_);
lean_dec_ref_known(v___x_5207_, 1);
lean_inc(v_a_5128_);
lean_inc_ref(v_a_5127_);
lean_inc(v_a_5126_);
lean_inc_ref(v_a_5125_);
lean_inc(v_a_5124_);
lean_inc_ref(v_a_5123_);
lean_inc(v_a_5122_);
lean_inc_ref(v_a_5121_);
lean_inc(v_a_5120_);
lean_inc(v_a_5119_);
v___x_5209_ = lean_grind_mk_eq_proof(v_arg_5138_, v_a_5166_, v_a_5119_, v_a_5120_, v_a_5121_, v_a_5122_, v_a_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_);
if (lean_obj_tag(v___x_5209_) == 0)
{
lean_object* v_a_5210_; lean_object* v___x_5211_; uint8_t v___x_5212_; lean_object* v___x_5213_; 
v_a_5210_ = lean_ctor_get(v___x_5209_, 0);
lean_inc(v_a_5210_);
lean_dec_ref_known(v___x_5209_, 1);
v___x_5211_ = l_Lean_mkApp3(v___x_5206_, v_a_5208_, v_a_5210_, v___x_5201_);
v___x_5212_ = 0;
v___x_5213_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_5118_, v_a_5191_, v___x_5211_, v___x_5212_, v_a_5119_, v_a_5121_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_);
return v___x_5213_;
}
else
{
lean_object* v_a_5214_; lean_object* v___x_5216_; uint8_t v_isShared_5217_; uint8_t v_isSharedCheck_5221_; 
lean_dec(v_a_5208_);
lean_dec_ref(v___x_5206_);
lean_dec_ref(v___x_5201_);
lean_dec(v_a_5191_);
lean_dec_ref(v_e_5118_);
v_a_5214_ = lean_ctor_get(v___x_5209_, 0);
v_isSharedCheck_5221_ = !lean_is_exclusive(v___x_5209_);
if (v_isSharedCheck_5221_ == 0)
{
v___x_5216_ = v___x_5209_;
v_isShared_5217_ = v_isSharedCheck_5221_;
goto v_resetjp_5215_;
}
else
{
lean_inc(v_a_5214_);
lean_dec(v___x_5209_);
v___x_5216_ = lean_box(0);
v_isShared_5217_ = v_isSharedCheck_5221_;
goto v_resetjp_5215_;
}
v_resetjp_5215_:
{
lean_object* v___x_5219_; 
if (v_isShared_5217_ == 0)
{
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
}
else
{
lean_object* v_a_5222_; lean_object* v___x_5224_; uint8_t v_isShared_5225_; uint8_t v_isSharedCheck_5229_; 
lean_dec_ref(v___x_5206_);
lean_dec_ref(v___x_5201_);
lean_dec(v_a_5191_);
lean_dec(v_a_5166_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_e_5118_);
v_a_5222_ = lean_ctor_get(v___x_5207_, 0);
v_isSharedCheck_5229_ = !lean_is_exclusive(v___x_5207_);
if (v_isSharedCheck_5229_ == 0)
{
v___x_5224_ = v___x_5207_;
v_isShared_5225_ = v_isSharedCheck_5229_;
goto v_resetjp_5223_;
}
else
{
lean_inc(v_a_5222_);
lean_dec(v___x_5207_);
v___x_5224_ = lean_box(0);
v_isShared_5225_ = v_isSharedCheck_5229_;
goto v_resetjp_5223_;
}
v_resetjp_5223_:
{
lean_object* v___x_5227_; 
if (v_isShared_5225_ == 0)
{
v___x_5227_ = v___x_5224_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_dec(v_a_5191_);
lean_dec(v_a_5175_);
lean_dec(v_a_5166_);
lean_dec_ref(v___x_5157_);
lean_dec_ref(v_arg_5156_);
lean_dec_ref(v_arg_5153_);
lean_dec_ref(v_arg_5150_);
lean_dec_ref(v_arg_5147_);
lean_dec_ref(v_arg_5144_);
lean_dec_ref(v_arg_5141_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
return v___x_5194_;
}
}
else
{
lean_object* v_a_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5237_; 
lean_dec(v_a_5175_);
lean_dec(v_a_5166_);
lean_dec_ref(v___x_5157_);
lean_dec_ref(v_arg_5156_);
lean_dec_ref(v_arg_5153_);
lean_dec_ref(v_arg_5150_);
lean_dec_ref(v_arg_5147_);
lean_dec_ref(v_arg_5144_);
lean_dec_ref(v_arg_5141_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
v_a_5230_ = lean_ctor_get(v___x_5190_, 0);
v_isSharedCheck_5237_ = !lean_is_exclusive(v___x_5190_);
if (v_isSharedCheck_5237_ == 0)
{
v___x_5232_ = v___x_5190_;
v_isShared_5233_ = v_isSharedCheck_5237_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_a_5230_);
lean_dec(v___x_5190_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5237_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
lean_object* v___x_5235_; 
if (v_isShared_5233_ == 0)
{
v___x_5235_ = v___x_5232_;
goto v_reusejp_5234_;
}
else
{
lean_object* v_reuseFailAlloc_5236_; 
v_reuseFailAlloc_5236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5236_, 0, v_a_5230_);
v___x_5235_ = v_reuseFailAlloc_5236_;
goto v_reusejp_5234_;
}
v_reusejp_5234_:
{
return v___x_5235_;
}
}
}
}
}
else
{
lean_object* v___x_5238_; lean_object* v___x_5240_; 
lean_dec(v_a_5177_);
lean_dec(v_a_5175_);
lean_dec(v_val_5172_);
lean_dec(v_a_5166_);
lean_dec_ref(v___x_5157_);
lean_dec_ref(v_arg_5156_);
lean_dec_ref(v_arg_5153_);
lean_dec_ref(v_arg_5150_);
lean_dec_ref(v_arg_5147_);
lean_dec_ref(v_arg_5144_);
lean_dec_ref(v_arg_5141_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
v___x_5238_ = lean_box(0);
if (v_isShared_5180_ == 0)
{
lean_ctor_set(v___x_5179_, 0, v___x_5238_);
v___x_5240_ = v___x_5179_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5241_; 
v_reuseFailAlloc_5241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5241_, 0, v___x_5238_);
v___x_5240_ = v_reuseFailAlloc_5241_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
return v___x_5240_;
}
}
}
}
else
{
lean_object* v_a_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5250_; 
lean_dec(v_a_5175_);
lean_dec(v_val_5172_);
lean_dec(v_a_5166_);
lean_dec_ref(v___x_5157_);
lean_dec_ref(v_arg_5156_);
lean_dec_ref(v_arg_5153_);
lean_dec_ref(v_arg_5150_);
lean_dec_ref(v_arg_5147_);
lean_dec_ref(v_arg_5144_);
lean_dec_ref(v_arg_5141_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
v_a_5243_ = lean_ctor_get(v___x_5176_, 0);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5176_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_5245_ = v___x_5176_;
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v___x_5176_);
v___x_5245_ = lean_box(0);
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
v_resetjp_5244_:
{
lean_object* v___x_5248_; 
if (v_isShared_5246_ == 0)
{
v___x_5248_ = v___x_5245_;
goto v_reusejp_5247_;
}
else
{
lean_object* v_reuseFailAlloc_5249_; 
v_reuseFailAlloc_5249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5249_, 0, v_a_5243_);
v___x_5248_ = v_reuseFailAlloc_5249_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
return v___x_5248_;
}
}
}
}
else
{
lean_object* v_a_5251_; lean_object* v___x_5253_; uint8_t v_isShared_5254_; uint8_t v_isSharedCheck_5258_; 
lean_dec(v_val_5172_);
lean_dec(v_a_5166_);
lean_dec_ref(v___x_5157_);
lean_dec_ref(v_arg_5156_);
lean_dec_ref(v_arg_5153_);
lean_dec_ref(v_arg_5150_);
lean_dec_ref(v_arg_5147_);
lean_dec_ref(v_arg_5144_);
lean_dec_ref(v_arg_5141_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
v_a_5251_ = lean_ctor_get(v___x_5174_, 0);
v_isSharedCheck_5258_ = !lean_is_exclusive(v___x_5174_);
if (v_isSharedCheck_5258_ == 0)
{
v___x_5253_ = v___x_5174_;
v_isShared_5254_ = v_isSharedCheck_5258_;
goto v_resetjp_5252_;
}
else
{
lean_inc(v_a_5251_);
lean_dec(v___x_5174_);
v___x_5253_ = lean_box(0);
v_isShared_5254_ = v_isSharedCheck_5258_;
goto v_resetjp_5252_;
}
v_resetjp_5252_:
{
lean_object* v___x_5256_; 
if (v_isShared_5254_ == 0)
{
v___x_5256_ = v___x_5253_;
goto v_reusejp_5255_;
}
else
{
lean_object* v_reuseFailAlloc_5257_; 
v_reuseFailAlloc_5257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5257_, 0, v_a_5251_);
v___x_5256_ = v_reuseFailAlloc_5257_;
goto v_reusejp_5255_;
}
v_reusejp_5255_:
{
return v___x_5256_;
}
}
}
}
else
{
lean_object* v___x_5259_; lean_object* v___x_5261_; 
lean_dec(v_a_5168_);
lean_dec(v_a_5166_);
lean_dec_ref(v___x_5157_);
lean_dec_ref(v_arg_5156_);
lean_dec_ref(v_arg_5153_);
lean_dec_ref(v_arg_5150_);
lean_dec_ref(v_arg_5147_);
lean_dec_ref(v_arg_5144_);
lean_dec_ref(v_arg_5141_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
v___x_5259_ = lean_box(0);
if (v_isShared_5171_ == 0)
{
lean_ctor_set(v___x_5170_, 0, v___x_5259_);
v___x_5261_ = v___x_5170_;
goto v_reusejp_5260_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v___x_5259_);
v___x_5261_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5260_;
}
v_reusejp_5260_:
{
return v___x_5261_;
}
}
}
}
else
{
lean_object* v_a_5264_; lean_object* v___x_5266_; uint8_t v_isShared_5267_; uint8_t v_isSharedCheck_5271_; 
lean_dec(v_a_5166_);
lean_dec_ref(v___x_5157_);
lean_dec_ref(v_arg_5156_);
lean_dec_ref(v_arg_5153_);
lean_dec_ref(v_arg_5150_);
lean_dec_ref(v_arg_5147_);
lean_dec_ref(v_arg_5144_);
lean_dec_ref(v_arg_5141_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
v_a_5264_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5271_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5271_ == 0)
{
v___x_5266_ = v___x_5167_;
v_isShared_5267_ = v_isSharedCheck_5271_;
goto v_resetjp_5265_;
}
else
{
lean_inc(v_a_5264_);
lean_dec(v___x_5167_);
v___x_5266_ = lean_box(0);
v_isShared_5267_ = v_isSharedCheck_5271_;
goto v_resetjp_5265_;
}
v_resetjp_5265_:
{
lean_object* v___x_5269_; 
if (v_isShared_5267_ == 0)
{
v___x_5269_ = v___x_5266_;
goto v_reusejp_5268_;
}
else
{
lean_object* v_reuseFailAlloc_5270_; 
v_reuseFailAlloc_5270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5270_, 0, v_a_5264_);
v___x_5269_ = v_reuseFailAlloc_5270_;
goto v_reusejp_5268_;
}
v_reusejp_5268_:
{
return v___x_5269_;
}
}
}
}
else
{
lean_object* v_a_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5279_; 
lean_dec_ref(v___x_5157_);
lean_dec_ref(v_arg_5156_);
lean_dec_ref(v_arg_5153_);
lean_dec_ref(v_arg_5150_);
lean_dec_ref(v_arg_5147_);
lean_dec_ref(v_arg_5144_);
lean_dec_ref(v_arg_5141_);
lean_dec_ref(v_arg_5138_);
lean_dec_ref(v_arg_5135_);
lean_dec_ref(v_e_5118_);
v_a_5272_ = lean_ctor_get(v___x_5165_, 0);
v_isSharedCheck_5279_ = !lean_is_exclusive(v___x_5165_);
if (v_isSharedCheck_5279_ == 0)
{
v___x_5274_ = v___x_5165_;
v_isShared_5275_ = v_isSharedCheck_5279_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_a_5272_);
lean_dec(v___x_5165_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5279_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v___x_5277_; 
if (v_isShared_5275_ == 0)
{
v___x_5277_ = v___x_5274_;
goto v_reusejp_5276_;
}
else
{
lean_object* v_reuseFailAlloc_5278_; 
v_reuseFailAlloc_5278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5278_, 0, v_a_5272_);
v___x_5277_ = v_reuseFailAlloc_5278_;
goto v_reusejp_5276_;
}
v_reusejp_5276_:
{
return v___x_5277_;
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
}
v___jp_5130_:
{
lean_object* v___x_5131_; lean_object* v___x_5132_; 
v___x_5131_ = lean_box(0);
v___x_5132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5132_, 0, v___x_5131_);
return v___x_5132_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_propagateBVGetElem_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5118_ = stack[0].m_obj;
lean_object* v_a_5119_ = stack[1].m_obj;
lean_object* v_a_5120_ = stack[2].m_obj;
lean_object* v_a_5121_ = stack[3].m_obj;
lean_object* v_a_5122_ = stack[4].m_obj;
lean_object* v_a_5123_ = stack[5].m_obj;
lean_object* v_a_5124_ = stack[6].m_obj;
lean_object* v_a_5125_ = stack[7].m_obj;
lean_object* v_a_5126_ = stack[8].m_obj;
lean_object* v_a_5127_ = stack[9].m_obj;
lean_object* v_a_5128_ = stack[10].m_obj;
lean_object* v_res_5280_;
v_res_5280_ = l_Lean_Meta_Grind_propagateBVGetElem(v_e_5118_, v_a_5119_, v_a_5120_, v_a_5121_, v_a_5122_, v_a_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_);
stack->m_obj
 = v_res_5280_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetElem___boxed(lean_object* v_e_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_){
_start:
{
lean_object* v_res_5293_; 
v_res_5293_ = l_Lean_Meta_Grind_propagateBVGetElem(v_e_5281_, v_a_5282_, v_a_5283_, v_a_5284_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_);
lean_dec(v_a_5291_);
lean_dec_ref(v_a_5290_);
lean_dec(v_a_5289_);
lean_dec_ref(v_a_5288_);
lean_dec(v_a_5287_);
lean_dec_ref(v_a_5286_);
lean_dec(v_a_5285_);
lean_dec_ref(v_a_5284_);
lean_dec(v_a_5283_);
lean_dec(v_a_5282_);
return v_res_5293_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetElem___regBuiltin_Lean_Meta_Grind_propagateBVGetElem_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2454187461____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; 
v___x_5295_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetElem___closed__2));
v___x_5296_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVGetElem___boxed), 12, 0);
v___x_5297_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_5295_, v___x_5296_);
return v___x_5297_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetElem___regBuiltin_Lean_Meta_Grind_propagateBVGetElem_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2454187461____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5298_;
v_res_5298_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetElem___regBuiltin_Lean_Meta_Grind_propagateBVGetElem_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2454187461____hygCtx___hyg_9_();
stack->m_obj
 = v_res_5298_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetElem___regBuiltin_Lean_Meta_Grind_propagateBVGetElem_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2454187461____hygCtx___hyg_9____boxed(lean_object* v_a_5299_){
_start:
{
lean_object* v_res_5300_; 
v_res_5300_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetElem___regBuiltin_Lean_Meta_Grind_propagateBVGetElem_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2454187461____hygCtx___hyg_9_();
return v_res_5300_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_ToExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_BitVec(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVNot___regBuiltin_Lean_Meta_Grind_propagateBVNot_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_524020944____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVClz___regBuiltin_Lean_Meta_Grind_propagateBVClz_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3163129259____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVCpop___regBuiltin_Lean_Meta_Grind_propagateBVCpop_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4094280043____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVMsb___regBuiltin_Lean_Meta_Grind_propagateBVMsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1379739246____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToNat___regBuiltin_Lean_Meta_Grind_propagateBVToNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1265925494____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToInt___regBuiltin_Lean_Meta_Grind_propagateBVToInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2998338308____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1693823724____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_16048587____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4241407876____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3429100332____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3327375609____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAnd___regBuiltin_Lean_Meta_Grind_propagateBVAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_317501673____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOr___regBuiltin_Lean_Meta_Grind_propagateBVOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4272827602____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVXor___regBuiltin_Lean_Meta_Grind_propagateBVXor_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1120302969____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4057925374____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3262547096____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVUShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVUShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1878785357____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVSShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3342532823____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateLeft___regBuiltin_Lean_Meta_Grind_propagateBVRotateLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1541346404____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateRight___regBuiltin_Lean_Meta_Grind_propagateBVRotateRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2456321972____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2458924947____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVHShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1131064821____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetLsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetLsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1075602488____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetMsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetMsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1507361668____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetElem___regBuiltin_Lean_Meta_Grind_propagateBVGetElem_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2454187461____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_BitVec(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* initialize_Lean_ToExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_BitVec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_BitVec(builtin);
}
#ifdef __cplusplus
}
#endif
