// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.BitVec
// Imports: import Init.Grind import Init.Data.BitVec.Basic import Lean.Meta.LitValues import Lean.ToExpr import Lean.Meta.Tactic.Grind.Simp public import Lean.Meta.Tactic.Grind.PropagatorAttr import Lean.Util.SafeExponentiation
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
uint8_t l_Lean_isSafeBitVecWidth(lean_object*);
lean_object* l_BitVec_append___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_checkShiftLeft(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
lean_object* l_BitVec_clzFast(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1883179728____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1883179728____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVOfInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofInt"};
static const lean_object* l_Lean_Meta_Grind_propagateBVOfInt___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVOfInt___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVOfInt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVOfInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVOfInt___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVOfInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 33, 171, 14, 158, 104, 202, 91)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVOfInt___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVOfInt___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4268766526____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4268766526____hygCtx___hyg_9____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2693654335____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2693654335____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVExtractLsb___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "extractLsb"};
static const lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 192, 253, 234, 186, 255, 105, 184)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2382349498____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2382349498____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVReplicate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "replicate"};
static const lean_object* l_Lean_Meta_Grind_propagateBVReplicate___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVReplicate___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVReplicate___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVReplicate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVReplicate___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVReplicate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 123, 74, 120, 175, 214, 39, 20)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVReplicate___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVReplicate___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_281236239____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_281236239____hygCtx___hyg_9____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1194477106____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1194477106____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVShiftLeft___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "shiftLeft"};
static const lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVShiftLeft___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVShiftLeft___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVShiftLeft___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVShiftLeft___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVShiftLeft___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 17, 136, 59, 111, 1, 62, 62)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVShiftLeft___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3514232501____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3514232501____hygCtx___hyg_9____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "HShiftLeft"};
static const lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "hShiftLeft"};
static const lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 217, 51, 89, 252, 54, 156, 169)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__1_value),LEAN_SCALAR_PTR_LITERAL(181, 245, 218, 3, 224, 235, 179, 59)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3470952822____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3470952822____hygCtx___hyg_9____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(lean_object* v_n_7_, lean_object* v_v_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___boxed(lean_object* v_n_22_, lean_object* v_v_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_n_22_, v_v_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_, v_a_29_);
lean_dec(v_a_29_);
lean_dec_ref(v_a_28_);
lean_dec(v_a_27_);
lean_dec_ref(v_a_26_);
lean_dec(v_a_25_);
lean_dec_ref(v_a_24_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit(lean_object* v_n_32_, lean_object* v_v_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_n_32_, v_v_33_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___boxed(lean_object* v_n_46_, lean_object* v_v_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit(v_n_46_, v_v_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
lean_dec(v_a_55_);
lean_dec_ref(v_a_54_);
lean_dec(v_a_53_);
lean_dec_ref(v_a_52_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
lean_dec(v_a_48_);
return v_res_59_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__3(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_box(0);
v___x_66_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__2));
v___x_67_ = l_Lean_mkConst(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__6(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_box(0);
v___x_73_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__5));
v___x_74_ = l_Lean_mkConst(v___x_73_, v___x_72_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(uint8_t v_b_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
if (v_b_75_ == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__3);
v___x_84_ = l_Lean_Meta_Sym_shareCommon(v___x_83_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
return v___x_84_;
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__6, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___closed__6);
v___x_86_ = l_Lean_Meta_Sym_shareCommon(v___x_85_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg___boxed(lean_object* v_b_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
uint8_t v_b_boxed_95_; lean_object* v_res_96_; 
v_b_boxed_95_ = lean_unbox(v_b_87_);
v_res_96_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v_b_boxed_95_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit(uint8_t v_b_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v_b_97_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___boxed(lean_object* v_b_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
uint8_t v_b_boxed_122_; lean_object* v_res_123_; 
v_b_boxed_122_ = lean_unbox(v_b_110_);
v_res_123_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit(v_b_boxed_122_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec(v_a_111_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f___redArg(lean_object* v_x_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_st_ref_get(v_a_125_);
v___x_132_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_131_, v_x_124_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
lean_dec(v___x_131_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; lean_object* v___x_134_; 
v_a_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_a_133_);
lean_dec_ref_known(v___x_132_, 1);
v___x_134_ = l_Lean_Meta_getBitVecValue_x3f(v_a_133_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
return v___x_134_;
}
else
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
v_a_135_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_142_ == 0)
{
v___x_137_ = v___x_132_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_132_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_135_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f___redArg___boxed(lean_object* v_x_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f___redArg(v_x_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f(lean_object* v_x_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f___redArg(v_x_151_, v_a_152_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f___boxed(lean_object* v_x_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBV_x3f(v_x_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec(v_a_165_);
return v_res_176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_unsigned_to_nat(1u);
v___x_185_ = l_Lean_Level_ofNat(v___x_184_);
return v___x_185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__5(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_box(0);
v___x_187_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4);
v___x_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__6(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__5, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__5);
v___x_190_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4);
v___x_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
return v___x_191_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__7(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__6, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__6);
v___x_193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__3));
v___x_194_ = l_Lean_mkConst(v___x_193_, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__5, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__5);
v___x_201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__10));
v___x_202_ = l_Lean_mkConst(v___x_201_, v___x_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(lean_object* v_e_203_, lean_object* v_eval_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_a_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_a_216_ = l_Lean_Expr_appArg_x21(v_e_203_);
v___x_217_ = lean_st_ref_get(v_a_205_);
lean_inc_ref(v_a_216_);
v___x_218_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_217_, v_a_216_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
lean_dec(v___x_217_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_220_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc_n(v_a_219_, 2);
lean_dec_ref_known(v___x_218_, 1);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
lean_inc(v_a_212_);
lean_inc_ref(v_a_211_);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc(v_a_205_);
v___x_220_ = lean_apply_12(v_eval_204_, v_a_219_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, lean_box(0));
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_271_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_271_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_271_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_271_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
if (lean_obj_tag(v_a_221_) == 1)
{
lean_object* v_val_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
lean_del_object(v___x_223_);
v_val_225_ = lean_ctor_get(v_a_221_, 0);
lean_inc_n(v_val_225_, 2);
lean_dec_ref_known(v_a_221_, 1);
v___x_226_ = lean_unsigned_to_nat(0u);
v___x_227_ = lean_box(0);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
lean_inc(v_a_212_);
lean_inc_ref(v_a_211_);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc(v_a_205_);
v___x_228_ = lean_grind_internalize(v_val_225_, v___x_226_, v___x_227_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v___x_229_; 
lean_dec_ref_known(v___x_228_, 1);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
lean_inc(v_a_212_);
lean_inc_ref(v_a_211_);
lean_inc_ref(v_e_203_);
v___x_229_ = lean_infer_type(v_e_203_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_231_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v___x_229_, 1);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
lean_inc(v_a_212_);
lean_inc_ref(v_a_211_);
lean_inc_ref(v_a_216_);
v___x_231_ = lean_infer_type(v_a_216_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref_known(v___x_231_, 1);
v___x_233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__7, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__7);
v___x_234_ = l_Lean_Expr_appFn_x21(v_e_203_);
lean_inc(v_val_225_);
lean_inc(v_a_219_);
lean_inc_ref(v_a_216_);
lean_inc(v_a_230_);
v___x_235_ = l_Lean_mkApp6(v___x_233_, v_a_232_, v_a_230_, v___x_234_, v_a_216_, v_a_219_, v_val_225_);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
lean_inc(v_a_212_);
lean_inc_ref(v_a_211_);
lean_inc(v_a_210_);
lean_inc_ref(v_a_209_);
lean_inc(v_a_208_);
lean_inc_ref(v_a_207_);
lean_inc(v_a_206_);
lean_inc(v_a_205_);
v___x_236_ = lean_grind_mk_eq_proof(v_a_216_, v_a_219_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref_known(v___x_236_, 1);
v___x_238_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11);
lean_inc(v_val_225_);
v___x_239_ = l_Lean_mkAppB(v___x_238_, v_a_230_, v_val_225_);
v___x_240_ = l_Lean_mkAppB(v___x_235_, v_a_237_, v___x_239_);
v___x_241_ = 0;
v___x_242_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_203_, v_val_225_, v___x_240_, v___x_241_, v_a_205_, v_a_207_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
return v___x_242_;
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec_ref(v___x_235_);
lean_dec(v_a_230_);
lean_dec(v_val_225_);
lean_dec_ref(v_e_203_);
v_a_243_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_236_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_236_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec(v_a_230_);
lean_dec(v_val_225_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_216_);
lean_dec_ref(v_e_203_);
v_a_251_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_231_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_231_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec(v_val_225_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_216_);
lean_dec_ref(v_e_203_);
v_a_259_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_229_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_229_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
else
{
lean_dec(v_val_225_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_216_);
lean_dec_ref(v_e_203_);
return v___x_228_;
}
}
else
{
lean_object* v___x_267_; lean_object* v___x_269_; 
lean_dec(v_a_221_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_216_);
lean_dec_ref(v_e_203_);
v___x_267_ = lean_box(0);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_267_);
v___x_269_ = v___x_223_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
lean_dec(v_a_219_);
lean_dec_ref(v_a_216_);
lean_dec_ref(v_e_203_);
v_a_272_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_220_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_220_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_dec_ref(v_a_216_);
lean_dec_ref(v_eval_204_);
lean_dec_ref(v_e_203_);
v_a_280_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_218_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_218_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___boxed(lean_object* v_e_288_, lean_object* v_eval_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_288_, v_eval_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec(v_a_290_);
return v_res_301_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__2(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__6, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__6);
v___x_308_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__4);
v___x_309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_307_);
return v___x_309_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__3(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__2, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__2);
v___x_311_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__1));
v___x_312_ = l_Lean_mkConst(v___x_311_, v___x_310_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(lean_object* v_e_313_, lean_object* v_eval_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_a_u2082_326_; lean_object* v___x_327_; lean_object* v_a_u2081_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_a_u2082_326_ = l_Lean_Expr_appArg_x21(v_e_313_);
v___x_327_ = l_Lean_Expr_appFn_x21(v_e_313_);
v_a_u2081_328_ = l_Lean_Expr_appArg_x21(v___x_327_);
v___x_329_ = lean_st_ref_get(v_a_315_);
lean_inc_ref(v_a_u2081_328_);
v___x_330_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_329_, v_a_u2081_328_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v___x_329_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_330_, 1);
v___x_332_ = lean_st_ref_get(v_a_315_);
lean_inc_ref(v_a_u2082_326_);
v___x_333_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_332_, v_a_u2082_326_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v___x_332_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_335_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc_n(v_a_334_, 2);
lean_dec_ref_known(v___x_333_, 1);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
lean_inc(v_a_316_);
lean_inc(v_a_315_);
lean_inc(v_a_331_);
v___x_335_ = lean_apply_13(v_eval_314_, v_a_331_, v_a_334_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, lean_box(0));
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_406_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_406_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_406_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_406_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
if (lean_obj_tag(v_a_336_) == 1)
{
lean_object* v_val_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
lean_del_object(v___x_338_);
v_val_340_ = lean_ctor_get(v_a_336_, 0);
lean_inc_n(v_val_340_, 2);
lean_dec_ref_known(v_a_336_, 1);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_box(0);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
lean_inc(v_a_316_);
lean_inc(v_a_315_);
v___x_343_ = lean_grind_internalize(v_val_340_, v___x_341_, v___x_342_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v___x_344_; 
lean_dec_ref_known(v___x_343_, 1);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc_ref(v_e_313_);
v___x_344_ = lean_infer_type(v_e_313_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v___x_346_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_344_, 1);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc_ref(v_a_u2081_328_);
v___x_346_ = lean_infer_type(v_a_u2081_328_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_348_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref_known(v___x_346_, 1);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc_ref(v_a_u2082_326_);
v___x_348_ = lean_infer_type(v_a_u2082_326_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_348_, 1);
v___x_350_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__3, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___closed__3);
v___x_351_ = l_Lean_Expr_appFn_x21(v___x_327_);
lean_dec_ref(v___x_327_);
lean_inc(v_val_340_);
lean_inc(v_a_334_);
lean_inc_ref(v_a_u2082_326_);
lean_inc(v_a_331_);
lean_inc_ref(v_a_u2081_328_);
lean_inc(v_a_345_);
v___x_352_ = l_Lean_mkApp9(v___x_350_, v_a_347_, v_a_349_, v_a_345_, v___x_351_, v_a_u2081_328_, v_a_331_, v_a_u2082_326_, v_a_334_, v_val_340_);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
lean_inc(v_a_316_);
lean_inc(v_a_315_);
v___x_353_ = lean_grind_mk_eq_proof(v_a_u2081_328_, v_a_331_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v___x_355_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref_known(v___x_353_, 1);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
lean_inc(v_a_316_);
lean_inc(v_a_315_);
v___x_355_ = lean_grind_mk_eq_proof(v_a_u2082_326_, v_a_334_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; lean_object* v___x_361_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_355_, 1);
v___x_357_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11);
lean_inc(v_val_340_);
v___x_358_ = l_Lean_mkAppB(v___x_357_, v_a_345_, v_val_340_);
v___x_359_ = l_Lean_mkApp3(v___x_352_, v_a_354_, v_a_356_, v___x_358_);
v___x_360_ = 0;
v___x_361_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_313_, v_val_340_, v___x_359_, v___x_360_, v_a_315_, v_a_317_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
return v___x_361_;
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec(v_a_354_);
lean_dec_ref(v___x_352_);
lean_dec(v_a_345_);
lean_dec(v_val_340_);
lean_dec_ref(v_e_313_);
v_a_362_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_355_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_355_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec_ref(v___x_352_);
lean_dec(v_a_345_);
lean_dec(v_val_340_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_u2082_326_);
lean_dec_ref(v_e_313_);
v_a_370_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_353_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_353_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
else
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
lean_dec(v_a_347_);
lean_dec(v_a_345_);
lean_dec(v_val_340_);
lean_dec(v_a_334_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_u2081_328_);
lean_dec_ref(v___x_327_);
lean_dec_ref(v_a_u2082_326_);
lean_dec_ref(v_e_313_);
v_a_378_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v___x_348_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_348_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec(v_a_345_);
lean_dec(v_val_340_);
lean_dec(v_a_334_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_u2081_328_);
lean_dec_ref(v___x_327_);
lean_dec_ref(v_a_u2082_326_);
lean_dec_ref(v_e_313_);
v_a_386_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_346_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_346_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec(v_val_340_);
lean_dec(v_a_334_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_u2081_328_);
lean_dec_ref(v___x_327_);
lean_dec_ref(v_a_u2082_326_);
lean_dec_ref(v_e_313_);
v_a_394_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_344_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_344_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
else
{
lean_dec(v_val_340_);
lean_dec(v_a_334_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_u2081_328_);
lean_dec_ref(v___x_327_);
lean_dec_ref(v_a_u2082_326_);
lean_dec_ref(v_e_313_);
return v___x_343_;
}
}
else
{
lean_object* v___x_402_; lean_object* v___x_404_; 
lean_dec(v_a_336_);
lean_dec(v_a_334_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_u2081_328_);
lean_dec_ref(v___x_327_);
lean_dec_ref(v_a_u2082_326_);
lean_dec_ref(v_e_313_);
v___x_402_ = lean_box(0);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_402_);
v___x_404_ = v___x_338_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec(v_a_334_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_u2081_328_);
lean_dec_ref(v___x_327_);
lean_dec_ref(v_a_u2082_326_);
lean_dec_ref(v_e_313_);
v_a_407_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_335_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_335_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec(v_a_331_);
lean_dec_ref(v_a_u2081_328_);
lean_dec_ref(v___x_327_);
lean_dec_ref(v_a_u2082_326_);
lean_dec_ref(v_eval_314_);
lean_dec_ref(v_e_313_);
v_a_415_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_333_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_333_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec_ref(v_a_u2081_328_);
lean_dec_ref(v___x_327_);
lean_dec_ref(v_a_u2082_326_);
lean_dec_ref(v_eval_314_);
lean_dec_ref(v_e_313_);
v_a_423_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_330_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_330_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp___boxed(lean_object* v_e_431_, lean_object* v_eval_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_431_, v_eval_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec(v_a_433_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV___lam__0(lean_object* v_op_445_, lean_object* v_r_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Meta_getBitVecValue_x3f(v_r_446_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_495_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_495_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_495_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_495_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
if (lean_obj_tag(v_a_459_) == 1)
{
lean_object* v_val_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_490_; 
lean_del_object(v___x_461_);
v_val_463_ = lean_ctor_get(v_a_459_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v_a_459_);
if (v_isSharedCheck_490_ == 0)
{
v___x_465_ = v_a_459_;
v_isShared_466_ = v_isSharedCheck_490_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_val_463_);
lean_dec(v_a_459_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_490_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v_fst_467_; lean_object* v_snd_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v_fst_467_ = lean_ctor_get(v_val_463_, 0);
lean_inc_n(v_fst_467_, 2);
v_snd_468_ = lean_ctor_get(v_val_463_, 1);
lean_inc(v_snd_468_);
lean_dec(v_val_463_);
v___x_469_ = lean_apply_2(v_op_445_, v_fst_467_, v_snd_468_);
v___x_470_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_467_, v___x_469_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_481_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_481_ == 0)
{
v___x_473_ = v___x_470_;
v_isShared_474_ = v_isSharedCheck_481_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_470_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_481_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v_a_471_);
v___x_476_ = v___x_465_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_480_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_478_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_476_);
v___x_478_ = v___x_473_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
lean_del_object(v___x_465_);
v_a_482_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_470_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_470_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
else
{
lean_object* v___x_491_; lean_object* v___x_493_; 
lean_dec(v_a_459_);
lean_dec_ref(v_op_445_);
v___x_491_ = lean_box(0);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_491_);
v___x_493_ = v___x_461_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref(v_op_445_);
v_a_496_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_458_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_458_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV___lam__0___boxed(lean_object* v_op_504_, lean_object* v_r_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV___lam__0(v_op_504_, v_r_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec(v___y_506_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV(lean_object* v_declName_518_, lean_object* v_arity_519_, lean_object* v_op_520_, lean_object* v_e_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
uint8_t v___x_533_; 
v___x_533_ = l_Lean_Expr_isAppOfArity(v_e_521_, v_declName_518_, v_arity_519_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec_ref(v_e_521_);
lean_dec_ref(v_op_520_);
v___x_534_ = lean_box(0);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
else
{
lean_object* v___f_536_; lean_object* v___x_537_; 
v___f_536_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV___lam__0___boxed), 13, 1);
lean_closure_set(v___f_536_, 0, v_op_520_);
v___x_537_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_521_, v___f_536_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV___boxed(lean_object* v_declName_538_, lean_object* v_arity_539_, lean_object* v_op_540_, lean_object* v_e_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryBV(v_declName_538_, v_arity_539_, v_op_540_, v_e_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
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
lean_dec(v_declName_538_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV___lam__0(lean_object* v_op_554_, lean_object* v_val_555_, lean_object* v_r_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Meta_getBitVecValue_x3f(v_r_556_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_605_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_605_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_605_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_605_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
if (lean_obj_tag(v_a_569_) == 1)
{
lean_object* v_val_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_600_; 
lean_del_object(v___x_571_);
v_val_573_ = lean_ctor_get(v_a_569_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v_a_569_);
if (v_isSharedCheck_600_ == 0)
{
v___x_575_ = v_a_569_;
v_isShared_576_ = v_isSharedCheck_600_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_val_573_);
lean_dec(v_a_569_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_600_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v_fst_577_; lean_object* v_snd_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_fst_577_ = lean_ctor_get(v_val_573_, 0);
lean_inc(v_fst_577_);
v_snd_578_ = lean_ctor_get(v_val_573_, 1);
lean_inc(v_snd_578_);
lean_dec(v_val_573_);
lean_inc(v_val_555_);
v___x_579_ = lean_apply_3(v_op_554_, v_fst_577_, v_val_555_, v_snd_578_);
v___x_580_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_val_555_, v___x_579_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_591_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_591_ == 0)
{
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_591_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_591_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v_a_581_);
v___x_586_ = v___x_575_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_590_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_588_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_586_);
v___x_588_ = v___x_583_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_del_object(v___x_575_);
v_a_592_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_580_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_580_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_603_; 
lean_dec(v_a_569_);
lean_dec(v_val_555_);
lean_dec_ref(v_op_554_);
v___x_601_ = lean_box(0);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_601_);
v___x_603_ = v___x_571_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec(v_val_555_);
lean_dec_ref(v_op_554_);
v_a_606_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_568_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_568_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV___lam__0___boxed(lean_object* v_op_614_, lean_object* v_val_615_, lean_object* v_r_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV___lam__0(v_op_614_, v_val_615_, v_r_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec(v___y_617_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV(lean_object* v_declName_629_, lean_object* v_op_630_, lean_object* v_e_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = lean_unsigned_to_nat(3u);
v___x_644_ = l_Lean_Expr_isAppOfArity(v_e_631_, v_declName_629_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec_ref(v_e_631_);
lean_dec_ref(v_op_630_);
v___x_645_ = lean_box(0);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = l_Lean_Expr_getAppNumArgs(v_e_631_);
v___x_649_ = lean_nat_sub(v___x_648_, v___x_647_);
lean_dec(v___x_648_);
v___x_650_ = lean_nat_sub(v___x_649_, v___x_647_);
lean_dec(v___x_649_);
v___x_651_ = l_Lean_Expr_getRevArg_x21(v_e_631_, v___x_650_);
v___x_652_ = l_Lean_Meta_getNatValue_x3f(v___x_651_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
lean_dec_ref(v___x_651_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_669_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_669_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_669_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_669_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
if (lean_obj_tag(v_a_653_) == 1)
{
lean_object* v_val_657_; uint8_t v___x_658_; 
v_val_657_ = lean_ctor_get(v_a_653_, 0);
lean_inc(v_val_657_);
lean_dec_ref_known(v_a_653_, 1);
v___x_658_ = l_Lean_isSafeBitVecWidth(v_val_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_661_; 
lean_dec(v_val_657_);
lean_dec_ref(v_e_631_);
lean_dec_ref(v_op_630_);
v___x_659_ = lean_box(0);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_659_);
v___x_661_ = v___x_655_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
else
{
lean_object* v___f_663_; lean_object* v___x_664_; 
lean_del_object(v___x_655_);
v___f_663_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV___lam__0___boxed), 14, 2);
lean_closure_set(v___f_663_, 0, v_op_630_);
lean_closure_set(v___f_663_, 1, v_val_657_);
v___x_664_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_631_, v___f_663_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
return v___x_664_;
}
}
else
{
lean_object* v___x_665_; lean_object* v___x_667_; 
lean_dec(v_a_653_);
lean_dec_ref(v_e_631_);
lean_dec_ref(v_op_630_);
v___x_665_ = lean_box(0);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_665_);
v___x_667_ = v___x_655_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v_e_631_);
lean_dec_ref(v_op_630_);
v_a_670_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_652_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_652_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV___boxed(lean_object* v_declName_678_, lean_object* v_op_679_, lean_object* v_e_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV(v_declName_678_, v_op_679_, v_e_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec(v_a_681_);
lean_dec(v_declName_678_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0(lean_object* v_op_693_, lean_object* v_val_694_, lean_object* v_val_695_, lean_object* v___x_696_, lean_object* v_r_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_Meta_getBitVecValue_x3f(v_r_697_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_746_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_746_ == 0)
{
v___x_712_ = v___x_709_;
v_isShared_713_ = v_isSharedCheck_746_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_746_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
if (lean_obj_tag(v_a_710_) == 1)
{
lean_object* v_val_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_741_; 
lean_del_object(v___x_712_);
v_val_714_ = lean_ctor_get(v_a_710_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v_a_710_);
if (v_isSharedCheck_741_ == 0)
{
v___x_716_ = v_a_710_;
v_isShared_717_ = v_isSharedCheck_741_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_val_714_);
lean_dec(v_a_710_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_741_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_fst_718_; lean_object* v_snd_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_fst_718_ = lean_ctor_get(v_val_714_, 0);
lean_inc(v_fst_718_);
v_snd_719_ = lean_ctor_get(v_val_714_, 1);
lean_inc(v_snd_719_);
lean_dec(v_val_714_);
v___x_720_ = lean_apply_4(v_op_693_, v_fst_718_, v_val_694_, v_val_695_, v_snd_719_);
v___x_721_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v___x_696_, v___x_720_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_732_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_732_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_732_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_732_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v_a_722_);
v___x_727_ = v___x_716_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_731_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_729_; 
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_727_);
v___x_729_ = v___x_724_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_del_object(v___x_716_);
v_a_733_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_721_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_721_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
else
{
lean_object* v___x_742_; lean_object* v___x_744_; 
lean_dec(v_a_710_);
lean_dec(v___x_696_);
lean_dec(v_val_695_);
lean_dec(v_val_694_);
lean_dec_ref(v_op_693_);
v___x_742_ = lean_box(0);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_742_);
v___x_744_ = v___x_712_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v___x_696_);
lean_dec(v_val_695_);
lean_dec(v_val_694_);
lean_dec_ref(v_op_693_);
v_a_747_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_709_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_709_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0___boxed(lean_object* v_op_755_, lean_object* v_val_756_, lean_object* v_val_757_, lean_object* v___x_758_, lean_object* v_r_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0(v_op_755_, v_val_756_, v_val_757_, v___x_758_, v_r_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec(v___y_760_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV(lean_object* v_declName_772_, lean_object* v_width_773_, lean_object* v_op_774_, lean_object* v_e_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_787_ = lean_unsigned_to_nat(4u);
v___x_788_ = l_Lean_Expr_isAppOfArity(v_e_775_, v_declName_772_, v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec_ref(v_e_775_);
lean_dec_ref(v_op_774_);
lean_dec_ref(v_width_773_);
v___x_789_ = lean_box(0);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
return v___x_790_;
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_791_ = lean_unsigned_to_nat(1u);
v___x_792_ = l_Lean_Expr_getAppNumArgs(v_e_775_);
v___x_793_ = lean_nat_sub(v___x_792_, v___x_791_);
v___x_794_ = lean_nat_sub(v___x_793_, v___x_791_);
lean_dec(v___x_793_);
v___x_795_ = l_Lean_Expr_getRevArg_x21(v_e_775_, v___x_794_);
v___x_796_ = l_Lean_Meta_getNatValue_x3f(v___x_795_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
lean_dec_ref(v___x_795_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_837_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_837_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_837_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_837_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
if (lean_obj_tag(v_a_797_) == 1)
{
lean_object* v_val_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_del_object(v___x_799_);
v_val_801_ = lean_ctor_get(v_a_797_, 0);
lean_inc(v_val_801_);
lean_dec_ref_known(v_a_797_, 1);
v___x_802_ = lean_unsigned_to_nat(2u);
v___x_803_ = lean_nat_sub(v___x_792_, v___x_802_);
lean_dec(v___x_792_);
v___x_804_ = lean_nat_sub(v___x_803_, v___x_791_);
lean_dec(v___x_803_);
v___x_805_ = l_Lean_Expr_getRevArg_x21(v_e_775_, v___x_804_);
v___x_806_ = l_Lean_Meta_getNatValue_x3f(v___x_805_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
lean_dec_ref(v___x_805_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_824_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_824_ == 0)
{
v___x_809_ = v___x_806_;
v_isShared_810_ = v_isSharedCheck_824_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_824_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
if (lean_obj_tag(v_a_807_) == 1)
{
lean_object* v_val_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
v_val_811_ = lean_ctor_get(v_a_807_, 0);
lean_inc_n(v_val_811_, 2);
lean_dec_ref_known(v_a_807_, 1);
lean_inc(v_val_801_);
v___x_812_ = lean_apply_2(v_width_773_, v_val_801_, v_val_811_);
v___x_813_ = l_Lean_isSafeBitVecWidth(v___x_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_816_; 
lean_dec(v___x_812_);
lean_dec(v_val_811_);
lean_dec(v_val_801_);
lean_dec_ref(v_e_775_);
lean_dec_ref(v_op_774_);
v___x_814_ = lean_box(0);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_814_);
v___x_816_ = v___x_809_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
else
{
lean_object* v___f_818_; lean_object* v___x_819_; 
lean_del_object(v___x_809_);
v___f_818_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0___boxed), 16, 4);
lean_closure_set(v___f_818_, 0, v_op_774_);
lean_closure_set(v___f_818_, 1, v_val_801_);
lean_closure_set(v___f_818_, 2, v_val_811_);
lean_closure_set(v___f_818_, 3, v___x_812_);
v___x_819_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_775_, v___f_818_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
return v___x_819_;
}
}
else
{
lean_object* v___x_820_; lean_object* v___x_822_; 
lean_dec(v_a_807_);
lean_dec(v_val_801_);
lean_dec_ref(v_e_775_);
lean_dec_ref(v_op_774_);
lean_dec_ref(v_width_773_);
v___x_820_ = lean_box(0);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_820_);
v___x_822_ = v___x_809_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v_val_801_);
lean_dec_ref(v_e_775_);
lean_dec_ref(v_op_774_);
lean_dec_ref(v_width_773_);
v_a_825_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_806_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_806_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
else
{
lean_object* v___x_833_; lean_object* v___x_835_; 
lean_dec(v_a_797_);
lean_dec(v___x_792_);
lean_dec_ref(v_e_775_);
lean_dec_ref(v_op_774_);
lean_dec_ref(v_width_773_);
v___x_833_ = lean_box(0);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_833_);
v___x_835_ = v___x_799_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
lean_dec(v___x_792_);
lean_dec_ref(v_e_775_);
lean_dec_ref(v_op_774_);
lean_dec_ref(v_width_773_);
v_a_838_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_796_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_796_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___boxed(lean_object* v_declName_846_, lean_object* v_width_847_, lean_object* v_op_848_, lean_object* v_e_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV(v_declName_846_, v_width_847_, v_op_848_, v_e_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec(v_a_850_);
lean_dec(v_declName_846_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0(lean_object* v_op_862_, lean_object* v_r_u2081_863_, lean_object* v_r_u2082_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_863_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_939_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_939_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_939_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_939_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
if (lean_obj_tag(v_a_877_) == 1)
{
lean_object* v_val_881_; lean_object* v_fst_882_; lean_object* v_snd_883_; lean_object* v___x_884_; 
lean_del_object(v___x_879_);
v_val_881_ = lean_ctor_get(v_a_877_, 0);
lean_inc(v_val_881_);
lean_dec_ref_known(v_a_877_, 1);
v_fst_882_ = lean_ctor_get(v_val_881_, 0);
lean_inc(v_fst_882_);
v_snd_883_ = lean_ctor_get(v_val_881_, 1);
lean_inc(v_snd_883_);
lean_dec(v_val_881_);
v___x_884_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_864_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_926_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_926_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_926_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_926_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
if (lean_obj_tag(v_a_885_) == 1)
{
lean_object* v_val_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_921_; 
v_val_889_ = lean_ctor_get(v_a_885_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v_a_885_);
if (v_isSharedCheck_921_ == 0)
{
v___x_891_ = v_a_885_;
v_isShared_892_ = v_isSharedCheck_921_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_val_889_);
lean_dec(v_a_885_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_921_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v_fst_893_; lean_object* v_snd_894_; uint8_t v___x_895_; 
v_fst_893_ = lean_ctor_get(v_val_889_, 0);
lean_inc(v_fst_893_);
v_snd_894_ = lean_ctor_get(v_val_889_, 1);
lean_inc(v_snd_894_);
lean_dec(v_val_889_);
v___x_895_ = lean_nat_dec_eq(v_fst_882_, v_fst_893_);
lean_dec(v_fst_893_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; lean_object* v___x_898_; 
lean_dec(v_snd_894_);
lean_del_object(v___x_891_);
lean_dec(v_snd_883_);
lean_dec(v_fst_882_);
lean_dec_ref(v_op_862_);
v___x_896_ = lean_box(0);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_896_);
v___x_898_ = v___x_887_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; 
lean_del_object(v___x_887_);
lean_inc(v_fst_882_);
v___x_900_ = lean_apply_3(v_op_862_, v_fst_882_, v_snd_883_, v_snd_894_);
v___x_901_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_882_, v___x_900_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_912_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_912_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v_a_902_);
v___x_907_ = v___x_891_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_911_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_909_; 
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_907_);
v___x_909_ = v___x_904_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_del_object(v___x_891_);
v_a_913_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_901_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_901_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
}
else
{
lean_object* v___x_922_; lean_object* v___x_924_; 
lean_dec(v_a_885_);
lean_dec(v_snd_883_);
lean_dec(v_fst_882_);
lean_dec_ref(v_op_862_);
v___x_922_ = lean_box(0);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_922_);
v___x_924_ = v___x_887_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_snd_883_);
lean_dec(v_fst_882_);
lean_dec_ref(v_op_862_);
v_a_927_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_884_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_884_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
else
{
lean_object* v___x_935_; lean_object* v___x_937_; 
lean_dec(v_a_877_);
lean_dec_ref(v_r_u2082_864_);
lean_dec_ref(v_op_862_);
v___x_935_ = lean_box(0);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_935_);
v___x_937_ = v___x_879_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v_r_u2082_864_);
lean_dec_ref(v_op_862_);
v_a_940_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_876_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_876_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0___boxed(lean_object* v_op_948_, lean_object* v_r_u2081_949_, lean_object* v_r_u2082_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0(v_op_948_, v_r_u2081_949_, v_r_u2082_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec(v___y_951_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV(lean_object* v_declName_963_, lean_object* v_arity_964_, lean_object* v_op_965_, lean_object* v_e_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
uint8_t v___x_978_; 
v___x_978_ = l_Lean_Expr_isAppOfArity(v_e_966_, v_declName_963_, v_arity_964_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; 
lean_dec_ref(v_e_966_);
lean_dec_ref(v_op_965_);
v___x_979_ = lean_box(0);
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
return v___x_980_;
}
else
{
lean_object* v___f_981_; lean_object* v___x_982_; 
v___f_981_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0___boxed), 14, 1);
lean_closure_set(v___f_981_, 0, v_op_965_);
v___x_982_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_966_, v___f_981_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___boxed(lean_object* v_declName_983_, lean_object* v_arity_984_, lean_object* v_op_985_, lean_object* v_e_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV(v_declName_983_, v_arity_984_, v_op_985_, v_e_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
lean_dec(v_a_987_);
lean_dec(v_declName_983_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0(lean_object* v_op_999_, uint8_t v_isLeftShift_1000_, uint8_t v___x_1001_, lean_object* v_r_u2081_1002_, lean_object* v_r_u2082_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_1002_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1097_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1018_ = v___x_1015_;
v_isShared_1019_ = v_isSharedCheck_1097_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1097_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
if (lean_obj_tag(v_a_1016_) == 1)
{
lean_object* v_val_1020_; lean_object* v_fst_1021_; lean_object* v_snd_1022_; lean_object* v___x_1023_; 
lean_del_object(v___x_1018_);
v_val_1020_ = lean_ctor_get(v_a_1016_, 0);
lean_inc(v_val_1020_);
lean_dec_ref_known(v_a_1016_, 1);
v_fst_1021_ = lean_ctor_get(v_val_1020_, 0);
lean_inc(v_fst_1021_);
v_snd_1022_ = lean_ctor_get(v_val_1020_, 1);
lean_inc(v_snd_1022_);
lean_dec(v_val_1020_);
v___x_1023_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_1003_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1084_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1084_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1084_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
if (lean_obj_tag(v_a_1024_) == 1)
{
lean_object* v_val_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1079_; 
lean_del_object(v___x_1026_);
v_val_1028_ = lean_ctor_get(v_a_1024_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_a_1024_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1030_ = v_a_1024_;
v_isShared_1031_ = v_isSharedCheck_1079_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_val_1028_);
lean_dec(v_a_1024_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1079_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; 
if (v_isLeftShift_1000_ == 0)
{
v___y_1033_ = v___y_1008_;
v___y_1034_ = v___y_1009_;
v___y_1035_ = v___y_1010_;
v___y_1036_ = v___y_1011_;
v___y_1037_ = v___y_1012_;
v___y_1038_ = v___y_1013_;
goto v___jp_1032_;
}
else
{
lean_object* v___x_1060_; 
lean_inc(v_val_1028_);
v___x_1060_ = l_Lean_checkShiftLeft(v_snd_1022_, v_val_1028_, v___x_1001_, v___y_1012_, v___y_1013_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1070_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1070_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1070_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
uint8_t v___x_1065_; 
v___x_1065_ = lean_unbox(v_a_1061_);
lean_dec(v_a_1061_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
lean_del_object(v___x_1030_);
lean_dec(v_val_1028_);
lean_dec(v_snd_1022_);
lean_dec(v_fst_1021_);
lean_dec_ref(v_op_999_);
v___x_1066_ = lean_box(0);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1066_);
v___x_1068_ = v___x_1063_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
else
{
lean_del_object(v___x_1063_);
v___y_1033_ = v___y_1008_;
v___y_1034_ = v___y_1009_;
v___y_1035_ = v___y_1010_;
v___y_1036_ = v___y_1011_;
v___y_1037_ = v___y_1012_;
v___y_1038_ = v___y_1013_;
goto v___jp_1032_;
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_del_object(v___x_1030_);
lean_dec(v_val_1028_);
lean_dec(v_snd_1022_);
lean_dec(v_fst_1021_);
lean_dec_ref(v_op_999_);
v_a_1071_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1060_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1060_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
v___jp_1032_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_inc(v_fst_1021_);
v___x_1039_ = lean_apply_3(v_op_999_, v_fst_1021_, v_snd_1022_, v_val_1028_);
v___x_1040_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_1021_, v___x_1039_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1051_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1051_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1051_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v_a_1041_);
v___x_1046_ = v___x_1030_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1048_; 
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1046_);
v___x_1048_ = v___x_1043_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
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
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_del_object(v___x_1030_);
v_a_1052_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1040_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1040_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
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
else
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
lean_dec(v_a_1024_);
lean_dec(v_snd_1022_);
lean_dec(v_fst_1021_);
lean_dec_ref(v_op_999_);
v___x_1080_ = lean_box(0);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1080_);
v___x_1082_ = v___x_1026_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec(v_snd_1022_);
lean_dec(v_fst_1021_);
lean_dec_ref(v_op_999_);
v_a_1085_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1023_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1023_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
lean_dec(v_a_1016_);
lean_dec_ref(v_op_999_);
v___x_1093_ = lean_box(0);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1093_);
v___x_1095_ = v___x_1018_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v_op_999_);
v_a_1098_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1015_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1015_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0___boxed(lean_object* v_op_1106_, lean_object* v_isLeftShift_1107_, lean_object* v___x_1108_, lean_object* v_r_u2081_1109_, lean_object* v_r_u2082_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
uint8_t v_isLeftShift_boxed_1122_; uint8_t v___x_6801__boxed_1123_; lean_object* v_res_1124_; 
v_isLeftShift_boxed_1122_ = lean_unbox(v_isLeftShift_1107_);
v___x_6801__boxed_1123_ = lean_unbox(v___x_1108_);
v_res_1124_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0(v_op_1106_, v_isLeftShift_boxed_1122_, v___x_6801__boxed_1123_, v_r_u2081_1109_, v_r_u2082_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v_r_u2082_1110_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV(lean_object* v_declName_1125_, lean_object* v_arity_1126_, lean_object* v_op_1127_, lean_object* v_e_1128_, uint8_t v_isLeftShift_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
uint8_t v___x_1141_; 
v___x_1141_ = l_Lean_Expr_isAppOfArity(v_e_1128_, v_declName_1125_, v_arity_1126_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec_ref(v_e_1128_);
lean_dec_ref(v_op_1127_);
v___x_1142_ = lean_box(0);
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___f_1146_; lean_object* v___x_1147_; 
v___x_1144_ = lean_box(v_isLeftShift_1129_);
v___x_1145_ = lean_box(v___x_1141_);
v___f_1146_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0___boxed), 16, 3);
lean_closure_set(v___f_1146_, 0, v_op_1127_);
lean_closure_set(v___f_1146_, 1, v___x_1144_);
lean_closure_set(v___f_1146_, 2, v___x_1145_);
v___x_1147_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_1128_, v___f_1146_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___boxed(lean_object* v_declName_1148_, lean_object* v_arity_1149_, lean_object* v_op_1150_, lean_object* v_e_1151_, lean_object* v_isLeftShift_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
uint8_t v_isLeftShift_boxed_1164_; lean_object* v_res_1165_; 
v_isLeftShift_boxed_1164_ = lean_unbox(v_isLeftShift_1152_);
v_res_1165_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV(v_declName_1148_, v_arity_1149_, v_op_1150_, v_e_1151_, v_isLeftShift_boxed_1164_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec(v_declName_1148_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___lam__0(lean_object* v_op_1166_, lean_object* v_r_u2081_1167_, lean_object* v_r_u2082_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_1167_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1237_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1183_ = v___x_1180_;
v_isShared_1184_ = v_isSharedCheck_1237_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1237_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
if (lean_obj_tag(v_a_1181_) == 1)
{
lean_object* v_val_1185_; lean_object* v_fst_1186_; lean_object* v_snd_1187_; lean_object* v___x_1188_; 
lean_del_object(v___x_1183_);
v_val_1185_ = lean_ctor_get(v_a_1181_, 0);
lean_inc(v_val_1185_);
lean_dec_ref_known(v_a_1181_, 1);
v_fst_1186_ = lean_ctor_get(v_val_1185_, 0);
lean_inc(v_fst_1186_);
v_snd_1187_ = lean_ctor_get(v_val_1185_, 1);
lean_inc(v_snd_1187_);
lean_dec(v_val_1185_);
v___x_1188_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_1168_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1224_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1191_ = v___x_1188_;
v_isShared_1192_ = v_isSharedCheck_1224_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1224_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
if (lean_obj_tag(v_a_1189_) == 1)
{
lean_object* v_val_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1219_; 
lean_del_object(v___x_1191_);
v_val_1193_ = lean_ctor_get(v_a_1189_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_a_1189_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1195_ = v_a_1189_;
v_isShared_1196_ = v_isSharedCheck_1219_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_val_1193_);
lean_dec(v_a_1189_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1219_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; uint8_t v___x_1198_; lean_object* v___x_1199_; 
v___x_1197_ = lean_apply_3(v_op_1166_, v_fst_1186_, v_snd_1187_, v_val_1193_);
v___x_1198_ = lean_unbox(v___x_1197_);
v___x_1199_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v___x_1198_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1210_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1202_ = v___x_1199_;
v_isShared_1203_ = v_isSharedCheck_1210_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1199_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1210_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v_a_1200_);
v___x_1205_ = v___x_1195_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1207_; 
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1205_);
v___x_1207_ = v___x_1202_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
lean_del_object(v___x_1195_);
v_a_1211_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1199_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1199_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1222_; 
lean_dec(v_a_1189_);
lean_dec(v_snd_1187_);
lean_dec(v_fst_1186_);
lean_dec_ref(v_op_1166_);
v___x_1220_ = lean_box(0);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1220_);
v___x_1222_ = v___x_1191_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec(v_snd_1187_);
lean_dec(v_fst_1186_);
lean_dec_ref(v_op_1166_);
v_a_1225_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1188_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1188_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1235_; 
lean_dec(v_a_1181_);
lean_dec_ref(v_op_1166_);
v___x_1233_ = lean_box(0);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1233_);
v___x_1235_ = v___x_1183_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
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
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
lean_dec_ref(v_op_1166_);
v_a_1238_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1180_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1180_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___lam__0___boxed(lean_object* v_op_1246_, lean_object* v_r_u2081_1247_, lean_object* v_r_u2082_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___lam__0(v_op_1246_, v_r_u2081_1247_, v_r_u2082_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v_r_u2082_1248_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV(lean_object* v_declName_1261_, lean_object* v_op_1262_, lean_object* v_e_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = lean_unsigned_to_nat(3u);
v___x_1276_ = l_Lean_Expr_isAppOfArity(v_e_1263_, v_declName_1261_, v___x_1275_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec_ref(v_e_1263_);
lean_dec_ref(v_op_1262_);
v___x_1277_ = lean_box(0);
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
return v___x_1278_;
}
else
{
lean_object* v___f_1279_; lean_object* v___x_1280_; 
v___f_1279_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___lam__0___boxed), 14, 1);
lean_closure_set(v___f_1279_, 0, v_op_1262_);
v___x_1280_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_1263_, v___f_1279_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
return v___x_1280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___boxed(lean_object* v_declName_1281_, lean_object* v_op_1282_, lean_object* v_e_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV(v_declName_1281_, v_op_1282_, v_e_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec(v_declName_1281_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVNot___lam__0(lean_object* v_r_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1296_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1345_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1345_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1345_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
if (lean_obj_tag(v_a_1309_) == 1)
{
lean_object* v_val_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1340_; 
lean_del_object(v___x_1311_);
v_val_1313_ = lean_ctor_get(v_a_1309_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_a_1309_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1315_ = v_a_1309_;
v_isShared_1316_ = v_isSharedCheck_1340_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_val_1313_);
lean_dec(v_a_1309_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1340_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v_fst_1317_; lean_object* v_snd_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v_fst_1317_ = lean_ctor_get(v_val_1313_, 0);
lean_inc(v_fst_1317_);
v_snd_1318_ = lean_ctor_get(v_val_1313_, 1);
lean_inc(v_snd_1318_);
lean_dec(v_val_1313_);
v___x_1319_ = l_BitVec_not(v_fst_1317_, v_snd_1318_);
lean_dec(v_snd_1318_);
v___x_1320_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_1317_, v___x_1319_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1331_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1331_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1331_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 0, v_a_1321_);
v___x_1326_ = v___x_1315_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1328_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1326_);
v___x_1328_ = v___x_1323_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_del_object(v___x_1315_);
v_a_1332_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1320_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1320_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1343_; 
lean_dec(v_a_1309_);
v___x_1341_ = lean_box(0);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1341_);
v___x_1343_ = v___x_1311_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
v_a_1346_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1308_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1308_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVNot___lam__0___boxed(lean_object* v_r_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_Meta_Grind_propagateBVNot___lam__0(v_r_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec(v___y_1355_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVNot(lean_object* v_e_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1385_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVNot___closed__2));
v___x_1386_ = lean_unsigned_to_nat(3u);
v___x_1387_ = l_Lean_Expr_isAppOfArity(v_e_1373_, v___x_1385_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec_ref(v_e_1373_);
v___x_1388_ = lean_box(0);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
else
{
lean_object* v___f_1390_; lean_object* v___x_1391_; 
v___f_1390_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVNot___closed__3));
v___x_1391_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1373_, v___f_1390_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
return v___x_1391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVNot___boxed(lean_object* v_e_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_Meta_Grind_propagateBVNot(v_e_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec(v_a_1393_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVNot___regBuiltin_Lean_Meta_Grind_propagateBVNot_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_524020944____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVNot___closed__2));
v___x_1407_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVNot___boxed), 12, 0);
v___x_1408_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1406_, v___x_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVNot___regBuiltin_Lean_Meta_Grind_propagateBVNot_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_524020944____hygCtx___hyg_9____boxed(lean_object* v_a_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVNot___regBuiltin_Lean_Meta_Grind_propagateBVNot_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_524020944____hygCtx___hyg_9_();
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVClz___lam__0(lean_object* v_r_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1411_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1460_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1460_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1460_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
if (lean_obj_tag(v_a_1424_) == 1)
{
lean_object* v_val_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1455_; 
lean_del_object(v___x_1426_);
v_val_1428_ = lean_ctor_get(v_a_1424_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_a_1424_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1430_ = v_a_1424_;
v_isShared_1431_ = v_isSharedCheck_1455_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_val_1428_);
lean_dec(v_a_1424_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1455_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v_fst_1432_; lean_object* v_snd_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v_fst_1432_ = lean_ctor_get(v_val_1428_, 0);
lean_inc(v_fst_1432_);
v_snd_1433_ = lean_ctor_get(v_val_1428_, 1);
lean_inc(v_snd_1433_);
lean_dec(v_val_1428_);
v___x_1434_ = l_BitVec_clzFast(v_fst_1432_, v_snd_1433_);
lean_dec(v_snd_1433_);
v___x_1435_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_1432_, v___x_1434_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1446_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1446_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1446_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v_a_1436_);
v___x_1441_ = v___x_1430_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1443_; 
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1441_);
v___x_1443_ = v___x_1438_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_del_object(v___x_1430_);
v_a_1447_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1435_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1435_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
lean_dec(v_a_1424_);
v___x_1456_ = lean_box(0);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1456_);
v___x_1458_ = v___x_1426_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
v_a_1461_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1423_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1423_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVClz___lam__0___boxed(lean_object* v_r_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_Meta_Grind_propagateBVClz___lam__0(v_r_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec(v___y_1470_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVClz(lean_object* v_e_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1499_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVClz___closed__1));
v___x_1500_ = lean_unsigned_to_nat(2u);
v___x_1501_ = l_Lean_Expr_isAppOfArity(v_e_1487_, v___x_1499_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_dec_ref(v_e_1487_);
v___x_1502_ = lean_box(0);
v___x_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
return v___x_1503_;
}
else
{
lean_object* v___f_1504_; lean_object* v___x_1505_; 
v___f_1504_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVClz___closed__2));
v___x_1505_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1487_, v___f_1504_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
return v___x_1505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVClz___boxed(lean_object* v_e_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_Meta_Grind_propagateBVClz(v_e_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
lean_dec(v_a_1514_);
lean_dec_ref(v_a_1513_);
lean_dec(v_a_1512_);
lean_dec_ref(v_a_1511_);
lean_dec(v_a_1510_);
lean_dec_ref(v_a_1509_);
lean_dec(v_a_1508_);
lean_dec(v_a_1507_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVClz___regBuiltin_Lean_Meta_Grind_propagateBVClz_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3163129259____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1520_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVClz___closed__1));
v___x_1521_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVClz___boxed), 12, 0);
v___x_1522_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1520_, v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVClz___regBuiltin_Lean_Meta_Grind_propagateBVClz_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3163129259____hygCtx___hyg_9____boxed(lean_object* v_a_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVClz___regBuiltin_Lean_Meta_Grind_propagateBVClz_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3163129259____hygCtx___hyg_9_();
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVCpop___lam__0(lean_object* v_r_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1525_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1574_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1574_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1574_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
if (lean_obj_tag(v_a_1538_) == 1)
{
lean_object* v_val_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1569_; 
lean_del_object(v___x_1540_);
v_val_1542_ = lean_ctor_get(v_a_1538_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v_a_1538_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1544_ = v_a_1538_;
v_isShared_1545_ = v_isSharedCheck_1569_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_val_1542_);
lean_dec(v_a_1538_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1569_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v_fst_1546_; lean_object* v_snd_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_fst_1546_ = lean_ctor_get(v_val_1542_, 0);
lean_inc_n(v_fst_1546_, 2);
v_snd_1547_ = lean_ctor_get(v_val_1542_, 1);
lean_inc(v_snd_1547_);
lean_dec(v_val_1542_);
v___x_1548_ = l_BitVec_cpop(v_fst_1546_, v_snd_1547_);
lean_dec(v_snd_1547_);
v___x_1549_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_1546_, v___x_1548_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1560_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1560_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1560_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v_a_1550_);
v___x_1555_ = v___x_1544_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1557_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1555_);
v___x_1557_ = v___x_1552_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_del_object(v___x_1544_);
v_a_1561_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1549_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1549_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
else
{
lean_object* v___x_1570_; lean_object* v___x_1572_; 
lean_dec(v_a_1538_);
v___x_1570_ = lean_box(0);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1570_);
v___x_1572_ = v___x_1540_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
v_a_1575_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1537_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1537_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVCpop___lam__0___boxed(lean_object* v_r_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_Meta_Grind_propagateBVCpop___lam__0(v_r_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec(v___y_1584_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVCpop(lean_object* v_e_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1613_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVCpop___closed__1));
v___x_1614_ = lean_unsigned_to_nat(2u);
v___x_1615_ = l_Lean_Expr_isAppOfArity(v_e_1601_, v___x_1613_, v___x_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
lean_dec_ref(v_e_1601_);
v___x_1616_ = lean_box(0);
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
return v___x_1617_;
}
else
{
lean_object* v___f_1618_; lean_object* v___x_1619_; 
v___f_1618_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVCpop___closed__2));
v___x_1619_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1601_, v___f_1618_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVCpop___boxed(lean_object* v_e_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Meta_Grind_propagateBVCpop(v_e_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec(v_a_1622_);
lean_dec(v_a_1621_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVCpop___regBuiltin_Lean_Meta_Grind_propagateBVCpop_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4094280043____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVCpop___closed__1));
v___x_1635_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVCpop___boxed), 12, 0);
v___x_1636_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1634_, v___x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVCpop___regBuiltin_Lean_Meta_Grind_propagateBVCpop_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4094280043____hygCtx___hyg_9____boxed(lean_object* v_a_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVCpop___regBuiltin_Lean_Meta_Grind_propagateBVCpop_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4094280043____hygCtx___hyg_9_();
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVMsb___lam__0(lean_object* v_r_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1639_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1688_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1688_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1688_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
uint8_t v___y_1657_; 
if (lean_obj_tag(v_a_1652_) == 1)
{
lean_object* v_val_1676_; lean_object* v_fst_1677_; lean_object* v_snd_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
lean_del_object(v___x_1654_);
v_val_1676_ = lean_ctor_get(v_a_1652_, 0);
lean_inc(v_val_1676_);
lean_dec_ref_known(v_a_1652_, 1);
v_fst_1677_ = lean_ctor_get(v_val_1676_, 0);
lean_inc(v_fst_1677_);
v_snd_1678_ = lean_ctor_get(v_val_1676_, 1);
lean_inc(v_snd_1678_);
lean_dec(v_val_1676_);
v___x_1679_ = lean_unsigned_to_nat(0u);
v___x_1680_ = lean_nat_dec_lt(v___x_1679_, v_fst_1677_);
if (v___x_1680_ == 0)
{
lean_dec(v_snd_1678_);
lean_dec(v_fst_1677_);
v___y_1657_ = v___x_1680_;
goto v___jp_1656_;
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1681_ = lean_unsigned_to_nat(1u);
v___x_1682_ = lean_nat_sub(v_fst_1677_, v___x_1681_);
lean_dec(v_fst_1677_);
v___x_1683_ = l_Nat_testBit(v_snd_1678_, v___x_1682_);
lean_dec(v___x_1682_);
lean_dec(v_snd_1678_);
v___y_1657_ = v___x_1683_;
goto v___jp_1656_;
}
}
else
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
lean_dec(v_a_1652_);
v___x_1684_ = lean_box(0);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1684_);
v___x_1686_ = v___x_1654_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
v___jp_1656_:
{
lean_object* v___x_1658_; 
v___x_1658_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v___y_1657_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1667_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1661_ = v___x_1658_;
v_isShared_1662_ = v_isSharedCheck_1667_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1667_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1663_, 0, v_a_1659_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v___x_1663_);
v___x_1665_ = v___x_1661_;
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
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
v_a_1668_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1658_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1658_);
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
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
v_a_1689_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1651_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1651_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVMsb___lam__0___boxed(lean_object* v_r_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_Meta_Grind_propagateBVMsb___lam__0(v_r_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec(v___y_1698_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVMsb(lean_object* v_e_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1727_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVMsb___closed__1));
v___x_1728_ = lean_unsigned_to_nat(2u);
v___x_1729_ = l_Lean_Expr_isAppOfArity(v_e_1715_, v___x_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec_ref(v_e_1715_);
v___x_1730_ = lean_box(0);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
else
{
lean_object* v___f_1732_; lean_object* v___x_1733_; 
v___f_1732_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVMsb___closed__2));
v___x_1733_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1715_, v___f_1732_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
return v___x_1733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVMsb___boxed(lean_object* v_e_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Meta_Grind_propagateBVMsb(v_e_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
lean_dec(v_a_1736_);
lean_dec(v_a_1735_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVMsb___regBuiltin_Lean_Meta_Grind_propagateBVMsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1379739246____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1748_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVMsb___closed__1));
v___x_1749_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVMsb___boxed), 12, 0);
v___x_1750_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1748_, v___x_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVMsb___regBuiltin_Lean_Meta_Grind_propagateBVMsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1379739246____hygCtx___hyg_9____boxed(lean_object* v_a_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVMsb___regBuiltin_Lean_Meta_Grind_propagateBVMsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1379739246____hygCtx___hyg_9_();
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToNat___lam__0(lean_object* v_r_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1753_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1801_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1801_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1801_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
if (lean_obj_tag(v_a_1766_) == 1)
{
lean_object* v_val_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1796_; 
lean_del_object(v___x_1768_);
v_val_1770_ = lean_ctor_get(v_a_1766_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_a_1766_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1772_ = v_a_1766_;
v_isShared_1773_ = v_isSharedCheck_1796_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_val_1770_);
lean_dec(v_a_1766_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1796_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v_snd_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_snd_1774_ = lean_ctor_get(v_val_1770_, 1);
lean_inc(v_snd_1774_);
lean_dec(v_val_1770_);
v___x_1775_ = l_Lean_mkNatLit(v_snd_1774_);
v___x_1776_ = l_Lean_Meta_Sym_shareCommon(v___x_1775_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1787_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1787_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1787_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v_a_1777_);
v___x_1782_ = v___x_1772_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1782_);
v___x_1784_ = v___x_1779_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_del_object(v___x_1772_);
v_a_1788_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1776_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1776_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1799_; 
lean_dec(v_a_1766_);
v___x_1797_ = lean_box(0);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1797_);
v___x_1799_ = v___x_1768_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
v_a_1802_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1765_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1765_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToNat___lam__0___boxed(lean_object* v_r_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_Meta_Grind_propagateBVToNat___lam__0(v_r_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec(v___y_1811_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToNat(lean_object* v_e_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1840_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToNat___closed__1));
v___x_1841_ = lean_unsigned_to_nat(2u);
v___x_1842_ = l_Lean_Expr_isAppOfArity(v_e_1828_, v___x_1840_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_dec_ref(v_e_1828_);
v___x_1843_ = lean_box(0);
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
return v___x_1844_;
}
else
{
lean_object* v___f_1845_; lean_object* v___x_1846_; 
v___f_1845_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToNat___closed__2));
v___x_1846_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1828_, v___f_1845_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
return v___x_1846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToNat___boxed(lean_object* v_e_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_Meta_Grind_propagateBVToNat(v_e_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
lean_dec(v_a_1849_);
lean_dec(v_a_1848_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToNat___regBuiltin_Lean_Meta_Grind_propagateBVToNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1265925494____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1861_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToNat___closed__1));
v___x_1862_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVToNat___boxed), 12, 0);
v___x_1863_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1861_, v___x_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToNat___regBuiltin_Lean_Meta_Grind_propagateBVToNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1265925494____hygCtx___hyg_9____boxed(lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToNat___regBuiltin_Lean_Meta_Grind_propagateBVToNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1265925494____hygCtx___hyg_9_();
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToInt___lam__0(lean_object* v_r_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1866_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1916_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1881_ = v___x_1878_;
v_isShared_1882_ = v_isSharedCheck_1916_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1878_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1916_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
if (lean_obj_tag(v_a_1879_) == 1)
{
lean_object* v_val_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1911_; 
lean_del_object(v___x_1881_);
v_val_1883_ = lean_ctor_get(v_a_1879_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_a_1879_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1885_ = v_a_1879_;
v_isShared_1886_ = v_isSharedCheck_1911_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_val_1883_);
lean_dec(v_a_1879_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1911_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v_fst_1887_; lean_object* v_snd_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v_fst_1887_ = lean_ctor_get(v_val_1883_, 0);
lean_inc(v_fst_1887_);
v_snd_1888_ = lean_ctor_get(v_val_1883_, 1);
lean_inc(v_snd_1888_);
lean_dec(v_val_1883_);
v___x_1889_ = l_BitVec_toInt(v_fst_1887_, v_snd_1888_);
lean_dec(v_fst_1887_);
v___x_1890_ = l_Lean_mkIntLit(v___x_1889_);
lean_dec(v___x_1889_);
v___x_1891_ = l_Lean_Meta_Sym_shareCommon(v___x_1890_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1902_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1894_ = v___x_1891_;
v_isShared_1895_ = v_isSharedCheck_1902_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1891_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1902_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v_a_1892_);
v___x_1897_ = v___x_1885_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1899_; 
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___x_1897_);
v___x_1899_ = v___x_1894_;
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
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_del_object(v___x_1885_);
v_a_1903_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1891_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1891_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1914_; 
lean_dec(v_a_1879_);
v___x_1912_ = lean_box(0);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v___x_1912_);
v___x_1914_ = v___x_1881_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
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
v_a_1917_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1878_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1878_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToInt___lam__0___boxed(lean_object* v_r_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_Meta_Grind_propagateBVToInt___lam__0(v_r_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec(v___y_1926_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToInt(lean_object* v_e_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1955_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToInt___closed__1));
v___x_1956_ = lean_unsigned_to_nat(2u);
v___x_1957_ = l_Lean_Expr_isAppOfArity(v_e_1943_, v___x_1955_, v___x_1956_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
lean_dec_ref(v_e_1943_);
v___x_1958_ = lean_box(0);
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
return v___x_1959_;
}
else
{
lean_object* v___f_1960_; lean_object* v___x_1961_; 
v___f_1960_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToInt___closed__2));
v___x_1961_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1943_, v___f_1960_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
return v___x_1961_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToInt___boxed(lean_object* v_e_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_Meta_Grind_propagateBVToInt(v_e_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
lean_dec(v_a_1966_);
lean_dec_ref(v_a_1965_);
lean_dec(v_a_1964_);
lean_dec(v_a_1963_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToInt___regBuiltin_Lean_Meta_Grind_propagateBVToInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2998338308____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1976_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToInt___closed__1));
v___x_1977_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVToInt___boxed), 12, 0);
v___x_1978_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1976_, v___x_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToInt___regBuiltin_Lean_Meta_Grind_propagateBVToInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2998338308____hygCtx___hyg_9____boxed(lean_object* v_a_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToInt___regBuiltin_Lean_Meta_Grind_propagateBVToInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2998338308____hygCtx___hyg_9_();
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat___lam__0(lean_object* v_val_1981_, lean_object* v_r_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_Meta_getNatValue_x3f(v_r_1982_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2029_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2029_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2029_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
if (lean_obj_tag(v_a_1995_) == 1)
{
lean_object* v_val_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2024_; 
lean_del_object(v___x_1997_);
v_val_1999_ = lean_ctor_get(v_a_1995_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_a_1995_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2001_ = v_a_1995_;
v_isShared_2002_ = v_isSharedCheck_2024_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_val_1999_);
lean_dec(v_a_1995_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2024_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = l_BitVec_ofNat(v_val_1981_, v_val_1999_);
lean_dec(v_val_1999_);
v___x_2004_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_val_1981_, v___x_2003_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2015_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2015_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2015_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v_a_2005_);
v___x_2010_ = v___x_2001_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2010_);
v___x_2012_ = v___x_2007_;
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
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_del_object(v___x_2001_);
v_a_2016_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2004_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2004_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
else
{
lean_object* v___x_2025_; lean_object* v___x_2027_; 
lean_dec(v_a_1995_);
lean_dec(v_val_1981_);
v___x_2025_ = lean_box(0);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2025_);
v___x_2027_ = v___x_1997_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec(v_val_1981_);
v_a_2030_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_1994_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_1994_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat___lam__0___boxed(lean_object* v_val_2038_, lean_object* v_r_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_Meta_Grind_propagateBVOfNat___lam__0(v_val_2038_, v_r_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v_r_2039_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat(lean_object* v_e_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2068_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOfNat___closed__1));
v___x_2069_ = lean_unsigned_to_nat(2u);
v___x_2070_ = l_Lean_Expr_isAppOfArity(v_e_2056_, v___x_2068_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
lean_dec_ref(v_e_2056_);
v___x_2071_ = lean_box(0);
v___x_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
return v___x_2072_;
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2073_ = l_Lean_Expr_getAppNumArgs(v_e_2056_);
v___x_2074_ = lean_unsigned_to_nat(1u);
v___x_2075_ = lean_nat_sub(v___x_2073_, v___x_2074_);
lean_dec(v___x_2073_);
v___x_2076_ = l_Lean_Expr_getRevArg_x21(v_e_2056_, v___x_2075_);
v___x_2077_ = l_Lean_Meta_getNatValue_x3f(v___x_2076_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
lean_dec_ref(v___x_2076_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2094_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2080_ = v___x_2077_;
v_isShared_2081_ = v_isSharedCheck_2094_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2094_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
if (lean_obj_tag(v_a_2078_) == 1)
{
lean_object* v_val_2082_; uint8_t v___x_2083_; 
v_val_2082_ = lean_ctor_get(v_a_2078_, 0);
lean_inc(v_val_2082_);
lean_dec_ref_known(v_a_2078_, 1);
v___x_2083_ = l_Lean_isSafeBitVecWidth(v_val_2082_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
lean_dec(v_val_2082_);
lean_dec_ref(v_e_2056_);
v___x_2084_ = lean_box(0);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2084_);
v___x_2086_ = v___x_2080_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
else
{
lean_object* v___f_2088_; lean_object* v___x_2089_; 
lean_del_object(v___x_2080_);
v___f_2088_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVOfNat___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2088_, 0, v_val_2082_);
v___x_2089_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2056_, v___f_2088_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
return v___x_2089_;
}
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
lean_dec(v_a_2078_);
lean_dec_ref(v_e_2056_);
v___x_2090_ = lean_box(0);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2090_);
v___x_2092_ = v___x_2080_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec_ref(v_e_2056_);
v_a_2095_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2077_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2077_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat___boxed(lean_object* v_e_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Lean_Meta_Grind_propagateBVOfNat(v_e_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
lean_dec(v_a_2113_);
lean_dec_ref(v_a_2112_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec(v_a_2107_);
lean_dec_ref(v_a_2106_);
lean_dec(v_a_2105_);
lean_dec(v_a_2104_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1883179728____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOfNat___closed__1));
v___x_2118_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVOfNat___boxed), 12, 0);
v___x_2119_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2117_, v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1883179728____hygCtx___hyg_9____boxed(lean_object* v_a_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1883179728____hygCtx___hyg_9_();
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt___lam__0(lean_object* v_val_2122_, lean_object* v_r_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l_Lean_Meta_getIntValue_x3f(v_r_2123_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2170_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2170_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2170_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
if (lean_obj_tag(v_a_2136_) == 1)
{
lean_object* v_val_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2165_; 
lean_del_object(v___x_2138_);
v_val_2140_ = lean_ctor_get(v_a_2136_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_a_2136_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2142_ = v_a_2136_;
v_isShared_2143_ = v_isSharedCheck_2165_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_val_2140_);
lean_dec(v_a_2136_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2165_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = l_BitVec_ofInt(v_val_2122_, v_val_2140_);
lean_dec(v_val_2140_);
v___x_2145_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_val_2122_, v___x_2144_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2156_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2148_ = v___x_2145_;
v_isShared_2149_ = v_isSharedCheck_2156_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2145_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2156_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v_a_2146_);
v___x_2151_ = v___x_2142_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2153_; 
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2151_);
v___x_2153_ = v___x_2148_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2151_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_del_object(v___x_2142_);
v_a_2157_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2145_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2145_);
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
else
{
lean_object* v___x_2166_; lean_object* v___x_2168_; 
lean_dec(v_a_2136_);
lean_dec(v_val_2122_);
v___x_2166_ = lean_box(0);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2166_);
v___x_2168_ = v___x_2138_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec(v_val_2122_);
v_a_2171_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2135_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2135_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt___lam__0___boxed(lean_object* v_val_2179_, lean_object* v_r_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_Meta_Grind_propagateBVOfInt___lam__0(v_val_2179_, v_r_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec(v___y_2181_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt(lean_object* v_e_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; 
v___x_2209_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOfInt___closed__1));
v___x_2210_ = lean_unsigned_to_nat(2u);
v___x_2211_ = l_Lean_Expr_isAppOfArity(v_e_2197_, v___x_2209_, v___x_2210_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec_ref(v_e_2197_);
v___x_2212_ = lean_box(0);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
return v___x_2213_;
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2214_ = l_Lean_Expr_getAppNumArgs(v_e_2197_);
v___x_2215_ = lean_unsigned_to_nat(1u);
v___x_2216_ = lean_nat_sub(v___x_2214_, v___x_2215_);
lean_dec(v___x_2214_);
v___x_2217_ = l_Lean_Expr_getRevArg_x21(v_e_2197_, v___x_2216_);
v___x_2218_ = l_Lean_Meta_getNatValue_x3f(v___x_2217_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
lean_dec_ref(v___x_2217_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2235_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2221_ = v___x_2218_;
v_isShared_2222_ = v_isSharedCheck_2235_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2218_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2235_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
if (lean_obj_tag(v_a_2219_) == 1)
{
lean_object* v_val_2223_; uint8_t v___x_2224_; 
v_val_2223_ = lean_ctor_get(v_a_2219_, 0);
lean_inc(v_val_2223_);
lean_dec_ref_known(v_a_2219_, 1);
v___x_2224_ = l_Lean_isSafeBitVecWidth(v_val_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
lean_dec(v_val_2223_);
lean_dec_ref(v_e_2197_);
v___x_2225_ = lean_box(0);
if (v_isShared_2222_ == 0)
{
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
else
{
lean_object* v___f_2229_; lean_object* v___x_2230_; 
lean_del_object(v___x_2221_);
v___f_2229_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVOfInt___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2229_, 0, v_val_2223_);
v___x_2230_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2197_, v___f_2229_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
return v___x_2230_;
}
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
lean_dec(v_a_2219_);
lean_dec_ref(v_e_2197_);
v___x_2231_ = lean_box(0);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 0, v___x_2231_);
v___x_2233_ = v___x_2221_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
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
lean_dec_ref(v_e_2197_);
v_a_2236_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2218_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2218_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt___boxed(lean_object* v_e_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Meta_Grind_propagateBVOfInt(v_e_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec(v_a_2246_);
lean_dec(v_a_2245_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4268766526____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2258_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOfInt___closed__1));
v___x_2259_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVOfInt___boxed), 12, 0);
v___x_2260_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2258_, v___x_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4268766526____hygCtx___hyg_9____boxed(lean_object* v_a_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4268766526____hygCtx___hyg_9_();
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___lam__0(lean_object* v_val_2263_, lean_object* v_r_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = l_Lean_Meta_getBitVecValue_x3f(v_r_2264_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2313_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2279_ = v___x_2276_;
v_isShared_2280_ = v_isSharedCheck_2313_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2313_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
if (lean_obj_tag(v_a_2277_) == 1)
{
lean_object* v_val_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2308_; 
lean_del_object(v___x_2279_);
v_val_2281_ = lean_ctor_get(v_a_2277_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_a_2277_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2283_ = v_a_2277_;
v_isShared_2284_ = v_isSharedCheck_2308_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_val_2281_);
lean_dec(v_a_2277_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2308_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v_fst_2285_; lean_object* v_snd_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v_fst_2285_ = lean_ctor_get(v_val_2281_, 0);
lean_inc(v_fst_2285_);
v_snd_2286_ = lean_ctor_get(v_val_2281_, 1);
lean_inc(v_snd_2286_);
lean_dec(v_val_2281_);
v___x_2287_ = l_BitVec_setWidth(v_fst_2285_, v_val_2263_, v_snd_2286_);
lean_dec(v_snd_2286_);
lean_dec(v_fst_2285_);
v___x_2288_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_val_2263_, v___x_2287_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2299_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2299_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2299_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v_a_2289_);
v___x_2294_ = v___x_2283_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
lean_object* v___x_2296_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2294_);
v___x_2296_ = v___x_2291_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_del_object(v___x_2283_);
v_a_2300_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2288_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2288_);
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
lean_object* v___x_2309_; lean_object* v___x_2311_; 
lean_dec(v_a_2277_);
lean_dec(v_val_2263_);
v___x_2309_ = lean_box(0);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2309_);
v___x_2311_ = v___x_2279_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec(v_val_2263_);
v_a_2314_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2276_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2276_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___lam__0___boxed(lean_object* v_val_2322_, lean_object* v_r_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_Meta_Grind_propagateBVSetWidth___lam__0(v_val_2322_, v_r_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec(v___y_2324_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth(lean_object* v_e_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2352_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSetWidth___closed__1));
v___x_2353_ = lean_unsigned_to_nat(3u);
v___x_2354_ = l_Lean_Expr_isAppOfArity(v_e_2340_, v___x_2352_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
lean_dec_ref(v_e_2340_);
v___x_2355_ = lean_box(0);
v___x_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
return v___x_2356_;
}
else
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2357_ = lean_unsigned_to_nat(1u);
v___x_2358_ = l_Lean_Expr_getAppNumArgs(v_e_2340_);
v___x_2359_ = lean_nat_sub(v___x_2358_, v___x_2357_);
lean_dec(v___x_2358_);
v___x_2360_ = lean_nat_sub(v___x_2359_, v___x_2357_);
lean_dec(v___x_2359_);
v___x_2361_ = l_Lean_Expr_getRevArg_x21(v_e_2340_, v___x_2360_);
v___x_2362_ = l_Lean_Meta_getNatValue_x3f(v___x_2361_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_);
lean_dec_ref(v___x_2361_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2379_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2379_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2379_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
if (lean_obj_tag(v_a_2363_) == 1)
{
lean_object* v_val_2367_; uint8_t v___x_2368_; 
v_val_2367_ = lean_ctor_get(v_a_2363_, 0);
lean_inc(v_val_2367_);
lean_dec_ref_known(v_a_2363_, 1);
v___x_2368_ = l_Lean_isSafeBitVecWidth(v_val_2367_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; lean_object* v___x_2371_; 
lean_dec(v_val_2367_);
lean_dec_ref(v_e_2340_);
v___x_2369_ = lean_box(0);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2369_);
v___x_2371_ = v___x_2365_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
else
{
lean_object* v___f_2373_; lean_object* v___x_2374_; 
lean_del_object(v___x_2365_);
v___f_2373_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVSetWidth___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2373_, 0, v_val_2367_);
v___x_2374_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2340_, v___f_2373_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_);
return v___x_2374_;
}
}
else
{
lean_object* v___x_2375_; lean_object* v___x_2377_; 
lean_dec(v_a_2363_);
lean_dec_ref(v_e_2340_);
v___x_2375_ = lean_box(0);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2375_);
v___x_2377_ = v___x_2365_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec_ref(v_e_2340_);
v_a_2380_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2362_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2362_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___boxed(lean_object* v_e_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lean_Meta_Grind_propagateBVSetWidth(v_e_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec(v_a_2389_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2402_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSetWidth___closed__1));
v___x_2403_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVSetWidth___boxed), 12, 0);
v___x_2404_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2402_, v___x_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_9____boxed(lean_object* v_a_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_9_();
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___lam__0(lean_object* v_val_2407_, lean_object* v_r_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_Meta_getBitVecValue_x3f(v_r_2408_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2457_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2423_ = v___x_2420_;
v_isShared_2424_ = v_isSharedCheck_2457_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2420_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2457_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
if (lean_obj_tag(v_a_2421_) == 1)
{
lean_object* v_val_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2452_; 
lean_del_object(v___x_2423_);
v_val_2425_ = lean_ctor_get(v_a_2421_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_a_2421_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2427_ = v_a_2421_;
v_isShared_2428_ = v_isSharedCheck_2452_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_val_2425_);
lean_dec(v_a_2421_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2452_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v_fst_2429_; lean_object* v_snd_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v_fst_2429_ = lean_ctor_get(v_val_2425_, 0);
lean_inc(v_fst_2429_);
v_snd_2430_ = lean_ctor_get(v_val_2425_, 1);
lean_inc(v_snd_2430_);
lean_dec(v_val_2425_);
v___x_2431_ = l_BitVec_signExtend(v_fst_2429_, v_val_2407_, v_snd_2430_);
lean_dec(v_fst_2429_);
v___x_2432_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_val_2407_, v___x_2431_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2443_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2435_ = v___x_2432_;
v_isShared_2436_ = v_isSharedCheck_2443_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2443_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v_a_2433_);
v___x_2438_ = v___x_2427_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
lean_object* v___x_2440_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2438_);
v___x_2440_ = v___x_2435_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_del_object(v___x_2427_);
v_a_2444_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2432_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2432_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
}
else
{
lean_object* v___x_2453_; lean_object* v___x_2455_; 
lean_dec(v_a_2421_);
lean_dec(v_val_2407_);
v___x_2453_ = lean_box(0);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2453_);
v___x_2455_ = v___x_2423_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
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
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec(v_val_2407_);
v_a_2458_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2420_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2420_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___lam__0___boxed(lean_object* v_val_2466_, lean_object* v_r_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lean_Meta_Grind_propagateBVSignExtend___lam__0(v_val_2466_, v_r_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec(v___y_2468_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend(lean_object* v_e_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; 
v___x_2496_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSignExtend___closed__1));
v___x_2497_ = lean_unsigned_to_nat(3u);
v___x_2498_ = l_Lean_Expr_isAppOfArity(v_e_2484_, v___x_2496_, v___x_2497_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_dec_ref(v_e_2484_);
v___x_2499_ = lean_box(0);
v___x_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
return v___x_2500_;
}
else
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2501_ = lean_unsigned_to_nat(1u);
v___x_2502_ = l_Lean_Expr_getAppNumArgs(v_e_2484_);
v___x_2503_ = lean_nat_sub(v___x_2502_, v___x_2501_);
lean_dec(v___x_2502_);
v___x_2504_ = lean_nat_sub(v___x_2503_, v___x_2501_);
lean_dec(v___x_2503_);
v___x_2505_ = l_Lean_Expr_getRevArg_x21(v_e_2484_, v___x_2504_);
v___x_2506_ = l_Lean_Meta_getNatValue_x3f(v___x_2505_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
lean_dec_ref(v___x_2505_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2523_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2509_ = v___x_2506_;
v_isShared_2510_ = v_isSharedCheck_2523_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2506_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2523_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
if (lean_obj_tag(v_a_2507_) == 1)
{
lean_object* v_val_2511_; uint8_t v___x_2512_; 
v_val_2511_ = lean_ctor_get(v_a_2507_, 0);
lean_inc(v_val_2511_);
lean_dec_ref_known(v_a_2507_, 1);
v___x_2512_ = l_Lean_isSafeBitVecWidth(v_val_2511_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2515_; 
lean_dec(v_val_2511_);
lean_dec_ref(v_e_2484_);
v___x_2513_ = lean_box(0);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 0, v___x_2513_);
v___x_2515_ = v___x_2509_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
else
{
lean_object* v___f_2517_; lean_object* v___x_2518_; 
lean_del_object(v___x_2509_);
v___f_2517_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVSignExtend___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2517_, 0, v_val_2511_);
v___x_2518_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2484_, v___f_2517_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
return v___x_2518_;
}
}
else
{
lean_object* v___x_2519_; lean_object* v___x_2521_; 
lean_dec(v_a_2507_);
lean_dec_ref(v_e_2484_);
v___x_2519_ = lean_box(0);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 0, v___x_2519_);
v___x_2521_ = v___x_2509_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec_ref(v_e_2484_);
v_a_2524_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2506_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2506_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___boxed(lean_object* v_e_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_Meta_Grind_propagateBVSignExtend(v_e_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
lean_dec(v_a_2534_);
lean_dec(v_a_2533_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2546_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSignExtend___closed__1));
v___x_2547_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVSignExtend___boxed), 12, 0);
v___x_2548_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2546_, v___x_2547_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_9____boxed(lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_9_();
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0(lean_object* v_val_2551_, lean_object* v_val_2552_, lean_object* v_r_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_Meta_getBitVecValue_x3f(v_r_2553_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2601_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2601_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2601_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
if (lean_obj_tag(v_a_2566_) == 1)
{
lean_object* v_val_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2596_; 
lean_del_object(v___x_2568_);
v_val_2570_ = lean_ctor_get(v_a_2566_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v_a_2566_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2572_ = v_a_2566_;
v_isShared_2573_ = v_isSharedCheck_2596_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_val_2570_);
lean_dec(v_a_2566_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2596_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v_snd_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v_snd_2574_ = lean_ctor_get(v_val_2570_, 1);
lean_inc(v_snd_2574_);
lean_dec(v_val_2570_);
v___x_2575_ = l_BitVec_extractLsb_x27___redArg(v_val_2551_, v_val_2552_, v_snd_2574_);
lean_dec(v_snd_2574_);
v___x_2576_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_val_2552_, v___x_2575_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2587_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2587_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2587_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v_a_2577_);
v___x_2582_ = v___x_2572_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2584_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2582_);
v___x_2584_ = v___x_2579_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_del_object(v___x_2572_);
v_a_2588_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2576_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2576_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2599_; 
lean_dec(v_a_2566_);
lean_dec(v_val_2552_);
v___x_2597_ = lean_box(0);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2597_);
v___x_2599_ = v___x_2568_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec(v_val_2552_);
v_a_2602_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2565_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2565_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0___boxed(lean_object* v_val_2610_, lean_object* v_val_2611_, lean_object* v_r_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0(v_val_2610_, v_val_2611_, v_r_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec(v_val_2610_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27(lean_object* v_e_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; 
v___x_2641_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__1));
v___x_2642_ = lean_unsigned_to_nat(4u);
v___x_2643_ = l_Lean_Expr_isAppOfArity(v_e_2629_, v___x_2641_, v___x_2642_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
lean_dec_ref(v_e_2629_);
v___x_2644_ = lean_box(0);
v___x_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
return v___x_2645_;
}
else
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2646_ = lean_unsigned_to_nat(1u);
v___x_2647_ = l_Lean_Expr_getAppNumArgs(v_e_2629_);
v___x_2648_ = lean_nat_sub(v___x_2647_, v___x_2646_);
v___x_2649_ = lean_nat_sub(v___x_2648_, v___x_2646_);
lean_dec(v___x_2648_);
v___x_2650_ = l_Lean_Expr_getRevArg_x21(v_e_2629_, v___x_2649_);
v___x_2651_ = l_Lean_Meta_getNatValue_x3f(v___x_2650_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_);
lean_dec_ref(v___x_2650_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2691_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2654_ = v___x_2651_;
v_isShared_2655_ = v_isSharedCheck_2691_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2651_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2691_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
if (lean_obj_tag(v_a_2652_) == 1)
{
lean_object* v_val_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
lean_del_object(v___x_2654_);
v_val_2656_ = lean_ctor_get(v_a_2652_, 0);
lean_inc(v_val_2656_);
lean_dec_ref_known(v_a_2652_, 1);
v___x_2657_ = lean_unsigned_to_nat(2u);
v___x_2658_ = lean_nat_sub(v___x_2647_, v___x_2657_);
lean_dec(v___x_2647_);
v___x_2659_ = lean_nat_sub(v___x_2658_, v___x_2646_);
lean_dec(v___x_2658_);
v___x_2660_ = l_Lean_Expr_getRevArg_x21(v_e_2629_, v___x_2659_);
v___x_2661_ = l_Lean_Meta_getNatValue_x3f(v___x_2660_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_);
lean_dec_ref(v___x_2660_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2678_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2664_ = v___x_2661_;
v_isShared_2665_ = v_isSharedCheck_2678_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2661_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2678_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
if (lean_obj_tag(v_a_2662_) == 1)
{
lean_object* v_val_2666_; uint8_t v___x_2667_; 
v_val_2666_ = lean_ctor_get(v_a_2662_, 0);
lean_inc(v_val_2666_);
lean_dec_ref_known(v_a_2662_, 1);
v___x_2667_ = l_Lean_isSafeBitVecWidth(v_val_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
lean_dec(v_val_2666_);
lean_dec(v_val_2656_);
lean_dec_ref(v_e_2629_);
v___x_2668_ = lean_box(0);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v___x_2668_);
v___x_2670_ = v___x_2664_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
else
{
lean_object* v___f_2672_; lean_object* v___x_2673_; 
lean_del_object(v___x_2664_);
v___f_2672_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0___boxed), 14, 2);
lean_closure_set(v___f_2672_, 0, v_val_2656_);
lean_closure_set(v___f_2672_, 1, v_val_2666_);
v___x_2673_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2629_, v___f_2672_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_);
return v___x_2673_;
}
}
else
{
lean_object* v___x_2674_; lean_object* v___x_2676_; 
lean_dec(v_a_2662_);
lean_dec(v_val_2656_);
lean_dec_ref(v_e_2629_);
v___x_2674_ = lean_box(0);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v___x_2674_);
v___x_2676_ = v___x_2664_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_dec(v_val_2656_);
lean_dec_ref(v_e_2629_);
v_a_2679_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2661_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2661_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
else
{
lean_object* v___x_2687_; lean_object* v___x_2689_; 
lean_dec(v_a_2652_);
lean_dec(v___x_2647_);
lean_dec_ref(v_e_2629_);
v___x_2687_ = lean_box(0);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 0, v___x_2687_);
v___x_2689_ = v___x_2654_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec(v___x_2647_);
lean_dec_ref(v_e_2629_);
v_a_2692_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2651_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2651_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___boxed(lean_object* v_e_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Lean_Meta_Grind_propagateBVExtractLsb_x27(v_e_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
lean_dec(v_a_2702_);
lean_dec(v_a_2701_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2693654335____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2714_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__1));
v___x_2715_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVExtractLsb_x27___boxed), 12, 0);
v___x_2716_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2714_, v___x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2693654335____hygCtx___hyg_9____boxed(lean_object* v_a_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2693654335____hygCtx___hyg_9_();
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0(lean_object* v_val_2719_, lean_object* v_val_2720_, lean_object* v___x_2721_, lean_object* v_r_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Lean_Meta_getBitVecValue_x3f(v_r_2722_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2770_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2737_ = v___x_2734_;
v_isShared_2738_ = v_isSharedCheck_2770_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2770_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
if (lean_obj_tag(v_a_2735_) == 1)
{
lean_object* v_val_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2765_; 
lean_del_object(v___x_2737_);
v_val_2739_ = lean_ctor_get(v_a_2735_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v_a_2735_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2741_ = v_a_2735_;
v_isShared_2742_ = v_isSharedCheck_2765_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_val_2739_);
lean_dec(v_a_2735_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2765_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v_snd_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v_snd_2743_ = lean_ctor_get(v_val_2739_, 1);
lean_inc(v_snd_2743_);
lean_dec(v_val_2739_);
v___x_2744_ = l_BitVec_extractLsb___redArg(v_val_2719_, v_val_2720_, v_snd_2743_);
lean_dec(v_snd_2743_);
v___x_2745_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v___x_2721_, v___x_2744_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2756_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2748_ = v___x_2745_;
v_isShared_2749_ = v_isSharedCheck_2756_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2745_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2756_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v_a_2746_);
v___x_2751_ = v___x_2741_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
lean_object* v___x_2753_; 
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2751_);
v___x_2753_ = v___x_2748_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_del_object(v___x_2741_);
v_a_2757_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2745_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2745_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
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
}
}
else
{
lean_object* v___x_2766_; lean_object* v___x_2768_; 
lean_dec(v_a_2735_);
lean_dec(v___x_2721_);
v___x_2766_ = lean_box(0);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2766_);
v___x_2768_ = v___x_2737_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v___x_2721_);
v_a_2771_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2734_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2734_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0___boxed(lean_object* v_val_2779_, lean_object* v_val_2780_, lean_object* v___x_2781_, lean_object* v_r_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0(v_val_2779_, v_val_2780_, v___x_2781_, v_r_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec(v_val_2780_);
lean_dec(v_val_2779_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb(lean_object* v_e_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2811_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1));
v___x_2812_ = lean_unsigned_to_nat(4u);
v___x_2813_ = l_Lean_Expr_isAppOfArity(v_e_2799_, v___x_2811_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
lean_dec_ref(v_e_2799_);
v___x_2814_ = lean_box(0);
v___x_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
return v___x_2815_;
}
else
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2816_ = lean_unsigned_to_nat(1u);
v___x_2817_ = l_Lean_Expr_getAppNumArgs(v_e_2799_);
v___x_2818_ = lean_nat_sub(v___x_2817_, v___x_2816_);
v___x_2819_ = lean_nat_sub(v___x_2818_, v___x_2816_);
lean_dec(v___x_2818_);
v___x_2820_ = l_Lean_Expr_getRevArg_x21(v_e_2799_, v___x_2819_);
v___x_2821_ = l_Lean_Meta_getNatValue_x3f(v___x_2820_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
lean_dec_ref(v___x_2820_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2863_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2824_ = v___x_2821_;
v_isShared_2825_ = v_isSharedCheck_2863_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2821_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2863_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
if (lean_obj_tag(v_a_2822_) == 1)
{
lean_object* v_val_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_del_object(v___x_2824_);
v_val_2826_ = lean_ctor_get(v_a_2822_, 0);
lean_inc(v_val_2826_);
lean_dec_ref_known(v_a_2822_, 1);
v___x_2827_ = lean_unsigned_to_nat(2u);
v___x_2828_ = lean_nat_sub(v___x_2817_, v___x_2827_);
lean_dec(v___x_2817_);
v___x_2829_ = lean_nat_sub(v___x_2828_, v___x_2816_);
lean_dec(v___x_2828_);
v___x_2830_ = l_Lean_Expr_getRevArg_x21(v_e_2799_, v___x_2829_);
v___x_2831_ = l_Lean_Meta_getNatValue_x3f(v___x_2830_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
lean_dec_ref(v___x_2830_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2850_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2850_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2850_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
if (lean_obj_tag(v_a_2832_) == 1)
{
lean_object* v_val_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; uint8_t v___x_2839_; 
v_val_2836_ = lean_ctor_get(v_a_2832_, 0);
lean_inc(v_val_2836_);
lean_dec_ref_known(v_a_2832_, 1);
v___x_2837_ = lean_nat_sub(v_val_2826_, v_val_2836_);
v___x_2838_ = lean_nat_add(v___x_2837_, v___x_2816_);
lean_dec(v___x_2837_);
v___x_2839_ = l_Lean_isSafeBitVecWidth(v___x_2838_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; lean_object* v___x_2842_; 
lean_dec(v___x_2838_);
lean_dec(v_val_2836_);
lean_dec(v_val_2826_);
lean_dec_ref(v_e_2799_);
v___x_2840_ = lean_box(0);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2840_);
v___x_2842_ = v___x_2834_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2840_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
else
{
lean_object* v___f_2844_; lean_object* v___x_2845_; 
lean_del_object(v___x_2834_);
v___f_2844_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0___boxed), 15, 3);
lean_closure_set(v___f_2844_, 0, v_val_2826_);
lean_closure_set(v___f_2844_, 1, v_val_2836_);
lean_closure_set(v___f_2844_, 2, v___x_2838_);
v___x_2845_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2799_, v___f_2844_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
return v___x_2845_;
}
}
else
{
lean_object* v___x_2846_; lean_object* v___x_2848_; 
lean_dec(v_a_2832_);
lean_dec(v_val_2826_);
lean_dec_ref(v_e_2799_);
v___x_2846_ = lean_box(0);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2846_);
v___x_2848_ = v___x_2834_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2846_);
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
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec(v_val_2826_);
lean_dec_ref(v_e_2799_);
v_a_2851_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2831_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2831_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2861_; 
lean_dec(v_a_2822_);
lean_dec(v___x_2817_);
lean_dec_ref(v_e_2799_);
v___x_2859_ = lean_box(0);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v___x_2859_);
v___x_2861_ = v___x_2824_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2859_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v___x_2817_);
lean_dec_ref(v_e_2799_);
v_a_2864_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2821_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2821_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___boxed(lean_object* v_e_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_Meta_Grind_propagateBVExtractLsb(v_e_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
lean_dec(v_a_2882_);
lean_dec_ref(v_a_2881_);
lean_dec(v_a_2880_);
lean_dec_ref(v_a_2879_);
lean_dec(v_a_2878_);
lean_dec_ref(v_a_2877_);
lean_dec(v_a_2876_);
lean_dec_ref(v_a_2875_);
lean_dec(v_a_2874_);
lean_dec(v_a_2873_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2382349498____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2886_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1));
v___x_2887_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVExtractLsb___boxed), 12, 0);
v___x_2888_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2886_, v___x_2887_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2382349498____hygCtx___hyg_9____boxed(lean_object* v_a_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2382349498____hygCtx___hyg_9_();
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate___lam__0(lean_object* v_val_2891_, lean_object* v_r_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = l_Lean_Meta_getBitVecValue_x3f(v_r_2892_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2947_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2907_ = v___x_2904_;
v_isShared_2908_ = v_isSharedCheck_2947_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2904_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2947_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
if (lean_obj_tag(v_a_2905_) == 1)
{
lean_object* v_val_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2942_; 
v_val_2909_ = lean_ctor_get(v_a_2905_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v_a_2905_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2911_ = v_a_2905_;
v_isShared_2912_ = v_isSharedCheck_2942_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_val_2909_);
lean_dec(v_a_2905_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2942_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v_fst_2913_; lean_object* v_snd_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; 
v_fst_2913_ = lean_ctor_get(v_val_2909_, 0);
lean_inc(v_fst_2913_);
v_snd_2914_ = lean_ctor_get(v_val_2909_, 1);
lean_inc(v_snd_2914_);
lean_dec(v_val_2909_);
v___x_2915_ = lean_nat_mul(v_fst_2913_, v_val_2891_);
v___x_2916_ = l_Lean_isSafeBitVecWidth(v___x_2915_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; lean_object* v___x_2919_; 
lean_dec(v___x_2915_);
lean_dec(v_snd_2914_);
lean_dec(v_fst_2913_);
lean_del_object(v___x_2911_);
v___x_2917_ = lean_box(0);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v___x_2917_);
v___x_2919_ = v___x_2907_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2917_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
else
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_del_object(v___x_2907_);
v___x_2921_ = l_BitVec_replicate(v_fst_2913_, v_val_2891_, v_snd_2914_);
lean_dec(v_snd_2914_);
lean_dec(v_fst_2913_);
v___x_2922_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v___x_2915_, v___x_2921_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2933_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2925_ = v___x_2922_;
v_isShared_2926_ = v_isSharedCheck_2933_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2922_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2933_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 0, v_a_2923_);
v___x_2928_ = v___x_2911_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2930_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 0, v___x_2928_);
v___x_2930_ = v___x_2925_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2928_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_del_object(v___x_2911_);
v_a_2934_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2922_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2922_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
}
}
else
{
lean_object* v___x_2943_; lean_object* v___x_2945_; 
lean_dec(v_a_2905_);
v___x_2943_ = lean_box(0);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v___x_2943_);
v___x_2945_ = v___x_2907_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
v_a_2948_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2904_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2904_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate___lam__0___boxed(lean_object* v_val_2956_, lean_object* v_r_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_Meta_Grind_propagateBVReplicate___lam__0(v_val_2956_, v_r_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec(v_val_2956_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate(lean_object* v_e_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; 
v___x_2986_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVReplicate___closed__1));
v___x_2987_ = lean_unsigned_to_nat(3u);
v___x_2988_ = l_Lean_Expr_isAppOfArity(v_e_2974_, v___x_2986_, v___x_2987_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
lean_dec_ref(v_e_2974_);
v___x_2989_ = lean_box(0);
v___x_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
return v___x_2990_;
}
else
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2991_ = lean_unsigned_to_nat(1u);
v___x_2992_ = l_Lean_Expr_getAppNumArgs(v_e_2974_);
v___x_2993_ = lean_nat_sub(v___x_2992_, v___x_2991_);
lean_dec(v___x_2992_);
v___x_2994_ = lean_nat_sub(v___x_2993_, v___x_2991_);
lean_dec(v___x_2993_);
v___x_2995_ = l_Lean_Expr_getRevArg_x21(v_e_2974_, v___x_2994_);
v___x_2996_ = l_Lean_Meta_getNatValue_x3f(v___x_2995_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_);
lean_dec_ref(v___x_2995_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3008_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2999_ = v___x_2996_;
v_isShared_3000_ = v_isSharedCheck_3008_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2996_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3008_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
if (lean_obj_tag(v_a_2997_) == 1)
{
lean_object* v_val_3001_; lean_object* v___f_3002_; lean_object* v___x_3003_; 
lean_del_object(v___x_2999_);
v_val_3001_ = lean_ctor_get(v_a_2997_, 0);
lean_inc(v_val_3001_);
lean_dec_ref_known(v_a_2997_, 1);
v___f_3002_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVReplicate___lam__0___boxed), 13, 1);
lean_closure_set(v___f_3002_, 0, v_val_3001_);
v___x_3003_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2974_, v___f_3002_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_);
return v___x_3003_;
}
else
{
lean_object* v___x_3004_; lean_object* v___x_3006_; 
lean_dec(v_a_2997_);
lean_dec_ref(v_e_2974_);
v___x_3004_ = lean_box(0);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 0, v___x_3004_);
v___x_3006_ = v___x_2999_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec_ref(v_e_2974_);
v_a_3009_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_2996_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_2996_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate___boxed(lean_object* v_e_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_Meta_Grind_propagateBVReplicate(v_e_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
lean_dec(v_a_3027_);
lean_dec_ref(v_a_3026_);
lean_dec(v_a_3025_);
lean_dec_ref(v_a_3024_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec(v_a_3018_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_281236239____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3031_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVReplicate___closed__1));
v___x_3032_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVReplicate___boxed), 12, 0);
v___x_3033_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3031_, v___x_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_281236239____hygCtx___hyg_9____boxed(lean_object* v_a_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_281236239____hygCtx___hyg_9_();
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAnd___lam__0(lean_object* v_r_u2081_3036_, lean_object* v_r_u2082_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3036_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3112_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3052_ = v___x_3049_;
v_isShared_3053_ = v_isSharedCheck_3112_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3049_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3112_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
if (lean_obj_tag(v_a_3050_) == 1)
{
lean_object* v_val_3054_; lean_object* v_fst_3055_; lean_object* v_snd_3056_; lean_object* v___x_3057_; 
lean_del_object(v___x_3052_);
v_val_3054_ = lean_ctor_get(v_a_3050_, 0);
lean_inc(v_val_3054_);
lean_dec_ref_known(v_a_3050_, 1);
v_fst_3055_ = lean_ctor_get(v_val_3054_, 0);
lean_inc(v_fst_3055_);
v_snd_3056_ = lean_ctor_get(v_val_3054_, 1);
lean_inc(v_snd_3056_);
lean_dec(v_val_3054_);
v___x_3057_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_3037_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3099_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3099_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3099_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
if (lean_obj_tag(v_a_3058_) == 1)
{
lean_object* v_val_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3094_; 
v_val_3062_ = lean_ctor_get(v_a_3058_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v_a_3058_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3064_ = v_a_3058_;
v_isShared_3065_ = v_isSharedCheck_3094_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_val_3062_);
lean_dec(v_a_3058_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3094_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v_fst_3066_; lean_object* v_snd_3067_; uint8_t v___x_3068_; 
v_fst_3066_ = lean_ctor_get(v_val_3062_, 0);
lean_inc(v_fst_3066_);
v_snd_3067_ = lean_ctor_get(v_val_3062_, 1);
lean_inc(v_snd_3067_);
lean_dec(v_val_3062_);
v___x_3068_ = lean_nat_dec_eq(v_fst_3055_, v_fst_3066_);
lean_dec(v_fst_3066_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; lean_object* v___x_3071_; 
lean_dec(v_snd_3067_);
lean_del_object(v___x_3064_);
lean_dec(v_snd_3056_);
lean_dec(v_fst_3055_);
v___x_3069_ = lean_box(0);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v___x_3069_);
v___x_3071_ = v___x_3060_;
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
else
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
lean_del_object(v___x_3060_);
v___x_3073_ = lean_nat_land(v_snd_3056_, v_snd_3067_);
lean_dec(v_snd_3067_);
lean_dec(v_snd_3056_);
v___x_3074_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3055_, v___x_3073_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3085_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3077_ = v___x_3074_;
v_isShared_3078_ = v_isSharedCheck_3085_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3074_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3085_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3065_ == 0)
{
lean_ctor_set(v___x_3064_, 0, v_a_3075_);
v___x_3080_ = v___x_3064_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
lean_object* v___x_3082_; 
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 0, v___x_3080_);
v___x_3082_ = v___x_3077_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_del_object(v___x_3064_);
v_a_3086_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3074_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3074_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
}
}
else
{
lean_object* v___x_3095_; lean_object* v___x_3097_; 
lean_dec(v_a_3058_);
lean_dec(v_snd_3056_);
lean_dec(v_fst_3055_);
v___x_3095_ = lean_box(0);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v___x_3095_);
v___x_3097_ = v___x_3060_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_dec(v_snd_3056_);
lean_dec(v_fst_3055_);
v_a_3100_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3057_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3057_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
else
{
lean_object* v___x_3108_; lean_object* v___x_3110_; 
lean_dec(v_a_3050_);
lean_dec_ref(v_r_u2082_3037_);
v___x_3108_ = lean_box(0);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 0, v___x_3108_);
v___x_3110_ = v___x_3052_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_dec_ref(v_r_u2082_3037_);
v_a_3113_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3049_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3049_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAnd___lam__0___boxed(lean_object* v_r_u2081_3121_, lean_object* v_r_u2082_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_Meta_Grind_propagateBVAnd___lam__0(v_r_u2081_3121_, v_r_u2082_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec(v___y_3123_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAnd(lean_object* v_e_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_){
_start:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; uint8_t v___x_3155_; 
v___x_3153_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAnd___closed__2));
v___x_3154_ = lean_unsigned_to_nat(6u);
v___x_3155_ = l_Lean_Expr_isAppOfArity(v_e_3141_, v___x_3153_, v___x_3154_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
lean_dec_ref(v_e_3141_);
v___x_3156_ = lean_box(0);
v___x_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
return v___x_3157_;
}
else
{
lean_object* v___f_3158_; lean_object* v___x_3159_; 
v___f_3158_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAnd___closed__3));
v___x_3159_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3141_, v___f_3158_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
return v___x_3159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAnd___boxed(lean_object* v_e_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_Meta_Grind_propagateBVAnd(v_e_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_);
lean_dec(v_a_3170_);
lean_dec_ref(v_a_3169_);
lean_dec(v_a_3168_);
lean_dec_ref(v_a_3167_);
lean_dec(v_a_3166_);
lean_dec_ref(v_a_3165_);
lean_dec(v_a_3164_);
lean_dec_ref(v_a_3163_);
lean_dec(v_a_3162_);
lean_dec(v_a_3161_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAnd___regBuiltin_Lean_Meta_Grind_propagateBVAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_317501673____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3174_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAnd___closed__2));
v___x_3175_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVAnd___boxed), 12, 0);
v___x_3176_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3174_, v___x_3175_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAnd___regBuiltin_Lean_Meta_Grind_propagateBVAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_317501673____hygCtx___hyg_9____boxed(lean_object* v_a_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAnd___regBuiltin_Lean_Meta_Grind_propagateBVAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_317501673____hygCtx___hyg_9_();
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOr___lam__0(lean_object* v_r_u2081_3179_, lean_object* v_r_u2082_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v___x_3192_; 
v___x_3192_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3179_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3255_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3195_ = v___x_3192_;
v_isShared_3196_ = v_isSharedCheck_3255_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3255_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
if (lean_obj_tag(v_a_3193_) == 1)
{
lean_object* v_val_3197_; lean_object* v_fst_3198_; lean_object* v_snd_3199_; lean_object* v___x_3200_; 
lean_del_object(v___x_3195_);
v_val_3197_ = lean_ctor_get(v_a_3193_, 0);
lean_inc(v_val_3197_);
lean_dec_ref_known(v_a_3193_, 1);
v_fst_3198_ = lean_ctor_get(v_val_3197_, 0);
lean_inc(v_fst_3198_);
v_snd_3199_ = lean_ctor_get(v_val_3197_, 1);
lean_inc(v_snd_3199_);
lean_dec(v_val_3197_);
v___x_3200_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_3180_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3242_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3203_ = v___x_3200_;
v_isShared_3204_ = v_isSharedCheck_3242_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3242_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
if (lean_obj_tag(v_a_3201_) == 1)
{
lean_object* v_val_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3237_; 
v_val_3205_ = lean_ctor_get(v_a_3201_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v_a_3201_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3207_ = v_a_3201_;
v_isShared_3208_ = v_isSharedCheck_3237_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_val_3205_);
lean_dec(v_a_3201_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3237_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v_fst_3209_; lean_object* v_snd_3210_; uint8_t v___x_3211_; 
v_fst_3209_ = lean_ctor_get(v_val_3205_, 0);
lean_inc(v_fst_3209_);
v_snd_3210_ = lean_ctor_get(v_val_3205_, 1);
lean_inc(v_snd_3210_);
lean_dec(v_val_3205_);
v___x_3211_ = lean_nat_dec_eq(v_fst_3198_, v_fst_3209_);
lean_dec(v_fst_3209_);
if (v___x_3211_ == 0)
{
lean_object* v___x_3212_; lean_object* v___x_3214_; 
lean_dec(v_snd_3210_);
lean_del_object(v___x_3207_);
lean_dec(v_snd_3199_);
lean_dec(v_fst_3198_);
v___x_3212_ = lean_box(0);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v___x_3212_);
v___x_3214_ = v___x_3203_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3212_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
else
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
lean_del_object(v___x_3203_);
v___x_3216_ = lean_nat_lor(v_snd_3199_, v_snd_3210_);
lean_dec(v_snd_3210_);
lean_dec(v_snd_3199_);
v___x_3217_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3198_, v___x_3216_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3228_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3220_ = v___x_3217_;
v_isShared_3221_ = v_isSharedCheck_3228_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3217_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3228_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 0, v_a_3218_);
v___x_3223_ = v___x_3207_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
lean_object* v___x_3225_; 
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 0, v___x_3223_);
v___x_3225_ = v___x_3220_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3223_);
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
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
lean_del_object(v___x_3207_);
v_a_3229_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3217_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3217_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3229_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
}
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3240_; 
lean_dec(v_a_3201_);
lean_dec(v_snd_3199_);
lean_dec(v_fst_3198_);
v___x_3238_ = lean_box(0);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v___x_3238_);
v___x_3240_ = v___x_3203_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
lean_dec(v_snd_3199_);
lean_dec(v_fst_3198_);
v_a_3243_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3200_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3200_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_a_3243_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
else
{
lean_object* v___x_3251_; lean_object* v___x_3253_; 
lean_dec(v_a_3193_);
lean_dec_ref(v_r_u2082_3180_);
v___x_3251_ = lean_box(0);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v___x_3251_);
v___x_3253_ = v___x_3195_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3251_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_dec_ref(v_r_u2082_3180_);
v_a_3256_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3192_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3192_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOr___lam__0___boxed(lean_object* v_r_u2081_3264_, lean_object* v_r_u2082_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_Lean_Meta_Grind_propagateBVOr___lam__0(v_r_u2081_3264_, v_r_u2082_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec(v___y_3266_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOr(lean_object* v_e_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; 
v___x_3296_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOr___closed__2));
v___x_3297_ = lean_unsigned_to_nat(6u);
v___x_3298_ = l_Lean_Expr_isAppOfArity(v_e_3284_, v___x_3296_, v___x_3297_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
lean_dec_ref(v_e_3284_);
v___x_3299_ = lean_box(0);
v___x_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
return v___x_3300_;
}
else
{
lean_object* v___f_3301_; lean_object* v___x_3302_; 
v___f_3301_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOr___closed__3));
v___x_3302_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3284_, v___f_3301_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
return v___x_3302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOr___boxed(lean_object* v_e_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_Lean_Meta_Grind_propagateBVOr(v_e_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
lean_dec(v_a_3313_);
lean_dec_ref(v_a_3312_);
lean_dec(v_a_3311_);
lean_dec_ref(v_a_3310_);
lean_dec(v_a_3309_);
lean_dec_ref(v_a_3308_);
lean_dec(v_a_3307_);
lean_dec_ref(v_a_3306_);
lean_dec(v_a_3305_);
lean_dec(v_a_3304_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOr___regBuiltin_Lean_Meta_Grind_propagateBVOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4272827602____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3317_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOr___closed__2));
v___x_3318_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVOr___boxed), 12, 0);
v___x_3319_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3317_, v___x_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOr___regBuiltin_Lean_Meta_Grind_propagateBVOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4272827602____hygCtx___hyg_9____boxed(lean_object* v_a_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOr___regBuiltin_Lean_Meta_Grind_propagateBVOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4272827602____hygCtx___hyg_9_();
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVXor___lam__0(lean_object* v_r_u2081_3322_, lean_object* v_r_u2082_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3322_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3398_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3338_ = v___x_3335_;
v_isShared_3339_ = v_isSharedCheck_3398_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3335_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3398_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
if (lean_obj_tag(v_a_3336_) == 1)
{
lean_object* v_val_3340_; lean_object* v_fst_3341_; lean_object* v_snd_3342_; lean_object* v___x_3343_; 
lean_del_object(v___x_3338_);
v_val_3340_ = lean_ctor_get(v_a_3336_, 0);
lean_inc(v_val_3340_);
lean_dec_ref_known(v_a_3336_, 1);
v_fst_3341_ = lean_ctor_get(v_val_3340_, 0);
lean_inc(v_fst_3341_);
v_snd_3342_ = lean_ctor_get(v_val_3340_, 1);
lean_inc(v_snd_3342_);
lean_dec(v_val_3340_);
v___x_3343_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_3323_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3385_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3346_ = v___x_3343_;
v_isShared_3347_ = v_isSharedCheck_3385_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3343_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3385_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
if (lean_obj_tag(v_a_3344_) == 1)
{
lean_object* v_val_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3380_; 
v_val_3348_ = lean_ctor_get(v_a_3344_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v_a_3344_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3350_ = v_a_3344_;
v_isShared_3351_ = v_isSharedCheck_3380_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_val_3348_);
lean_dec(v_a_3344_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3380_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v_fst_3352_; lean_object* v_snd_3353_; uint8_t v___x_3354_; 
v_fst_3352_ = lean_ctor_get(v_val_3348_, 0);
lean_inc(v_fst_3352_);
v_snd_3353_ = lean_ctor_get(v_val_3348_, 1);
lean_inc(v_snd_3353_);
lean_dec(v_val_3348_);
v___x_3354_ = lean_nat_dec_eq(v_fst_3341_, v_fst_3352_);
lean_dec(v_fst_3352_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; lean_object* v___x_3357_; 
lean_dec(v_snd_3353_);
lean_del_object(v___x_3350_);
lean_dec(v_snd_3342_);
lean_dec(v_fst_3341_);
v___x_3355_ = lean_box(0);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3355_);
v___x_3357_ = v___x_3346_;
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
else
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
lean_del_object(v___x_3346_);
v___x_3359_ = lean_nat_lxor(v_snd_3342_, v_snd_3353_);
lean_dec(v_snd_3353_);
lean_dec(v_snd_3342_);
v___x_3360_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3341_, v___x_3359_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3371_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3363_ = v___x_3360_;
v_isShared_3364_ = v_isSharedCheck_3371_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3360_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3371_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 0, v_a_3361_);
v___x_3366_ = v___x_3350_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3368_; 
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 0, v___x_3366_);
v___x_3368_ = v___x_3363_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3366_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
else
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3379_; 
lean_del_object(v___x_3350_);
v_a_3372_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3374_ = v___x_3360_;
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3360_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3377_; 
if (v_isShared_3375_ == 0)
{
v___x_3377_ = v___x_3374_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3372_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
}
}
else
{
lean_object* v___x_3381_; lean_object* v___x_3383_; 
lean_dec(v_a_3344_);
lean_dec(v_snd_3342_);
lean_dec(v_fst_3341_);
v___x_3381_ = lean_box(0);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3381_);
v___x_3383_ = v___x_3346_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
lean_dec(v_snd_3342_);
lean_dec(v_fst_3341_);
v_a_3386_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v___x_3343_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3343_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
else
{
lean_object* v___x_3394_; lean_object* v___x_3396_; 
lean_dec(v_a_3336_);
lean_dec_ref(v_r_u2082_3323_);
v___x_3394_ = lean_box(0);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 0, v___x_3394_);
v___x_3396_ = v___x_3338_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3394_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
else
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec_ref(v_r_u2082_3323_);
v_a_3399_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3335_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3335_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVXor___lam__0___boxed(lean_object* v_r_u2081_3407_, lean_object* v_r_u2082_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_Meta_Grind_propagateBVXor___lam__0(v_r_u2081_3407_, v_r_u2082_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec(v___y_3409_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVXor(lean_object* v_e_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_){
_start:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; uint8_t v___x_3441_; 
v___x_3439_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVXor___closed__2));
v___x_3440_ = lean_unsigned_to_nat(6u);
v___x_3441_ = l_Lean_Expr_isAppOfArity(v_e_3427_, v___x_3439_, v___x_3440_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
lean_dec_ref(v_e_3427_);
v___x_3442_ = lean_box(0);
v___x_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
return v___x_3443_;
}
else
{
lean_object* v___f_3444_; lean_object* v___x_3445_; 
v___f_3444_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVXor___closed__3));
v___x_3445_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3427_, v___f_3444_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
return v___x_3445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVXor___boxed(lean_object* v_e_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Lean_Meta_Grind_propagateBVXor(v_e_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec_ref(v_a_3453_);
lean_dec(v_a_3452_);
lean_dec_ref(v_a_3451_);
lean_dec(v_a_3450_);
lean_dec_ref(v_a_3449_);
lean_dec(v_a_3448_);
lean_dec(v_a_3447_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVXor___regBuiltin_Lean_Meta_Grind_propagateBVXor_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1120302969____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3460_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVXor___closed__2));
v___x_3461_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVXor___boxed), 12, 0);
v___x_3462_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3460_, v___x_3461_);
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVXor___regBuiltin_Lean_Meta_Grind_propagateBVXor_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1120302969____hygCtx___hyg_9____boxed(lean_object* v_a_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVXor___regBuiltin_Lean_Meta_Grind_propagateBVXor_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1120302969____hygCtx___hyg_9_();
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAppend___lam__0(lean_object* v_r_u2081_3465_, lean_object* v_r_u2082_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3465_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3542_; 
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3481_ = v___x_3478_;
v_isShared_3482_ = v_isSharedCheck_3542_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3478_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3542_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
if (lean_obj_tag(v_a_3479_) == 1)
{
lean_object* v_val_3483_; lean_object* v_fst_3484_; lean_object* v_snd_3485_; lean_object* v___x_3486_; 
lean_del_object(v___x_3481_);
v_val_3483_ = lean_ctor_get(v_a_3479_, 0);
lean_inc(v_val_3483_);
lean_dec_ref_known(v_a_3479_, 1);
v_fst_3484_ = lean_ctor_get(v_val_3483_, 0);
lean_inc(v_fst_3484_);
v_snd_3485_ = lean_ctor_get(v_val_3483_, 1);
lean_inc(v_snd_3485_);
lean_dec(v_val_3483_);
v___x_3486_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_3466_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3529_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3489_ = v___x_3486_;
v_isShared_3490_ = v_isSharedCheck_3529_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3486_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3529_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
if (lean_obj_tag(v_a_3487_) == 1)
{
lean_object* v_val_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3524_; 
v_val_3491_ = lean_ctor_get(v_a_3487_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v_a_3487_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3493_ = v_a_3487_;
v_isShared_3494_ = v_isSharedCheck_3524_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_val_3491_);
lean_dec(v_a_3487_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3524_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v_fst_3495_; lean_object* v_snd_3496_; lean_object* v___x_3497_; uint8_t v___x_3498_; 
v_fst_3495_ = lean_ctor_get(v_val_3491_, 0);
lean_inc(v_fst_3495_);
v_snd_3496_ = lean_ctor_get(v_val_3491_, 1);
lean_inc(v_snd_3496_);
lean_dec(v_val_3491_);
v___x_3497_ = lean_nat_add(v_fst_3484_, v_fst_3495_);
lean_dec(v_fst_3484_);
v___x_3498_ = l_Lean_isSafeBitVecWidth(v___x_3497_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; lean_object* v___x_3501_; 
lean_dec(v___x_3497_);
lean_dec(v_snd_3496_);
lean_dec(v_fst_3495_);
lean_del_object(v___x_3493_);
lean_dec(v_snd_3485_);
v___x_3499_ = lean_box(0);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v___x_3499_);
v___x_3501_ = v___x_3489_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
else
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
lean_del_object(v___x_3489_);
v___x_3503_ = l_BitVec_append___redArg(v_fst_3495_, v_snd_3485_, v_snd_3496_);
lean_dec(v_snd_3496_);
lean_dec(v_snd_3485_);
lean_dec(v_fst_3495_);
v___x_3504_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v___x_3497_, v___x_3503_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3515_; 
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3507_ = v___x_3504_;
v_isShared_3508_ = v_isSharedCheck_3515_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3504_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3515_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v_a_3505_);
v___x_3510_ = v___x_3493_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
lean_object* v___x_3512_; 
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 0, v___x_3510_);
v___x_3512_ = v___x_3507_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3510_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_del_object(v___x_3493_);
v_a_3516_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3504_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3504_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
}
}
else
{
lean_object* v___x_3525_; lean_object* v___x_3527_; 
lean_dec(v_a_3487_);
lean_dec(v_snd_3485_);
lean_dec(v_fst_3484_);
v___x_3525_ = lean_box(0);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v___x_3525_);
v___x_3527_ = v___x_3489_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
else
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3537_; 
lean_dec(v_snd_3485_);
lean_dec(v_fst_3484_);
v_a_3530_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3532_ = v___x_3486_;
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3486_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3535_; 
if (v_isShared_3533_ == 0)
{
v___x_3535_ = v___x_3532_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3530_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
else
{
lean_object* v___x_3538_; lean_object* v___x_3540_; 
lean_dec(v_a_3479_);
lean_dec_ref(v_r_u2082_3466_);
v___x_3538_ = lean_box(0);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 0, v___x_3538_);
v___x_3540_ = v___x_3481_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3538_);
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
lean_dec_ref(v_r_u2082_3466_);
v_a_3543_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3478_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3478_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAppend___lam__0___boxed(lean_object* v_r_u2081_3551_, lean_object* v_r_u2082_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l_Lean_Meta_Grind_propagateBVAppend___lam__0(v_r_u2081_3551_, v_r_u2082_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec(v___y_3553_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAppend(lean_object* v_e_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; uint8_t v___x_3585_; 
v___x_3583_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAppend___closed__2));
v___x_3584_ = lean_unsigned_to_nat(6u);
v___x_3585_ = l_Lean_Expr_isAppOfArity(v_e_3571_, v___x_3583_, v___x_3584_);
if (v___x_3585_ == 0)
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
lean_dec_ref(v_e_3571_);
v___x_3586_ = lean_box(0);
v___x_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
return v___x_3587_;
}
else
{
lean_object* v___f_3588_; lean_object* v___x_3589_; 
v___f_3588_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAppend___closed__3));
lean_inc(v_a_3581_);
lean_inc_ref(v_a_3580_);
lean_inc(v_a_3579_);
lean_inc_ref(v_a_3578_);
lean_inc_ref(v_e_3571_);
v___x_3589_ = lean_infer_type(v_e_3571_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3601_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3592_ = v___x_3589_;
v_isShared_3593_ = v_isSharedCheck_3601_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3589_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3601_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3594_; uint8_t v___x_3595_; 
v___x_3594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__1));
v___x_3595_ = l_Lean_Expr_isAppOf(v_a_3590_, v___x_3594_);
lean_dec(v_a_3590_);
if (v___x_3595_ == 0)
{
lean_object* v___x_3596_; lean_object* v___x_3598_; 
lean_dec_ref(v_e_3571_);
v___x_3596_ = lean_box(0);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v___x_3596_);
v___x_3598_ = v___x_3592_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3596_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
else
{
lean_object* v___x_3600_; 
lean_del_object(v___x_3592_);
v___x_3600_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3571_, v___f_3588_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
return v___x_3600_;
}
}
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
lean_dec_ref(v_e_3571_);
v_a_3602_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3589_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3589_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAppend___boxed(lean_object* v_e_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_Meta_Grind_propagateBVAppend(v_e_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_);
lean_dec(v_a_3620_);
lean_dec_ref(v_a_3619_);
lean_dec(v_a_3618_);
lean_dec_ref(v_a_3617_);
lean_dec(v_a_3616_);
lean_dec_ref(v_a_3615_);
lean_dec(v_a_3614_);
lean_dec_ref(v_a_3613_);
lean_dec(v_a_3612_);
lean_dec(v_a_3611_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1194477106____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3624_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAppend___closed__2));
v___x_3625_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVAppend___boxed), 12, 0);
v___x_3626_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3624_, v___x_3625_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1194477106____hygCtx___hyg_9____boxed(lean_object* v_a_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1194477106____hygCtx___hyg_9_();
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___lam__0(uint8_t v___x_3629_, lean_object* v_r_u2081_3630_, lean_object* v_r_u2082_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v___x_3643_; 
v___x_3643_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3630_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3718_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3646_ = v___x_3643_;
v_isShared_3647_ = v_isSharedCheck_3718_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3643_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3718_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
if (lean_obj_tag(v_a_3644_) == 1)
{
lean_object* v_val_3648_; lean_object* v_fst_3649_; lean_object* v_snd_3650_; lean_object* v___x_3651_; 
lean_del_object(v___x_3646_);
v_val_3648_ = lean_ctor_get(v_a_3644_, 0);
lean_inc(v_val_3648_);
lean_dec_ref_known(v_a_3644_, 1);
v_fst_3649_ = lean_ctor_get(v_val_3648_, 0);
lean_inc(v_fst_3649_);
v_snd_3650_ = lean_ctor_get(v_val_3648_, 1);
lean_inc(v_snd_3650_);
lean_dec(v_val_3648_);
v___x_3651_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_3631_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3705_; 
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3654_ = v___x_3651_;
v_isShared_3655_ = v_isSharedCheck_3705_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3651_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3705_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
if (lean_obj_tag(v_a_3652_) == 1)
{
lean_object* v_val_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3700_; 
lean_del_object(v___x_3654_);
v_val_3656_ = lean_ctor_get(v_a_3652_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v_a_3652_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3658_ = v_a_3652_;
v_isShared_3659_ = v_isSharedCheck_3700_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_val_3656_);
lean_dec(v_a_3652_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3700_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3660_; 
lean_inc(v_val_3656_);
v___x_3660_ = l_Lean_checkShiftLeft(v_snd_3650_, v_val_3656_, v___x_3629_, v___y_3640_, v___y_3641_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3691_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3663_ = v___x_3660_;
v_isShared_3664_ = v_isSharedCheck_3691_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3660_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3691_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
uint8_t v___x_3665_; 
v___x_3665_ = lean_unbox(v_a_3661_);
lean_dec(v_a_3661_);
if (v___x_3665_ == 0)
{
lean_object* v___x_3666_; lean_object* v___x_3668_; 
lean_del_object(v___x_3658_);
lean_dec(v_val_3656_);
lean_dec(v_snd_3650_);
lean_dec(v_fst_3649_);
v___x_3666_ = lean_box(0);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 0, v___x_3666_);
v___x_3668_ = v___x_3663_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3666_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
else
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
lean_del_object(v___x_3663_);
v___x_3670_ = l_BitVec_shiftLeft(v_fst_3649_, v_snd_3650_, v_val_3656_);
lean_dec(v_val_3656_);
lean_dec(v_snd_3650_);
v___x_3671_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3649_, v___x_3670_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3682_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3674_ = v___x_3671_;
v_isShared_3675_ = v_isSharedCheck_3682_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3671_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3682_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 0, v_a_3672_);
v___x_3677_ = v___x_3658_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
lean_object* v___x_3679_; 
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 0, v___x_3677_);
v___x_3679_ = v___x_3674_;
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
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_del_object(v___x_3658_);
v_a_3683_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3671_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3671_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
}
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_del_object(v___x_3658_);
lean_dec(v_val_3656_);
lean_dec(v_snd_3650_);
lean_dec(v_fst_3649_);
v_a_3692_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3660_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3660_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
}
else
{
lean_object* v___x_3701_; lean_object* v___x_3703_; 
lean_dec(v_a_3652_);
lean_dec(v_snd_3650_);
lean_dec(v_fst_3649_);
v___x_3701_ = lean_box(0);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 0, v___x_3701_);
v___x_3703_ = v___x_3654_;
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
}
}
else
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
lean_dec(v_snd_3650_);
lean_dec(v_fst_3649_);
v_a_3706_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___x_3651_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3651_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
else
{
lean_object* v___x_3714_; lean_object* v___x_3716_; 
lean_dec(v_a_3644_);
v___x_3714_ = lean_box(0);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v___x_3714_);
v___x_3716_ = v___x_3646_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3714_);
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
v_a_3719_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3721_ = v___x_3643_;
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3643_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___lam__0___boxed(lean_object* v___x_3727_, lean_object* v_r_u2081_3728_, lean_object* v_r_u2082_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
uint8_t v___x_138__boxed_3741_; lean_object* v_res_3742_; 
v___x_138__boxed_3741_ = lean_unbox(v___x_3727_);
v_res_3742_ = l_Lean_Meta_Grind_propagateBVShiftLeft___lam__0(v___x_138__boxed_3741_, v_r_u2081_3728_, v_r_u2082_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v___y_3731_);
lean_dec(v___y_3730_);
lean_dec_ref(v_r_u2082_3729_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft(lean_object* v_e_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_){
_start:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; uint8_t v___x_3761_; 
v___x_3759_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVShiftLeft___closed__1));
v___x_3760_ = lean_unsigned_to_nat(3u);
v___x_3761_ = l_Lean_Expr_isAppOfArity(v_e_3747_, v___x_3759_, v___x_3760_);
if (v___x_3761_ == 0)
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
lean_dec_ref(v_e_3747_);
v___x_3762_ = lean_box(0);
v___x_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
return v___x_3763_;
}
else
{
lean_object* v___x_3764_; lean_object* v___f_3765_; lean_object* v___x_3766_; 
v___x_3764_ = lean_box(v___x_3761_);
v___f_3765_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVShiftLeft___lam__0___boxed), 14, 1);
lean_closure_set(v___f_3765_, 0, v___x_3764_);
v___x_3766_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3747_, v___f_3765_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_, v_a_3755_, v_a_3756_, v_a_3757_);
return v___x_3766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___boxed(lean_object* v_e_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_){
_start:
{
lean_object* v_res_3779_; 
v_res_3779_ = l_Lean_Meta_Grind_propagateBVShiftLeft(v_e_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
lean_dec(v_a_3777_);
lean_dec_ref(v_a_3776_);
lean_dec(v_a_3775_);
lean_dec_ref(v_a_3774_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec(v_a_3768_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3514232501____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3781_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVShiftLeft___closed__1));
v___x_3782_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVShiftLeft___boxed), 12, 0);
v___x_3783_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3781_, v___x_3782_);
return v___x_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3514232501____hygCtx___hyg_9____boxed(lean_object* v_a_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3514232501____hygCtx___hyg_9_();
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight___lam__0(lean_object* v_r_u2081_3786_, lean_object* v_r_u2082_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3786_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3855_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3802_ = v___x_3799_;
v_isShared_3803_ = v_isSharedCheck_3855_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3799_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3855_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
if (lean_obj_tag(v_a_3800_) == 1)
{
lean_object* v_val_3804_; lean_object* v_fst_3805_; lean_object* v_snd_3806_; lean_object* v___x_3807_; 
lean_del_object(v___x_3802_);
v_val_3804_ = lean_ctor_get(v_a_3800_, 0);
lean_inc(v_val_3804_);
lean_dec_ref_known(v_a_3800_, 1);
v_fst_3805_ = lean_ctor_get(v_val_3804_, 0);
lean_inc(v_fst_3805_);
v_snd_3806_ = lean_ctor_get(v_val_3804_, 1);
lean_inc(v_snd_3806_);
lean_dec(v_val_3804_);
v___x_3807_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_3787_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3842_; 
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3810_ = v___x_3807_;
v_isShared_3811_ = v_isSharedCheck_3842_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3807_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3842_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
if (lean_obj_tag(v_a_3808_) == 1)
{
lean_object* v_val_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3837_; 
lean_del_object(v___x_3810_);
v_val_3812_ = lean_ctor_get(v_a_3808_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_a_3808_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3814_ = v_a_3808_;
v_isShared_3815_ = v_isSharedCheck_3837_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_val_3812_);
lean_dec(v_a_3808_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3837_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; 
v___x_3816_ = lean_nat_shiftr(v_snd_3806_, v_val_3812_);
lean_dec(v_val_3812_);
lean_dec(v_snd_3806_);
v___x_3817_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3805_, v___x_3816_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3828_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3820_ = v___x_3817_;
v_isShared_3821_ = v_isSharedCheck_3828_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3817_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3828_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 0, v_a_3818_);
v___x_3823_ = v___x_3814_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
lean_object* v___x_3825_; 
if (v_isShared_3821_ == 0)
{
lean_ctor_set(v___x_3820_, 0, v___x_3823_);
v___x_3825_ = v___x_3820_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3823_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
lean_del_object(v___x_3814_);
v_a_3829_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3817_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3817_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
}
else
{
lean_object* v___x_3838_; lean_object* v___x_3840_; 
lean_dec(v_a_3808_);
lean_dec(v_snd_3806_);
lean_dec(v_fst_3805_);
v___x_3838_ = lean_box(0);
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 0, v___x_3838_);
v___x_3840_ = v___x_3810_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3838_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
lean_dec(v_snd_3806_);
lean_dec(v_fst_3805_);
v_a_3843_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3807_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3807_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
else
{
lean_object* v___x_3851_; lean_object* v___x_3853_; 
lean_dec(v_a_3800_);
v___x_3851_ = lean_box(0);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v___x_3851_);
v___x_3853_ = v___x_3802_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v___x_3851_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
else
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3863_; 
v_a_3856_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3858_ = v___x_3799_;
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3799_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight___lam__0___boxed(lean_object* v_r_u2081_3864_, lean_object* v_r_u2082_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Lean_Meta_Grind_propagateBVUShiftRight___lam__0(v_r_u2081_3864_, v_r_u2082_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v_r_u2082_3865_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight(lean_object* v_e_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_){
_start:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; uint8_t v___x_3897_; 
v___x_3895_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVUShiftRight___closed__1));
v___x_3896_ = lean_unsigned_to_nat(3u);
v___x_3897_ = l_Lean_Expr_isAppOfArity(v_e_3883_, v___x_3895_, v___x_3896_);
if (v___x_3897_ == 0)
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
lean_dec_ref(v_e_3883_);
v___x_3898_ = lean_box(0);
v___x_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
return v___x_3899_;
}
else
{
lean_object* v___f_3900_; lean_object* v___x_3901_; 
v___f_3900_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVUShiftRight___closed__2));
v___x_3901_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3883_, v___f_3900_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_);
return v___x_3901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight___boxed(lean_object* v_e_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l_Lean_Meta_Grind_propagateBVUShiftRight(v_e_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_);
lean_dec(v_a_3912_);
lean_dec_ref(v_a_3911_);
lean_dec(v_a_3910_);
lean_dec_ref(v_a_3909_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
lean_dec(v_a_3904_);
lean_dec(v_a_3903_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVUShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVUShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1878785357____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3916_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVUShiftRight___closed__1));
v___x_3917_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVUShiftRight___boxed), 12, 0);
v___x_3918_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3916_, v___x_3917_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVUShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVUShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1878785357____hygCtx___hyg_9____boxed(lean_object* v_a_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVUShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVUShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1878785357____hygCtx___hyg_9_();
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight___lam__0(lean_object* v_r_u2081_3921_, lean_object* v_r_u2082_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3921_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3990_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3990_ == 0)
{
v___x_3937_ = v___x_3934_;
v_isShared_3938_ = v_isSharedCheck_3990_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3934_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3990_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
if (lean_obj_tag(v_a_3935_) == 1)
{
lean_object* v_val_3939_; lean_object* v_fst_3940_; lean_object* v_snd_3941_; lean_object* v___x_3942_; 
lean_del_object(v___x_3937_);
v_val_3939_ = lean_ctor_get(v_a_3935_, 0);
lean_inc(v_val_3939_);
lean_dec_ref_known(v_a_3935_, 1);
v_fst_3940_ = lean_ctor_get(v_val_3939_, 0);
lean_inc(v_fst_3940_);
v_snd_3941_ = lean_ctor_get(v_val_3939_, 1);
lean_inc(v_snd_3941_);
lean_dec(v_val_3939_);
v___x_3942_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_3922_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3977_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3945_ = v___x_3942_;
v_isShared_3946_ = v_isSharedCheck_3977_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3942_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3977_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
if (lean_obj_tag(v_a_3943_) == 1)
{
lean_object* v_val_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3972_; 
lean_del_object(v___x_3945_);
v_val_3947_ = lean_ctor_get(v_a_3943_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v_a_3943_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3949_ = v_a_3943_;
v_isShared_3950_ = v_isSharedCheck_3972_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_val_3947_);
lean_dec(v_a_3943_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3972_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3951_ = l_BitVec_sshiftRight(v_fst_3940_, v_snd_3941_, v_val_3947_);
lean_dec(v_val_3947_);
v___x_3952_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3940_, v___x_3951_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3963_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3955_ = v___x_3952_;
v_isShared_3956_ = v_isSharedCheck_3963_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v___x_3952_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3963_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3958_; 
if (v_isShared_3950_ == 0)
{
lean_ctor_set(v___x_3949_, 0, v_a_3953_);
v___x_3958_ = v___x_3949_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3953_);
v___x_3958_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
lean_object* v___x_3960_; 
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 0, v___x_3958_);
v___x_3960_ = v___x_3955_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3958_);
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
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_del_object(v___x_3949_);
v_a_3964_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3952_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3952_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
}
else
{
lean_object* v___x_3973_; lean_object* v___x_3975_; 
lean_dec(v_a_3943_);
lean_dec(v_snd_3941_);
lean_dec(v_fst_3940_);
v___x_3973_ = lean_box(0);
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 0, v___x_3973_);
v___x_3975_ = v___x_3945_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3973_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
}
else
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
lean_dec(v_snd_3941_);
lean_dec(v_fst_3940_);
v_a_3978_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3942_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3942_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3978_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
else
{
lean_object* v___x_3986_; lean_object* v___x_3988_; 
lean_dec(v_a_3935_);
v___x_3986_ = lean_box(0);
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 0, v___x_3986_);
v___x_3988_ = v___x_3937_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___x_3986_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
return v___x_3988_;
}
}
}
}
else
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3998_; 
v_a_3991_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3993_ = v___x_3934_;
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3934_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3998_;
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
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3991_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight___lam__0___boxed(lean_object* v_r_u2081_3999_, lean_object* v_r_u2082_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
lean_object* v_res_4012_; 
v_res_4012_ = l_Lean_Meta_Grind_propagateBVSShiftRight___lam__0(v_r_u2081_3999_, v_r_u2082_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
lean_dec(v___y_4002_);
lean_dec(v___y_4001_);
lean_dec_ref(v_r_u2082_4000_);
return v_res_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight(lean_object* v_e_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_){
_start:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; uint8_t v___x_4032_; 
v___x_4030_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSShiftRight___closed__1));
v___x_4031_ = lean_unsigned_to_nat(3u);
v___x_4032_ = l_Lean_Expr_isAppOfArity(v_e_4018_, v___x_4030_, v___x_4031_);
if (v___x_4032_ == 0)
{
lean_object* v___x_4033_; lean_object* v___x_4034_; 
lean_dec_ref(v_e_4018_);
v___x_4033_ = lean_box(0);
v___x_4034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4033_);
return v___x_4034_;
}
else
{
lean_object* v___f_4035_; lean_object* v___x_4036_; 
v___f_4035_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSShiftRight___closed__2));
v___x_4036_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4018_, v___f_4035_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_);
return v___x_4036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight___boxed(lean_object* v_e_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l_Lean_Meta_Grind_propagateBVSShiftRight(v_e_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_);
lean_dec(v_a_4047_);
lean_dec_ref(v_a_4046_);
lean_dec(v_a_4045_);
lean_dec_ref(v_a_4044_);
lean_dec(v_a_4043_);
lean_dec_ref(v_a_4042_);
lean_dec(v_a_4041_);
lean_dec_ref(v_a_4040_);
lean_dec(v_a_4039_);
lean_dec(v_a_4038_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVSShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3342532823____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4051_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSShiftRight___closed__1));
v___x_4052_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVSShiftRight___boxed), 12, 0);
v___x_4053_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4051_, v___x_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVSShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3342532823____hygCtx___hyg_9____boxed(lean_object* v_a_4054_){
_start:
{
lean_object* v_res_4055_; 
v_res_4055_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVSShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3342532823____hygCtx___hyg_9_();
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft___lam__0(lean_object* v_r_u2081_4056_, lean_object* v_r_u2082_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v___x_4069_; 
v___x_4069_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4056_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4125_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4072_ = v___x_4069_;
v_isShared_4073_ = v_isSharedCheck_4125_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4069_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4125_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
if (lean_obj_tag(v_a_4070_) == 1)
{
lean_object* v_val_4074_; lean_object* v_fst_4075_; lean_object* v_snd_4076_; lean_object* v___x_4077_; 
lean_del_object(v___x_4072_);
v_val_4074_ = lean_ctor_get(v_a_4070_, 0);
lean_inc(v_val_4074_);
lean_dec_ref_known(v_a_4070_, 1);
v_fst_4075_ = lean_ctor_get(v_val_4074_, 0);
lean_inc(v_fst_4075_);
v_snd_4076_ = lean_ctor_get(v_val_4074_, 1);
lean_inc(v_snd_4076_);
lean_dec(v_val_4074_);
v___x_4077_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4057_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4112_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4080_ = v___x_4077_;
v_isShared_4081_ = v_isSharedCheck_4112_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4077_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4112_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
if (lean_obj_tag(v_a_4078_) == 1)
{
lean_object* v_val_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4107_; 
lean_del_object(v___x_4080_);
v_val_4082_ = lean_ctor_get(v_a_4078_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v_a_4078_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4084_ = v_a_4078_;
v_isShared_4085_ = v_isSharedCheck_4107_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_val_4082_);
lean_dec(v_a_4078_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4107_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4086_ = l_BitVec_rotateLeft(v_fst_4075_, v_snd_4076_, v_val_4082_);
lean_dec(v_val_4082_);
lean_dec(v_snd_4076_);
v___x_4087_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4075_, v___x_4086_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4098_; 
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4090_ = v___x_4087_;
v_isShared_4091_ = v_isSharedCheck_4098_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4087_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4098_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___x_4093_; 
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 0, v_a_4088_);
v___x_4093_ = v___x_4084_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4088_);
v___x_4093_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
lean_object* v___x_4095_; 
if (v_isShared_4091_ == 0)
{
lean_ctor_set(v___x_4090_, 0, v___x_4093_);
v___x_4095_ = v___x_4090_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4093_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
lean_del_object(v___x_4084_);
v_a_4099_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4087_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4087_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
}
else
{
lean_object* v___x_4108_; lean_object* v___x_4110_; 
lean_dec(v_a_4078_);
lean_dec(v_snd_4076_);
lean_dec(v_fst_4075_);
v___x_4108_ = lean_box(0);
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v___x_4108_);
v___x_4110_ = v___x_4080_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v___x_4108_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4120_; 
lean_dec(v_snd_4076_);
lean_dec(v_fst_4075_);
v_a_4113_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4115_ = v___x_4077_;
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4077_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4118_; 
if (v_isShared_4116_ == 0)
{
v___x_4118_ = v___x_4115_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4113_);
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
else
{
lean_object* v___x_4121_; lean_object* v___x_4123_; 
lean_dec(v_a_4070_);
v___x_4121_ = lean_box(0);
if (v_isShared_4073_ == 0)
{
lean_ctor_set(v___x_4072_, 0, v___x_4121_);
v___x_4123_ = v___x_4072_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v___x_4121_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
else
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4133_; 
v_a_4126_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4128_ = v___x_4069_;
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v___x_4069_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4126_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft___lam__0___boxed(lean_object* v_r_u2081_4134_, lean_object* v_r_u2082_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l_Lean_Meta_Grind_propagateBVRotateLeft___lam__0(v_r_u2081_4134_, v_r_u2082_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec(v___y_4139_);
lean_dec_ref(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec_ref(v_r_u2082_4135_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft(lean_object* v_e_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_){
_start:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; uint8_t v___x_4167_; 
v___x_4165_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateLeft___closed__1));
v___x_4166_ = lean_unsigned_to_nat(3u);
v___x_4167_ = l_Lean_Expr_isAppOfArity(v_e_4153_, v___x_4165_, v___x_4166_);
if (v___x_4167_ == 0)
{
lean_object* v___x_4168_; lean_object* v___x_4169_; 
lean_dec_ref(v_e_4153_);
v___x_4168_ = lean_box(0);
v___x_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
return v___x_4169_;
}
else
{
lean_object* v___f_4170_; lean_object* v___x_4171_; 
v___f_4170_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateLeft___closed__2));
v___x_4171_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4153_, v___f_4170_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
return v___x_4171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft___boxed(lean_object* v_e_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_){
_start:
{
lean_object* v_res_4184_; 
v_res_4184_ = l_Lean_Meta_Grind_propagateBVRotateLeft(v_e_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_);
lean_dec(v_a_4182_);
lean_dec_ref(v_a_4181_);
lean_dec(v_a_4180_);
lean_dec_ref(v_a_4179_);
lean_dec(v_a_4178_);
lean_dec_ref(v_a_4177_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
lean_dec(v_a_4174_);
lean_dec(v_a_4173_);
return v_res_4184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateLeft___regBuiltin_Lean_Meta_Grind_propagateBVRotateLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1541346404____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4186_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateLeft___closed__1));
v___x_4187_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVRotateLeft___boxed), 12, 0);
v___x_4188_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4186_, v___x_4187_);
return v___x_4188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateLeft___regBuiltin_Lean_Meta_Grind_propagateBVRotateLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1541346404____hygCtx___hyg_9____boxed(lean_object* v_a_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateLeft___regBuiltin_Lean_Meta_Grind_propagateBVRotateLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1541346404____hygCtx___hyg_9_();
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateRight___lam__0(lean_object* v_r_u2081_4191_, lean_object* v_r_u2082_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4191_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4260_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4207_ = v___x_4204_;
v_isShared_4208_ = v_isSharedCheck_4260_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4204_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4260_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
if (lean_obj_tag(v_a_4205_) == 1)
{
lean_object* v_val_4209_; lean_object* v_fst_4210_; lean_object* v_snd_4211_; lean_object* v___x_4212_; 
lean_del_object(v___x_4207_);
v_val_4209_ = lean_ctor_get(v_a_4205_, 0);
lean_inc(v_val_4209_);
lean_dec_ref_known(v_a_4205_, 1);
v_fst_4210_ = lean_ctor_get(v_val_4209_, 0);
lean_inc(v_fst_4210_);
v_snd_4211_ = lean_ctor_get(v_val_4209_, 1);
lean_inc(v_snd_4211_);
lean_dec(v_val_4209_);
v___x_4212_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4192_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4247_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4215_ = v___x_4212_;
v_isShared_4216_ = v_isSharedCheck_4247_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4212_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4247_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
if (lean_obj_tag(v_a_4213_) == 1)
{
lean_object* v_val_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4242_; 
lean_del_object(v___x_4215_);
v_val_4217_ = lean_ctor_get(v_a_4213_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v_a_4213_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4219_ = v_a_4213_;
v_isShared_4220_ = v_isSharedCheck_4242_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_val_4217_);
lean_dec(v_a_4213_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4242_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4221_ = l_BitVec_rotateRight(v_fst_4210_, v_snd_4211_, v_val_4217_);
lean_dec(v_val_4217_);
lean_dec(v_snd_4211_);
v___x_4222_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4210_, v___x_4221_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4233_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4225_ = v___x_4222_;
v_isShared_4226_ = v_isSharedCheck_4233_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4222_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4233_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4220_ == 0)
{
lean_ctor_set(v___x_4219_, 0, v_a_4223_);
v___x_4228_ = v___x_4219_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
lean_object* v___x_4230_; 
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 0, v___x_4228_);
v___x_4230_ = v___x_4225_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4228_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
else
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4241_; 
lean_del_object(v___x_4219_);
v_a_4234_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4236_ = v___x_4222_;
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v___x_4222_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4239_; 
if (v_isShared_4237_ == 0)
{
v___x_4239_ = v___x_4236_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4234_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
}
}
else
{
lean_object* v___x_4243_; lean_object* v___x_4245_; 
lean_dec(v_a_4213_);
lean_dec(v_snd_4211_);
lean_dec(v_fst_4210_);
v___x_4243_ = lean_box(0);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 0, v___x_4243_);
v___x_4245_ = v___x_4215_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v___x_4243_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
}
else
{
lean_object* v_a_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4255_; 
lean_dec(v_snd_4211_);
lean_dec(v_fst_4210_);
v_a_4248_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4250_ = v___x_4212_;
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_a_4248_);
lean_dec(v___x_4212_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4253_; 
if (v_isShared_4251_ == 0)
{
v___x_4253_ = v___x_4250_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
else
{
lean_object* v___x_4256_; lean_object* v___x_4258_; 
lean_dec(v_a_4205_);
v___x_4256_ = lean_box(0);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v___x_4256_);
v___x_4258_ = v___x_4207_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v___x_4256_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
v_a_4261_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4263_ = v___x_4204_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4204_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_a_4261_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateRight___lam__0___boxed(lean_object* v_r_u2081_4269_, lean_object* v_r_u2082_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v_res_4282_; 
v_res_4282_ = l_Lean_Meta_Grind_propagateBVRotateRight___lam__0(v_r_u2081_4269_, v_r_u2082_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec(v___y_4271_);
lean_dec_ref(v_r_u2082_4270_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateRight(lean_object* v_e_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_){
_start:
{
lean_object* v___x_4300_; lean_object* v___x_4301_; uint8_t v___x_4302_; 
v___x_4300_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateRight___closed__1));
v___x_4301_ = lean_unsigned_to_nat(3u);
v___x_4302_ = l_Lean_Expr_isAppOfArity(v_e_4288_, v___x_4300_, v___x_4301_);
if (v___x_4302_ == 0)
{
lean_object* v___x_4303_; lean_object* v___x_4304_; 
lean_dec_ref(v_e_4288_);
v___x_4303_ = lean_box(0);
v___x_4304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4303_);
return v___x_4304_;
}
else
{
lean_object* v___f_4305_; lean_object* v___x_4306_; 
v___f_4305_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateRight___closed__2));
v___x_4306_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4288_, v___f_4305_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
return v___x_4306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateRight___boxed(lean_object* v_e_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = l_Lean_Meta_Grind_propagateBVRotateRight(v_e_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_);
lean_dec(v_a_4317_);
lean_dec_ref(v_a_4316_);
lean_dec(v_a_4315_);
lean_dec_ref(v_a_4314_);
lean_dec(v_a_4313_);
lean_dec_ref(v_a_4312_);
lean_dec(v_a_4311_);
lean_dec_ref(v_a_4310_);
lean_dec(v_a_4309_);
lean_dec(v_a_4308_);
return v_res_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateRight___regBuiltin_Lean_Meta_Grind_propagateBVRotateRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2456321972____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4321_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateRight___closed__1));
v___x_4322_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVRotateRight___boxed), 12, 0);
v___x_4323_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4321_, v___x_4322_);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateRight___regBuiltin_Lean_Meta_Grind_propagateBVRotateRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2456321972____hygCtx___hyg_9____boxed(lean_object* v_a_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateRight___regBuiltin_Lean_Meta_Grind_propagateBVRotateRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2456321972____hygCtx___hyg_9_();
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0(lean_object* v_op_4326_, uint8_t v_isLeftShift_4327_, uint8_t v___x_4328_, lean_object* v_r_u2081_4329_, lean_object* v_r_u2082_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v___x_4342_; 
v___x_4342_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4329_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
if (lean_obj_tag(v___x_4342_) == 0)
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4445_; 
v_a_4343_ = lean_ctor_get(v___x_4342_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4345_ = v___x_4342_;
v_isShared_4346_ = v_isSharedCheck_4445_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4342_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4445_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
if (lean_obj_tag(v_a_4343_) == 1)
{
lean_object* v_val_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4440_; 
lean_del_object(v___x_4345_);
v_val_4347_ = lean_ctor_get(v_a_4343_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v_a_4343_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4349_ = v_a_4343_;
v_isShared_4350_ = v_isSharedCheck_4440_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_val_4347_);
lean_dec(v_a_4343_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4440_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v_fst_4351_; lean_object* v_snd_4352_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v_i_4383_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___x_4409_; 
v_fst_4351_ = lean_ctor_get(v_val_4347_, 0);
lean_inc(v_fst_4351_);
v_snd_4352_ = lean_ctor_get(v_val_4347_, 1);
lean_inc(v_snd_4352_);
lean_dec(v_val_4347_);
v___x_4409_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4330_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
if (lean_obj_tag(v_a_4410_) == 1)
{
lean_object* v_val_4411_; 
lean_dec_ref(v_r_u2082_4330_);
v_val_4411_ = lean_ctor_get(v_a_4410_, 0);
lean_inc(v_val_4411_);
lean_dec_ref_known(v_a_4410_, 1);
v_i_4383_ = v_val_4411_;
v___y_4384_ = v___y_4335_;
v___y_4385_ = v___y_4336_;
v___y_4386_ = v___y_4337_;
v___y_4387_ = v___y_4338_;
v___y_4388_ = v___y_4339_;
v___y_4389_ = v___y_4340_;
goto v___jp_4382_;
}
else
{
lean_object* v___x_4412_; 
lean_dec(v_a_4410_);
v___x_4412_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_4330_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4423_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4415_ = v___x_4412_;
v_isShared_4416_ = v_isSharedCheck_4423_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v___x_4412_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4423_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
if (lean_obj_tag(v_a_4413_) == 1)
{
lean_object* v_val_4417_; lean_object* v_snd_4418_; 
lean_del_object(v___x_4415_);
v_val_4417_ = lean_ctor_get(v_a_4413_, 0);
lean_inc(v_val_4417_);
lean_dec_ref_known(v_a_4413_, 1);
v_snd_4418_ = lean_ctor_get(v_val_4417_, 1);
lean_inc(v_snd_4418_);
lean_dec(v_val_4417_);
v_i_4383_ = v_snd_4418_;
v___y_4384_ = v___y_4335_;
v___y_4385_ = v___y_4336_;
v___y_4386_ = v___y_4337_;
v___y_4387_ = v___y_4338_;
v___y_4388_ = v___y_4339_;
v___y_4389_ = v___y_4340_;
goto v___jp_4382_;
}
else
{
lean_object* v___x_4419_; lean_object* v___x_4421_; 
lean_dec(v_a_4413_);
lean_dec(v_snd_4352_);
lean_dec(v_fst_4351_);
lean_del_object(v___x_4349_);
lean_dec_ref(v_op_4326_);
v___x_4419_ = lean_box(0);
if (v_isShared_4416_ == 0)
{
lean_ctor_set(v___x_4415_, 0, v___x_4419_);
v___x_4421_ = v___x_4415_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v___x_4419_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
}
}
else
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
lean_dec(v_snd_4352_);
lean_dec(v_fst_4351_);
lean_del_object(v___x_4349_);
lean_dec_ref(v_op_4326_);
v_a_4424_ = lean_ctor_get(v___x_4412_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4426_ = v___x_4412_;
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4412_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4429_; 
if (v_isShared_4427_ == 0)
{
v___x_4429_ = v___x_4426_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
}
}
}
else
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4439_; 
lean_dec(v_snd_4352_);
lean_dec(v_fst_4351_);
lean_del_object(v___x_4349_);
lean_dec_ref(v_r_u2082_4330_);
lean_dec_ref(v_op_4326_);
v_a_4432_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4434_ = v___x_4409_;
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4409_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4437_; 
if (v_isShared_4435_ == 0)
{
v___x_4437_ = v___x_4434_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4432_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
v___jp_4353_:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; 
lean_inc(v_fst_4351_);
v___x_4361_ = lean_apply_3(v_op_4326_, v_fst_4351_, v_snd_4352_, v___y_4354_);
v___x_4362_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4351_, v___x_4361_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4373_; 
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4365_ = v___x_4362_;
v_isShared_4366_ = v_isSharedCheck_4373_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4362_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4373_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4350_ == 0)
{
lean_ctor_set(v___x_4349_, 0, v_a_4363_);
v___x_4368_ = v___x_4349_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_a_4363_);
v___x_4368_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
lean_object* v___x_4370_; 
if (v_isShared_4366_ == 0)
{
lean_ctor_set(v___x_4365_, 0, v___x_4368_);
v___x_4370_ = v___x_4365_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4368_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
else
{
lean_object* v_a_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4381_; 
lean_del_object(v___x_4349_);
v_a_4374_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4376_ = v___x_4362_;
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_a_4374_);
lean_dec(v___x_4362_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4379_; 
if (v_isShared_4377_ == 0)
{
v___x_4379_ = v___x_4376_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_a_4374_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
}
}
v___jp_4382_:
{
if (v_isLeftShift_4327_ == 0)
{
v___y_4354_ = v_i_4383_;
v___y_4355_ = v___y_4384_;
v___y_4356_ = v___y_4385_;
v___y_4357_ = v___y_4386_;
v___y_4358_ = v___y_4387_;
v___y_4359_ = v___y_4388_;
v___y_4360_ = v___y_4389_;
goto v___jp_4353_;
}
else
{
lean_object* v___x_4390_; 
lean_inc(v_i_4383_);
v___x_4390_ = l_Lean_checkShiftLeft(v_snd_4352_, v_i_4383_, v___x_4328_, v___y_4388_, v___y_4389_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4400_; 
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4393_ = v___x_4390_;
v_isShared_4394_ = v_isSharedCheck_4400_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4390_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4400_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
uint8_t v___x_4395_; 
v___x_4395_ = lean_unbox(v_a_4391_);
lean_dec(v_a_4391_);
if (v___x_4395_ == 0)
{
lean_object* v___x_4396_; lean_object* v___x_4398_; 
lean_dec(v_i_4383_);
lean_dec(v_snd_4352_);
lean_dec(v_fst_4351_);
lean_del_object(v___x_4349_);
lean_dec_ref(v_op_4326_);
v___x_4396_ = lean_box(0);
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 0, v___x_4396_);
v___x_4398_ = v___x_4393_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v___x_4396_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
else
{
lean_del_object(v___x_4393_);
v___y_4354_ = v_i_4383_;
v___y_4355_ = v___y_4384_;
v___y_4356_ = v___y_4385_;
v___y_4357_ = v___y_4386_;
v___y_4358_ = v___y_4387_;
v___y_4359_ = v___y_4388_;
v___y_4360_ = v___y_4389_;
goto v___jp_4353_;
}
}
}
else
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
lean_dec(v_i_4383_);
lean_dec(v_snd_4352_);
lean_dec(v_fst_4351_);
lean_del_object(v___x_4349_);
lean_dec_ref(v_op_4326_);
v_a_4401_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4390_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4390_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
if (v_isShared_4404_ == 0)
{
v___x_4406_ = v___x_4403_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_a_4401_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4441_; lean_object* v___x_4443_; 
lean_dec(v_a_4343_);
lean_dec_ref(v_r_u2082_4330_);
lean_dec_ref(v_op_4326_);
v___x_4441_ = lean_box(0);
if (v_isShared_4346_ == 0)
{
lean_ctor_set(v___x_4345_, 0, v___x_4441_);
v___x_4443_ = v___x_4345_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4441_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
}
else
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
lean_dec_ref(v_r_u2082_4330_);
lean_dec_ref(v_op_4326_);
v_a_4446_ = lean_ctor_get(v___x_4342_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4342_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4342_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0___boxed(lean_object* v_op_4454_, lean_object* v_isLeftShift_4455_, lean_object* v___x_4456_, lean_object* v_r_u2081_4457_, lean_object* v_r_u2082_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_){
_start:
{
uint8_t v_isLeftShift_boxed_4470_; uint8_t v___x_10276__boxed_4471_; lean_object* v_res_4472_; 
v_isLeftShift_boxed_4470_ = lean_unbox(v_isLeftShift_4455_);
v___x_10276__boxed_4471_ = lean_unbox(v___x_4456_);
v_res_4472_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0(v_op_4454_, v_isLeftShift_boxed_4470_, v___x_10276__boxed_4471_, v_r_u2081_4457_, v_r_u2082_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v___y_4460_);
lean_dec(v___y_4459_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV(lean_object* v_declName_4473_, lean_object* v_op_4474_, lean_object* v_e_4475_, uint8_t v_isLeftShift_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_){
_start:
{
lean_object* v___x_4488_; uint8_t v___x_4489_; 
v___x_4488_ = lean_unsigned_to_nat(6u);
v___x_4489_ = l_Lean_Expr_isAppOfArity(v_e_4475_, v_declName_4473_, v___x_4488_);
if (v___x_4489_ == 0)
{
lean_object* v___x_4490_; lean_object* v___x_4491_; 
lean_dec_ref(v_e_4475_);
lean_dec_ref(v_op_4474_);
v___x_4490_ = lean_box(0);
v___x_4491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4490_);
return v___x_4491_;
}
else
{
lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___f_4494_; lean_object* v___x_4495_; 
v___x_4492_ = lean_box(v_isLeftShift_4476_);
v___x_4493_ = lean_box(v___x_4489_);
v___f_4494_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4494_, 0, v_op_4474_);
lean_closure_set(v___f_4494_, 1, v___x_4492_);
lean_closure_set(v___f_4494_, 2, v___x_4493_);
v___x_4495_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4475_, v___f_4494_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_);
return v___x_4495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___boxed(lean_object* v_declName_4496_, lean_object* v_op_4497_, lean_object* v_e_4498_, lean_object* v_isLeftShift_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_){
_start:
{
uint8_t v_isLeftShift_boxed_4511_; lean_object* v_res_4512_; 
v_isLeftShift_boxed_4511_ = lean_unbox(v_isLeftShift_4499_);
v_res_4512_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV(v_declName_4496_, v_op_4497_, v_e_4498_, v_isLeftShift_boxed_4511_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
lean_dec(v_a_4505_);
lean_dec_ref(v_a_4504_);
lean_dec(v_a_4503_);
lean_dec_ref(v_a_4502_);
lean_dec(v_a_4501_);
lean_dec(v_a_4500_);
lean_dec(v_declName_4496_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___lam__0(uint8_t v___x_4513_, lean_object* v_r_u2081_4514_, lean_object* v_r_u2082_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
lean_object* v___x_4527_; 
v___x_4527_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4514_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4622_; 
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4530_ = v___x_4527_;
v_isShared_4531_ = v_isSharedCheck_4622_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v___x_4527_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4622_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
if (lean_obj_tag(v_a_4528_) == 1)
{
lean_object* v_val_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4617_; 
lean_del_object(v___x_4530_);
v_val_4532_ = lean_ctor_get(v_a_4528_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v_a_4528_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4534_ = v_a_4528_;
v_isShared_4535_ = v_isSharedCheck_4617_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_val_4532_);
lean_dec(v_a_4528_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4617_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v_fst_4536_; lean_object* v_snd_4537_; lean_object* v_i_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4545_; lean_object* v___x_4586_; 
v_fst_4536_ = lean_ctor_get(v_val_4532_, 0);
lean_inc(v_fst_4536_);
v_snd_4537_ = lean_ctor_get(v_val_4532_, 1);
lean_inc(v_snd_4537_);
lean_dec(v_val_4532_);
v___x_4586_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4515_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v_a_4587_; 
v_a_4587_ = lean_ctor_get(v___x_4586_, 0);
lean_inc(v_a_4587_);
lean_dec_ref_known(v___x_4586_, 1);
if (lean_obj_tag(v_a_4587_) == 1)
{
lean_object* v_val_4588_; 
lean_dec_ref(v_r_u2082_4515_);
v_val_4588_ = lean_ctor_get(v_a_4587_, 0);
lean_inc(v_val_4588_);
lean_dec_ref_known(v_a_4587_, 1);
v_i_4539_ = v_val_4588_;
v___y_4540_ = v___y_4520_;
v___y_4541_ = v___y_4521_;
v___y_4542_ = v___y_4522_;
v___y_4543_ = v___y_4523_;
v___y_4544_ = v___y_4524_;
v___y_4545_ = v___y_4525_;
goto v___jp_4538_;
}
else
{
lean_object* v___x_4589_; 
lean_dec(v_a_4587_);
v___x_4589_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_4515_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
if (lean_obj_tag(v___x_4589_) == 0)
{
lean_object* v_a_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4600_; 
v_a_4590_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4592_ = v___x_4589_;
v_isShared_4593_ = v_isSharedCheck_4600_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_a_4590_);
lean_dec(v___x_4589_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4600_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
if (lean_obj_tag(v_a_4590_) == 1)
{
lean_object* v_val_4594_; lean_object* v_snd_4595_; 
lean_del_object(v___x_4592_);
v_val_4594_ = lean_ctor_get(v_a_4590_, 0);
lean_inc(v_val_4594_);
lean_dec_ref_known(v_a_4590_, 1);
v_snd_4595_ = lean_ctor_get(v_val_4594_, 1);
lean_inc(v_snd_4595_);
lean_dec(v_val_4594_);
v_i_4539_ = v_snd_4595_;
v___y_4540_ = v___y_4520_;
v___y_4541_ = v___y_4521_;
v___y_4542_ = v___y_4522_;
v___y_4543_ = v___y_4523_;
v___y_4544_ = v___y_4524_;
v___y_4545_ = v___y_4525_;
goto v___jp_4538_;
}
else
{
lean_object* v___x_4596_; lean_object* v___x_4598_; 
lean_dec(v_a_4590_);
lean_dec(v_snd_4537_);
lean_dec(v_fst_4536_);
lean_del_object(v___x_4534_);
v___x_4596_ = lean_box(0);
if (v_isShared_4593_ == 0)
{
lean_ctor_set(v___x_4592_, 0, v___x_4596_);
v___x_4598_ = v___x_4592_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4596_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
else
{
lean_object* v_a_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4608_; 
lean_dec(v_snd_4537_);
lean_dec(v_fst_4536_);
lean_del_object(v___x_4534_);
v_a_4601_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4603_ = v___x_4589_;
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_a_4601_);
lean_dec(v___x_4589_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4606_; 
if (v_isShared_4604_ == 0)
{
v___x_4606_ = v___x_4603_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_a_4601_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
}
else
{
lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4616_; 
lean_dec(v_snd_4537_);
lean_dec(v_fst_4536_);
lean_del_object(v___x_4534_);
lean_dec_ref(v_r_u2082_4515_);
v_a_4609_ = lean_ctor_get(v___x_4586_, 0);
v_isSharedCheck_4616_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4611_ = v___x_4586_;
v_isShared_4612_ = v_isSharedCheck_4616_;
goto v_resetjp_4610_;
}
else
{
lean_inc(v_a_4609_);
lean_dec(v___x_4586_);
v___x_4611_ = lean_box(0);
v_isShared_4612_ = v_isSharedCheck_4616_;
goto v_resetjp_4610_;
}
v_resetjp_4610_:
{
lean_object* v___x_4614_; 
if (v_isShared_4612_ == 0)
{
v___x_4614_ = v___x_4611_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v_a_4609_);
v___x_4614_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
return v___x_4614_;
}
}
}
v___jp_4538_:
{
lean_object* v___x_4546_; 
lean_inc(v_i_4539_);
v___x_4546_ = l_Lean_checkShiftLeft(v_snd_4537_, v_i_4539_, v___x_4513_, v___y_4544_, v___y_4545_);
if (lean_obj_tag(v___x_4546_) == 0)
{
lean_object* v_a_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4577_; 
v_a_4547_ = lean_ctor_get(v___x_4546_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4546_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4549_ = v___x_4546_;
v_isShared_4550_ = v_isSharedCheck_4577_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_a_4547_);
lean_dec(v___x_4546_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4577_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
uint8_t v___x_4551_; 
v___x_4551_ = lean_unbox(v_a_4547_);
lean_dec(v_a_4547_);
if (v___x_4551_ == 0)
{
lean_object* v___x_4552_; lean_object* v___x_4554_; 
lean_dec(v_i_4539_);
lean_dec(v_snd_4537_);
lean_dec(v_fst_4536_);
lean_del_object(v___x_4534_);
v___x_4552_ = lean_box(0);
if (v_isShared_4550_ == 0)
{
lean_ctor_set(v___x_4549_, 0, v___x_4552_);
v___x_4554_ = v___x_4549_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v___x_4552_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
else
{
lean_object* v___x_4556_; lean_object* v___x_4557_; 
lean_del_object(v___x_4549_);
v___x_4556_ = l_BitVec_shiftLeft(v_fst_4536_, v_snd_4537_, v_i_4539_);
lean_dec(v_i_4539_);
lean_dec(v_snd_4537_);
v___x_4557_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4536_, v___x_4556_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_object* v_a_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4568_; 
v_a_4558_ = lean_ctor_get(v___x_4557_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___x_4557_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4560_ = v___x_4557_;
v_isShared_4561_ = v_isSharedCheck_4568_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_a_4558_);
lean_dec(v___x_4557_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4568_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v___x_4563_; 
if (v_isShared_4535_ == 0)
{
lean_ctor_set(v___x_4534_, 0, v_a_4558_);
v___x_4563_ = v___x_4534_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4558_);
v___x_4563_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
lean_object* v___x_4565_; 
if (v_isShared_4561_ == 0)
{
lean_ctor_set(v___x_4560_, 0, v___x_4563_);
v___x_4565_ = v___x_4560_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v___x_4563_);
v___x_4565_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
return v___x_4565_;
}
}
}
}
else
{
lean_object* v_a_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4576_; 
lean_del_object(v___x_4534_);
v_a_4569_ = lean_ctor_get(v___x_4557_, 0);
v_isSharedCheck_4576_ = !lean_is_exclusive(v___x_4557_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4571_ = v___x_4557_;
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_a_4569_);
lean_dec(v___x_4557_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v___x_4574_; 
if (v_isShared_4572_ == 0)
{
v___x_4574_ = v___x_4571_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_a_4569_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
return v___x_4574_;
}
}
}
}
}
}
else
{
lean_object* v_a_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4585_; 
lean_dec(v_i_4539_);
lean_dec(v_snd_4537_);
lean_dec(v_fst_4536_);
lean_del_object(v___x_4534_);
v_a_4578_ = lean_ctor_get(v___x_4546_, 0);
v_isSharedCheck_4585_ = !lean_is_exclusive(v___x_4546_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4580_ = v___x_4546_;
v_isShared_4581_ = v_isSharedCheck_4585_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_a_4578_);
lean_dec(v___x_4546_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4585_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___x_4583_; 
if (v_isShared_4581_ == 0)
{
v___x_4583_ = v___x_4580_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_a_4578_);
v___x_4583_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
return v___x_4583_;
}
}
}
}
}
}
else
{
lean_object* v___x_4618_; lean_object* v___x_4620_; 
lean_dec(v_a_4528_);
lean_dec_ref(v_r_u2082_4515_);
v___x_4618_ = lean_box(0);
if (v_isShared_4531_ == 0)
{
lean_ctor_set(v___x_4530_, 0, v___x_4618_);
v___x_4620_ = v___x_4530_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4618_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
}
}
else
{
lean_object* v_a_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4630_; 
lean_dec_ref(v_r_u2082_4515_);
v_a_4623_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4625_ = v___x_4527_;
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_a_4623_);
lean_dec(v___x_4527_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4628_; 
if (v_isShared_4626_ == 0)
{
v___x_4628_ = v___x_4625_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v_a_4623_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
return v___x_4628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___lam__0___boxed(lean_object* v___x_4631_, lean_object* v_r_u2081_4632_, lean_object* v_r_u2082_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
uint8_t v___x_183__boxed_4645_; lean_object* v_res_4646_; 
v___x_183__boxed_4645_ = lean_unbox(v___x_4631_);
v_res_4646_ = l_Lean_Meta_Grind_propagateBVHShiftLeft___lam__0(v___x_183__boxed_4645_, v_r_u2081_4632_, v_r_u2082_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
lean_dec(v___y_4643_);
lean_dec_ref(v___y_4642_);
lean_dec(v___y_4641_);
lean_dec_ref(v___y_4640_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
lean_dec(v___y_4635_);
lean_dec(v___y_4634_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft(lean_object* v_e_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_){
_start:
{
lean_object* v___x_4664_; lean_object* v___x_4665_; uint8_t v___x_4666_; 
v___x_4664_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__2));
v___x_4665_ = lean_unsigned_to_nat(6u);
v___x_4666_ = l_Lean_Expr_isAppOfArity(v_e_4652_, v___x_4664_, v___x_4665_);
if (v___x_4666_ == 0)
{
lean_object* v___x_4667_; lean_object* v___x_4668_; 
lean_dec_ref(v_e_4652_);
v___x_4667_ = lean_box(0);
v___x_4668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4668_, 0, v___x_4667_);
return v___x_4668_;
}
else
{
lean_object* v___x_4669_; lean_object* v___f_4670_; lean_object* v___x_4671_; 
v___x_4669_ = lean_box(v___x_4666_);
v___f_4670_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVHShiftLeft___lam__0___boxed), 14, 1);
lean_closure_set(v___f_4670_, 0, v___x_4669_);
v___x_4671_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4652_, v___f_4670_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_);
return v___x_4671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___boxed(lean_object* v_e_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_){
_start:
{
lean_object* v_res_4684_; 
v_res_4684_ = l_Lean_Meta_Grind_propagateBVHShiftLeft(v_e_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_);
lean_dec(v_a_4682_);
lean_dec_ref(v_a_4681_);
lean_dec(v_a_4680_);
lean_dec_ref(v_a_4679_);
lean_dec(v_a_4678_);
lean_dec_ref(v_a_4677_);
lean_dec(v_a_4676_);
lean_dec_ref(v_a_4675_);
lean_dec(v_a_4674_);
lean_dec(v_a_4673_);
return v_res_4684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3470952822____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4686_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__2));
v___x_4687_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVHShiftLeft___boxed), 12, 0);
v___x_4688_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4686_, v___x_4687_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3470952822____hygCtx___hyg_9____boxed(lean_object* v_a_4689_){
_start:
{
lean_object* v_res_4690_; 
v_res_4690_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3470952822____hygCtx___hyg_9_();
return v_res_4690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight___lam__0(lean_object* v_r_u2081_4691_, lean_object* v_r_u2082_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_){
_start:
{
lean_object* v___x_4704_; 
v___x_4704_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4691_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_);
if (lean_obj_tag(v___x_4704_) == 0)
{
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4780_; 
v_a_4705_ = lean_ctor_get(v___x_4704_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4707_ = v___x_4704_;
v_isShared_4708_ = v_isSharedCheck_4780_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___x_4704_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4780_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
if (lean_obj_tag(v_a_4705_) == 1)
{
lean_object* v_val_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4775_; 
lean_del_object(v___x_4707_);
v_val_4709_ = lean_ctor_get(v_a_4705_, 0);
v_isSharedCheck_4775_ = !lean_is_exclusive(v_a_4705_);
if (v_isSharedCheck_4775_ == 0)
{
v___x_4711_ = v_a_4705_;
v_isShared_4712_ = v_isSharedCheck_4775_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_val_4709_);
lean_dec(v_a_4705_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4775_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v_fst_4713_; lean_object* v_snd_4714_; lean_object* v_i_4716_; lean_object* v___y_4717_; lean_object* v___y_4718_; lean_object* v___y_4719_; lean_object* v___y_4720_; lean_object* v___y_4721_; lean_object* v___y_4722_; lean_object* v___x_4744_; 
v_fst_4713_ = lean_ctor_get(v_val_4709_, 0);
lean_inc(v_fst_4713_);
v_snd_4714_ = lean_ctor_get(v_val_4709_, 1);
lean_inc(v_snd_4714_);
lean_dec(v_val_4709_);
v___x_4744_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4692_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_object* v_a_4745_; 
v_a_4745_ = lean_ctor_get(v___x_4744_, 0);
lean_inc(v_a_4745_);
lean_dec_ref_known(v___x_4744_, 1);
if (lean_obj_tag(v_a_4745_) == 1)
{
lean_object* v_val_4746_; 
lean_dec_ref(v_r_u2082_4692_);
v_val_4746_ = lean_ctor_get(v_a_4745_, 0);
lean_inc(v_val_4746_);
lean_dec_ref_known(v_a_4745_, 1);
v_i_4716_ = v_val_4746_;
v___y_4717_ = v___y_4697_;
v___y_4718_ = v___y_4698_;
v___y_4719_ = v___y_4699_;
v___y_4720_ = v___y_4700_;
v___y_4721_ = v___y_4701_;
v___y_4722_ = v___y_4702_;
goto v___jp_4715_;
}
else
{
lean_object* v___x_4747_; 
lean_dec(v_a_4745_);
v___x_4747_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_4692_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_);
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v_a_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4758_; 
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4750_ = v___x_4747_;
v_isShared_4751_ = v_isSharedCheck_4758_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_a_4748_);
lean_dec(v___x_4747_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4758_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
if (lean_obj_tag(v_a_4748_) == 1)
{
lean_object* v_val_4752_; lean_object* v_snd_4753_; 
lean_del_object(v___x_4750_);
v_val_4752_ = lean_ctor_get(v_a_4748_, 0);
lean_inc(v_val_4752_);
lean_dec_ref_known(v_a_4748_, 1);
v_snd_4753_ = lean_ctor_get(v_val_4752_, 1);
lean_inc(v_snd_4753_);
lean_dec(v_val_4752_);
v_i_4716_ = v_snd_4753_;
v___y_4717_ = v___y_4697_;
v___y_4718_ = v___y_4698_;
v___y_4719_ = v___y_4699_;
v___y_4720_ = v___y_4700_;
v___y_4721_ = v___y_4701_;
v___y_4722_ = v___y_4702_;
goto v___jp_4715_;
}
else
{
lean_object* v___x_4754_; lean_object* v___x_4756_; 
lean_dec(v_a_4748_);
lean_dec(v_snd_4714_);
lean_dec(v_fst_4713_);
lean_del_object(v___x_4711_);
v___x_4754_ = lean_box(0);
if (v_isShared_4751_ == 0)
{
lean_ctor_set(v___x_4750_, 0, v___x_4754_);
v___x_4756_ = v___x_4750_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v___x_4754_);
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
else
{
lean_object* v_a_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4766_; 
lean_dec(v_snd_4714_);
lean_dec(v_fst_4713_);
lean_del_object(v___x_4711_);
v_a_4759_ = lean_ctor_get(v___x_4747_, 0);
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4766_ == 0)
{
v___x_4761_ = v___x_4747_;
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_a_4759_);
lean_dec(v___x_4747_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4764_; 
if (v_isShared_4762_ == 0)
{
v___x_4764_ = v___x_4761_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_a_4759_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
return v___x_4764_;
}
}
}
}
}
else
{
lean_object* v_a_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4774_; 
lean_dec(v_snd_4714_);
lean_dec(v_fst_4713_);
lean_del_object(v___x_4711_);
lean_dec_ref(v_r_u2082_4692_);
v_a_4767_ = lean_ctor_get(v___x_4744_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v___x_4744_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4769_ = v___x_4744_;
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_a_4767_);
lean_dec(v___x_4744_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___x_4772_; 
if (v_isShared_4770_ == 0)
{
v___x_4772_ = v___x_4769_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_a_4767_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
return v___x_4772_;
}
}
}
v___jp_4715_:
{
lean_object* v___x_4723_; lean_object* v___x_4724_; 
v___x_4723_ = lean_nat_shiftr(v_snd_4714_, v_i_4716_);
lean_dec(v_i_4716_);
lean_dec(v_snd_4714_);
v___x_4724_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4713_, v___x_4723_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_);
if (lean_obj_tag(v___x_4724_) == 0)
{
lean_object* v_a_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4735_; 
v_a_4725_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4735_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4735_ == 0)
{
v___x_4727_ = v___x_4724_;
v_isShared_4728_ = v_isSharedCheck_4735_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_a_4725_);
lean_dec(v___x_4724_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4735_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
lean_object* v___x_4730_; 
if (v_isShared_4712_ == 0)
{
lean_ctor_set(v___x_4711_, 0, v_a_4725_);
v___x_4730_ = v___x_4711_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_a_4725_);
v___x_4730_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
lean_object* v___x_4732_; 
if (v_isShared_4728_ == 0)
{
lean_ctor_set(v___x_4727_, 0, v___x_4730_);
v___x_4732_ = v___x_4727_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v___x_4730_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
}
}
else
{
lean_object* v_a_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4743_; 
lean_del_object(v___x_4711_);
v_a_4736_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4743_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4738_ = v___x_4724_;
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_a_4736_);
lean_dec(v___x_4724_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v___x_4741_; 
if (v_isShared_4739_ == 0)
{
v___x_4741_ = v___x_4738_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v_a_4736_);
v___x_4741_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
return v___x_4741_;
}
}
}
}
}
}
else
{
lean_object* v___x_4776_; lean_object* v___x_4778_; 
lean_dec(v_a_4705_);
lean_dec_ref(v_r_u2082_4692_);
v___x_4776_ = lean_box(0);
if (v_isShared_4708_ == 0)
{
lean_ctor_set(v___x_4707_, 0, v___x_4776_);
v___x_4778_ = v___x_4707_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v___x_4776_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
}
else
{
lean_object* v_a_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4788_; 
lean_dec_ref(v_r_u2082_4692_);
v_a_4781_ = lean_ctor_get(v___x_4704_, 0);
v_isSharedCheck_4788_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4783_ = v___x_4704_;
v_isShared_4784_ = v_isSharedCheck_4788_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_a_4781_);
lean_dec(v___x_4704_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4788_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v___x_4786_; 
if (v_isShared_4784_ == 0)
{
v___x_4786_ = v___x_4783_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v_a_4781_);
v___x_4786_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
return v___x_4786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight___lam__0___boxed(lean_object* v_r_u2081_4789_, lean_object* v_r_u2082_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_){
_start:
{
lean_object* v_res_4802_; 
v_res_4802_ = l_Lean_Meta_Grind_propagateBVHShiftRight___lam__0(v_r_u2081_4789_, v_r_u2082_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_);
lean_dec(v___y_4800_);
lean_dec_ref(v___y_4799_);
lean_dec(v___y_4798_);
lean_dec_ref(v___y_4797_);
lean_dec(v___y_4796_);
lean_dec_ref(v___y_4795_);
lean_dec(v___y_4794_);
lean_dec_ref(v___y_4793_);
lean_dec(v___y_4792_);
lean_dec(v___y_4791_);
return v_res_4802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight(lean_object* v_e_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_){
_start:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; uint8_t v___x_4823_; 
v___x_4821_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVHShiftRight___closed__2));
v___x_4822_ = lean_unsigned_to_nat(6u);
v___x_4823_ = l_Lean_Expr_isAppOfArity(v_e_4809_, v___x_4821_, v___x_4822_);
if (v___x_4823_ == 0)
{
lean_object* v___x_4824_; lean_object* v___x_4825_; 
lean_dec_ref(v_e_4809_);
v___x_4824_ = lean_box(0);
v___x_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4825_, 0, v___x_4824_);
return v___x_4825_;
}
else
{
lean_object* v___f_4826_; lean_object* v___x_4827_; 
v___f_4826_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVHShiftRight___closed__3));
v___x_4827_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4809_, v___f_4826_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_, v_a_4819_);
return v___x_4827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight___boxed(lean_object* v_e_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_){
_start:
{
lean_object* v_res_4840_; 
v_res_4840_ = l_Lean_Meta_Grind_propagateBVHShiftRight(v_e_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
lean_dec(v_a_4838_);
lean_dec_ref(v_a_4837_);
lean_dec(v_a_4836_);
lean_dec_ref(v_a_4835_);
lean_dec(v_a_4834_);
lean_dec_ref(v_a_4833_);
lean_dec(v_a_4832_);
lean_dec_ref(v_a_4831_);
lean_dec(v_a_4830_);
lean_dec(v_a_4829_);
return v_res_4840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVHShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1131064821____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4842_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVHShiftRight___closed__2));
v___x_4843_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVHShiftRight___boxed), 12, 0);
v___x_4844_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4842_, v___x_4843_);
return v___x_4844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVHShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1131064821____hygCtx___hyg_9____boxed(lean_object* v_a_4845_){
_start:
{
lean_object* v_res_4846_; 
v_res_4846_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVHShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1131064821____hygCtx___hyg_9_();
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD___lam__0(lean_object* v_r_u2081_4847_, lean_object* v_r_u2082_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_){
_start:
{
lean_object* v___x_4860_; 
v___x_4860_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4847_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
if (lean_obj_tag(v___x_4860_) == 0)
{
lean_object* v_a_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4915_; 
v_a_4861_ = lean_ctor_get(v___x_4860_, 0);
v_isSharedCheck_4915_ = !lean_is_exclusive(v___x_4860_);
if (v_isSharedCheck_4915_ == 0)
{
v___x_4863_ = v___x_4860_;
v_isShared_4864_ = v_isSharedCheck_4915_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_a_4861_);
lean_dec(v___x_4860_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4915_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
if (lean_obj_tag(v_a_4861_) == 1)
{
lean_object* v_val_4865_; lean_object* v_snd_4866_; lean_object* v___x_4867_; 
lean_del_object(v___x_4863_);
v_val_4865_ = lean_ctor_get(v_a_4861_, 0);
lean_inc(v_val_4865_);
lean_dec_ref_known(v_a_4861_, 1);
v_snd_4866_ = lean_ctor_get(v_val_4865_, 1);
lean_inc(v_snd_4866_);
lean_dec(v_val_4865_);
v___x_4867_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4848_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
if (lean_obj_tag(v___x_4867_) == 0)
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4902_; 
v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4870_ = v___x_4867_;
v_isShared_4871_ = v_isSharedCheck_4902_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4867_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4902_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
if (lean_obj_tag(v_a_4868_) == 1)
{
lean_object* v_val_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4897_; 
lean_del_object(v___x_4870_);
v_val_4872_ = lean_ctor_get(v_a_4868_, 0);
v_isSharedCheck_4897_ = !lean_is_exclusive(v_a_4868_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4874_ = v_a_4868_;
v_isShared_4875_ = v_isSharedCheck_4897_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_val_4872_);
lean_dec(v_a_4868_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4897_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
uint8_t v___x_4876_; lean_object* v___x_4877_; 
v___x_4876_ = l_Nat_testBit(v_snd_4866_, v_val_4872_);
lean_dec(v_val_4872_);
lean_dec(v_snd_4866_);
v___x_4877_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v___x_4876_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_object* v_a_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4888_; 
v_a_4878_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4880_ = v___x_4877_;
v_isShared_4881_ = v_isSharedCheck_4888_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_a_4878_);
lean_dec(v___x_4877_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4888_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v___x_4883_; 
if (v_isShared_4875_ == 0)
{
lean_ctor_set(v___x_4874_, 0, v_a_4878_);
v___x_4883_ = v___x_4874_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_a_4878_);
v___x_4883_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
lean_object* v___x_4885_; 
if (v_isShared_4881_ == 0)
{
lean_ctor_set(v___x_4880_, 0, v___x_4883_);
v___x_4885_ = v___x_4880_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4886_; 
v_reuseFailAlloc_4886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4883_);
v___x_4885_ = v_reuseFailAlloc_4886_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
return v___x_4885_;
}
}
}
}
else
{
lean_object* v_a_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4896_; 
lean_del_object(v___x_4874_);
v_a_4889_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4891_ = v___x_4877_;
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_a_4889_);
lean_dec(v___x_4877_);
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
else
{
lean_object* v___x_4898_; lean_object* v___x_4900_; 
lean_dec(v_a_4868_);
lean_dec(v_snd_4866_);
v___x_4898_ = lean_box(0);
if (v_isShared_4871_ == 0)
{
lean_ctor_set(v___x_4870_, 0, v___x_4898_);
v___x_4900_ = v___x_4870_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v___x_4898_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
return v___x_4900_;
}
}
}
}
else
{
lean_object* v_a_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4910_; 
lean_dec(v_snd_4866_);
v_a_4903_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4905_ = v___x_4867_;
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_a_4903_);
lean_dec(v___x_4867_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v___x_4908_; 
if (v_isShared_4906_ == 0)
{
v___x_4908_ = v___x_4905_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_a_4903_);
v___x_4908_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
return v___x_4908_;
}
}
}
}
else
{
lean_object* v___x_4911_; lean_object* v___x_4913_; 
lean_dec(v_a_4861_);
v___x_4911_ = lean_box(0);
if (v_isShared_4864_ == 0)
{
lean_ctor_set(v___x_4863_, 0, v___x_4911_);
v___x_4913_ = v___x_4863_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4914_; 
v_reuseFailAlloc_4914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4914_, 0, v___x_4911_);
v___x_4913_ = v_reuseFailAlloc_4914_;
goto v_reusejp_4912_;
}
v_reusejp_4912_:
{
return v___x_4913_;
}
}
}
}
else
{
lean_object* v_a_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4923_; 
v_a_4916_ = lean_ctor_get(v___x_4860_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___x_4860_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4918_ = v___x_4860_;
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_a_4916_);
lean_dec(v___x_4860_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___x_4921_; 
if (v_isShared_4919_ == 0)
{
v___x_4921_ = v___x_4918_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4916_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD___lam__0___boxed(lean_object* v_r_u2081_4924_, lean_object* v_r_u2082_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_){
_start:
{
lean_object* v_res_4937_; 
v_res_4937_ = l_Lean_Meta_Grind_propagateBVGetLsbD___lam__0(v_r_u2081_4924_, v_r_u2082_4925_, v___y_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_);
lean_dec(v___y_4935_);
lean_dec_ref(v___y_4934_);
lean_dec(v___y_4933_);
lean_dec_ref(v___y_4932_);
lean_dec(v___y_4931_);
lean_dec_ref(v___y_4930_);
lean_dec(v___y_4929_);
lean_dec_ref(v___y_4928_);
lean_dec(v___y_4927_);
lean_dec(v___y_4926_);
lean_dec_ref(v_r_u2082_4925_);
return v_res_4937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD(lean_object* v_e_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_){
_start:
{
lean_object* v___x_4955_; lean_object* v___x_4956_; uint8_t v___x_4957_; 
v___x_4955_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetLsbD___closed__1));
v___x_4956_ = lean_unsigned_to_nat(3u);
v___x_4957_ = l_Lean_Expr_isAppOfArity(v_e_4943_, v___x_4955_, v___x_4956_);
if (v___x_4957_ == 0)
{
lean_object* v___x_4958_; lean_object* v___x_4959_; 
lean_dec_ref(v_e_4943_);
v___x_4958_ = lean_box(0);
v___x_4959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4959_, 0, v___x_4958_);
return v___x_4959_;
}
else
{
lean_object* v___f_4960_; lean_object* v___x_4961_; 
v___f_4960_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetLsbD___closed__2));
v___x_4961_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4943_, v___f_4960_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_);
return v___x_4961_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD___boxed(lean_object* v_e_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_){
_start:
{
lean_object* v_res_4974_; 
v_res_4974_ = l_Lean_Meta_Grind_propagateBVGetLsbD(v_e_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_);
lean_dec(v_a_4972_);
lean_dec_ref(v_a_4971_);
lean_dec(v_a_4970_);
lean_dec_ref(v_a_4969_);
lean_dec(v_a_4968_);
lean_dec_ref(v_a_4967_);
lean_dec(v_a_4966_);
lean_dec_ref(v_a_4965_);
lean_dec(v_a_4964_);
lean_dec(v_a_4963_);
return v_res_4974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetLsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetLsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1075602488____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; 
v___x_4976_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetLsbD___closed__1));
v___x_4977_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVGetLsbD___boxed), 12, 0);
v___x_4978_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4976_, v___x_4977_);
return v___x_4978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetLsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetLsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1075602488____hygCtx___hyg_9____boxed(lean_object* v_a_4979_){
_start:
{
lean_object* v_res_4980_; 
v_res_4980_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetLsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetLsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1075602488____hygCtx___hyg_9_();
return v_res_4980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD___lam__0(lean_object* v_r_u2081_4981_, lean_object* v_r_u2082_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_){
_start:
{
lean_object* v___x_4994_; 
v___x_4994_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4981_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
if (lean_obj_tag(v___x_4994_) == 0)
{
lean_object* v_a_4995_; lean_object* v___x_4997_; uint8_t v_isShared_4998_; uint8_t v_isSharedCheck_5056_; 
v_a_4995_ = lean_ctor_get(v___x_4994_, 0);
v_isSharedCheck_5056_ = !lean_is_exclusive(v___x_4994_);
if (v_isSharedCheck_5056_ == 0)
{
v___x_4997_ = v___x_4994_;
v_isShared_4998_ = v_isSharedCheck_5056_;
goto v_resetjp_4996_;
}
else
{
lean_inc(v_a_4995_);
lean_dec(v___x_4994_);
v___x_4997_ = lean_box(0);
v_isShared_4998_ = v_isSharedCheck_5056_;
goto v_resetjp_4996_;
}
v_resetjp_4996_:
{
if (lean_obj_tag(v_a_4995_) == 1)
{
lean_object* v_val_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5051_; 
lean_del_object(v___x_4997_);
v_val_4999_ = lean_ctor_get(v_a_4995_, 0);
v_isSharedCheck_5051_ = !lean_is_exclusive(v_a_4995_);
if (v_isSharedCheck_5051_ == 0)
{
v___x_5001_ = v_a_4995_;
v_isShared_5002_ = v_isSharedCheck_5051_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_val_4999_);
lean_dec(v_a_4995_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5051_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v_fst_5003_; lean_object* v_snd_5004_; lean_object* v___x_5005_; 
v_fst_5003_ = lean_ctor_get(v_val_4999_, 0);
lean_inc(v_fst_5003_);
v_snd_5004_ = lean_ctor_get(v_val_4999_, 1);
lean_inc(v_snd_5004_);
lean_dec(v_val_4999_);
v___x_5005_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4982_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
if (lean_obj_tag(v___x_5005_) == 0)
{
lean_object* v_a_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5042_; 
v_a_5006_ = lean_ctor_get(v___x_5005_, 0);
v_isSharedCheck_5042_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5042_ == 0)
{
v___x_5008_ = v___x_5005_;
v_isShared_5009_ = v_isSharedCheck_5042_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_5005_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5042_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
uint8_t v___y_5011_; 
if (lean_obj_tag(v_a_5006_) == 1)
{
lean_object* v_val_5032_; uint8_t v___x_5033_; 
lean_del_object(v___x_5008_);
v_val_5032_ = lean_ctor_get(v_a_5006_, 0);
lean_inc(v_val_5032_);
lean_dec_ref_known(v_a_5006_, 1);
v___x_5033_ = lean_nat_dec_lt(v_val_5032_, v_fst_5003_);
if (v___x_5033_ == 0)
{
lean_dec(v_val_5032_);
lean_dec(v_snd_5004_);
lean_dec(v_fst_5003_);
v___y_5011_ = v___x_5033_;
goto v___jp_5010_;
}
else
{
lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; uint8_t v___x_5037_; 
v___x_5034_ = lean_unsigned_to_nat(1u);
v___x_5035_ = lean_nat_sub(v_fst_5003_, v___x_5034_);
lean_dec(v_fst_5003_);
v___x_5036_ = lean_nat_sub(v___x_5035_, v_val_5032_);
lean_dec(v_val_5032_);
lean_dec(v___x_5035_);
v___x_5037_ = l_Nat_testBit(v_snd_5004_, v___x_5036_);
lean_dec(v___x_5036_);
lean_dec(v_snd_5004_);
v___y_5011_ = v___x_5037_;
goto v___jp_5010_;
}
}
else
{
lean_object* v___x_5038_; lean_object* v___x_5040_; 
lean_dec(v_a_5006_);
lean_dec(v_snd_5004_);
lean_dec(v_fst_5003_);
lean_del_object(v___x_5001_);
v___x_5038_ = lean_box(0);
if (v_isShared_5009_ == 0)
{
lean_ctor_set(v___x_5008_, 0, v___x_5038_);
v___x_5040_ = v___x_5008_;
goto v_reusejp_5039_;
}
else
{
lean_object* v_reuseFailAlloc_5041_; 
v_reuseFailAlloc_5041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5041_, 0, v___x_5038_);
v___x_5040_ = v_reuseFailAlloc_5041_;
goto v_reusejp_5039_;
}
v_reusejp_5039_:
{
return v___x_5040_;
}
}
v___jp_5010_:
{
lean_object* v___x_5012_; 
v___x_5012_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v___y_5011_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v_a_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5023_; 
v_a_5013_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5015_ = v___x_5012_;
v_isShared_5016_ = v_isSharedCheck_5023_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_a_5013_);
lean_dec(v___x_5012_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5023_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v___x_5018_; 
if (v_isShared_5002_ == 0)
{
lean_ctor_set(v___x_5001_, 0, v_a_5013_);
v___x_5018_ = v___x_5001_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_a_5013_);
v___x_5018_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
lean_object* v___x_5020_; 
if (v_isShared_5016_ == 0)
{
lean_ctor_set(v___x_5015_, 0, v___x_5018_);
v___x_5020_ = v___x_5015_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v___x_5018_);
v___x_5020_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
return v___x_5020_;
}
}
}
}
else
{
lean_object* v_a_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5031_; 
lean_del_object(v___x_5001_);
v_a_5024_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5031_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5031_ == 0)
{
v___x_5026_ = v___x_5012_;
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_a_5024_);
lean_dec(v___x_5012_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5029_; 
if (v_isShared_5027_ == 0)
{
v___x_5029_ = v___x_5026_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_a_5024_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
}
}
}
}
else
{
lean_object* v_a_5043_; lean_object* v___x_5045_; uint8_t v_isShared_5046_; uint8_t v_isSharedCheck_5050_; 
lean_dec(v_snd_5004_);
lean_dec(v_fst_5003_);
lean_del_object(v___x_5001_);
v_a_5043_ = lean_ctor_get(v___x_5005_, 0);
v_isSharedCheck_5050_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5050_ == 0)
{
v___x_5045_ = v___x_5005_;
v_isShared_5046_ = v_isSharedCheck_5050_;
goto v_resetjp_5044_;
}
else
{
lean_inc(v_a_5043_);
lean_dec(v___x_5005_);
v___x_5045_ = lean_box(0);
v_isShared_5046_ = v_isSharedCheck_5050_;
goto v_resetjp_5044_;
}
v_resetjp_5044_:
{
lean_object* v___x_5048_; 
if (v_isShared_5046_ == 0)
{
v___x_5048_ = v___x_5045_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v_a_5043_);
v___x_5048_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
return v___x_5048_;
}
}
}
}
}
else
{
lean_object* v___x_5052_; lean_object* v___x_5054_; 
lean_dec(v_a_4995_);
v___x_5052_ = lean_box(0);
if (v_isShared_4998_ == 0)
{
lean_ctor_set(v___x_4997_, 0, v___x_5052_);
v___x_5054_ = v___x_4997_;
goto v_reusejp_5053_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v___x_5052_);
v___x_5054_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5053_;
}
v_reusejp_5053_:
{
return v___x_5054_;
}
}
}
}
else
{
lean_object* v_a_5057_; lean_object* v___x_5059_; uint8_t v_isShared_5060_; uint8_t v_isSharedCheck_5064_; 
v_a_5057_ = lean_ctor_get(v___x_4994_, 0);
v_isSharedCheck_5064_ = !lean_is_exclusive(v___x_4994_);
if (v_isSharedCheck_5064_ == 0)
{
v___x_5059_ = v___x_4994_;
v_isShared_5060_ = v_isSharedCheck_5064_;
goto v_resetjp_5058_;
}
else
{
lean_inc(v_a_5057_);
lean_dec(v___x_4994_);
v___x_5059_ = lean_box(0);
v_isShared_5060_ = v_isSharedCheck_5064_;
goto v_resetjp_5058_;
}
v_resetjp_5058_:
{
lean_object* v___x_5062_; 
if (v_isShared_5060_ == 0)
{
v___x_5062_ = v___x_5059_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v_a_5057_);
v___x_5062_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
return v___x_5062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD___lam__0___boxed(lean_object* v_r_u2081_5065_, lean_object* v_r_u2082_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_){
_start:
{
lean_object* v_res_5078_; 
v_res_5078_ = l_Lean_Meta_Grind_propagateBVGetMsbD___lam__0(v_r_u2081_5065_, v_r_u2082_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
lean_dec(v___y_5074_);
lean_dec_ref(v___y_5073_);
lean_dec(v___y_5072_);
lean_dec_ref(v___y_5071_);
lean_dec(v___y_5070_);
lean_dec_ref(v___y_5069_);
lean_dec(v___y_5068_);
lean_dec(v___y_5067_);
lean_dec_ref(v_r_u2082_5066_);
return v_res_5078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD(lean_object* v_e_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_, lean_object* v_a_5088_, lean_object* v_a_5089_, lean_object* v_a_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_){
_start:
{
lean_object* v___x_5096_; lean_object* v___x_5097_; uint8_t v___x_5098_; 
v___x_5096_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetMsbD___closed__1));
v___x_5097_ = lean_unsigned_to_nat(3u);
v___x_5098_ = l_Lean_Expr_isAppOfArity(v_e_5084_, v___x_5096_, v___x_5097_);
if (v___x_5098_ == 0)
{
lean_object* v___x_5099_; lean_object* v___x_5100_; 
lean_dec_ref(v_e_5084_);
v___x_5099_ = lean_box(0);
v___x_5100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5100_, 0, v___x_5099_);
return v___x_5100_;
}
else
{
lean_object* v___f_5101_; lean_object* v___x_5102_; 
v___f_5101_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetMsbD___closed__2));
v___x_5102_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_5084_, v___f_5101_, v_a_5085_, v_a_5086_, v_a_5087_, v_a_5088_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_, v_a_5093_, v_a_5094_);
return v___x_5102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD___boxed(lean_object* v_e_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_, lean_object* v_a_5114_){
_start:
{
lean_object* v_res_5115_; 
v_res_5115_ = l_Lean_Meta_Grind_propagateBVGetMsbD(v_e_5103_, v_a_5104_, v_a_5105_, v_a_5106_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_5111_, v_a_5112_, v_a_5113_);
lean_dec(v_a_5113_);
lean_dec_ref(v_a_5112_);
lean_dec(v_a_5111_);
lean_dec_ref(v_a_5110_);
lean_dec(v_a_5109_);
lean_dec_ref(v_a_5108_);
lean_dec(v_a_5107_);
lean_dec_ref(v_a_5106_);
lean_dec(v_a_5105_);
lean_dec(v_a_5104_);
return v_res_5115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetMsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetMsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1507361668____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; 
v___x_5117_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetMsbD___closed__1));
v___x_5118_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVGetMsbD___boxed), 12, 0);
v___x_5119_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_5117_, v___x_5118_);
return v___x_5119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetMsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetMsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1507361668____hygCtx___hyg_9____boxed(lean_object* v_a_5120_){
_start:
{
lean_object* v_res_5121_; 
v_res_5121_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetMsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetMsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1507361668____hygCtx___hyg_9_();
return v_res_5121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetElem(lean_object* v_e_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_){
_start:
{
lean_object* v___x_5154_; uint8_t v___x_5155_; 
v___x_5154_ = l_Lean_Expr_cleanupAnnotations(v_e_5139_);
v___x_5155_ = l_Lean_Expr_isApp(v___x_5154_);
if (v___x_5155_ == 0)
{
lean_dec_ref(v___x_5154_);
lean_dec_ref(v_e_5139_);
goto v___jp_5151_;
}
else
{
lean_object* v___x_5156_; uint8_t v___x_5157_; 
v___x_5156_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5154_);
v___x_5157_ = l_Lean_Expr_isApp(v___x_5156_);
if (v___x_5157_ == 0)
{
lean_dec_ref(v___x_5156_);
lean_dec_ref(v___x_5154_);
lean_dec_ref(v_e_5139_);
goto v___jp_5151_;
}
else
{
lean_object* v___x_5158_; uint8_t v___x_5159_; 
v___x_5158_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5156_);
v___x_5159_ = l_Lean_Expr_isApp(v___x_5158_);
if (v___x_5159_ == 0)
{
lean_dec_ref(v___x_5158_);
lean_dec_ref(v___x_5156_);
lean_dec_ref(v___x_5154_);
lean_dec_ref(v_e_5139_);
goto v___jp_5151_;
}
else
{
lean_object* v___x_5160_; uint8_t v___x_5161_; 
v___x_5160_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5158_);
v___x_5161_ = l_Lean_Expr_isApp(v___x_5160_);
if (v___x_5161_ == 0)
{
lean_dec_ref(v___x_5160_);
lean_dec_ref(v___x_5158_);
lean_dec_ref(v___x_5156_);
lean_dec_ref(v___x_5154_);
lean_dec_ref(v_e_5139_);
goto v___jp_5151_;
}
else
{
lean_object* v___x_5162_; uint8_t v___x_5163_; 
v___x_5162_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5160_);
v___x_5163_ = l_Lean_Expr_isApp(v___x_5162_);
if (v___x_5163_ == 0)
{
lean_dec_ref(v___x_5162_);
lean_dec_ref(v___x_5160_);
lean_dec_ref(v___x_5158_);
lean_dec_ref(v___x_5156_);
lean_dec_ref(v___x_5154_);
lean_dec_ref(v_e_5139_);
goto v___jp_5151_;
}
else
{
lean_object* v___x_5164_; uint8_t v___x_5165_; 
v___x_5164_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5162_);
v___x_5165_ = l_Lean_Expr_isApp(v___x_5164_);
if (v___x_5165_ == 0)
{
lean_dec_ref(v___x_5164_);
lean_dec_ref(v___x_5162_);
lean_dec_ref(v___x_5160_);
lean_dec_ref(v___x_5158_);
lean_dec_ref(v___x_5156_);
lean_dec_ref(v___x_5154_);
lean_dec_ref(v_e_5139_);
goto v___jp_5151_;
}
else
{
lean_object* v___x_5166_; uint8_t v___x_5167_; 
v___x_5166_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5164_);
v___x_5167_ = l_Lean_Expr_isApp(v___x_5166_);
if (v___x_5167_ == 0)
{
lean_dec_ref(v___x_5166_);
lean_dec_ref(v___x_5164_);
lean_dec_ref(v___x_5162_);
lean_dec_ref(v___x_5160_);
lean_dec_ref(v___x_5158_);
lean_dec_ref(v___x_5156_);
lean_dec_ref(v___x_5154_);
lean_dec_ref(v_e_5139_);
goto v___jp_5151_;
}
else
{
lean_object* v___x_5168_; uint8_t v___x_5169_; 
v___x_5168_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5166_);
v___x_5169_ = l_Lean_Expr_isApp(v___x_5168_);
if (v___x_5169_ == 0)
{
lean_dec_ref(v___x_5168_);
lean_dec_ref(v___x_5166_);
lean_dec_ref(v___x_5164_);
lean_dec_ref(v___x_5162_);
lean_dec_ref(v___x_5160_);
lean_dec_ref(v___x_5158_);
lean_dec_ref(v___x_5156_);
lean_dec_ref(v___x_5154_);
lean_dec_ref(v_e_5139_);
goto v___jp_5151_;
}
else
{
lean_object* v___x_5170_; lean_object* v___x_5171_; uint8_t v___x_5172_; 
v___x_5170_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5168_);
v___x_5171_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetElem___closed__2));
v___x_5172_ = l_Lean_Expr_isConstOf(v___x_5170_, v___x_5171_);
if (v___x_5172_ == 0)
{
lean_dec_ref(v___x_5170_);
lean_dec_ref(v___x_5168_);
lean_dec_ref(v___x_5166_);
lean_dec_ref(v___x_5164_);
lean_dec_ref(v___x_5162_);
lean_dec_ref(v___x_5160_);
lean_dec_ref(v___x_5158_);
lean_dec_ref(v___x_5156_);
lean_dec_ref(v___x_5154_);
lean_dec_ref(v_e_5139_);
goto v___jp_5151_;
}
else
{
lean_object* v_arg_5173_; lean_object* v___x_5174_; uint8_t v___x_5175_; 
v_arg_5173_ = lean_ctor_get(v___x_5160_, 1);
lean_inc_ref(v_arg_5173_);
lean_dec_ref(v___x_5160_);
v___x_5174_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetElem___closed__4));
v___x_5175_ = l_Lean_Expr_isAppOf(v_arg_5173_, v___x_5174_);
if (v___x_5175_ == 0)
{
lean_object* v___x_5176_; lean_object* v___x_5177_; 
lean_dec_ref(v_arg_5173_);
lean_dec_ref(v___x_5170_);
lean_dec_ref(v___x_5168_);
lean_dec_ref(v___x_5166_);
lean_dec_ref(v___x_5164_);
lean_dec_ref(v___x_5162_);
lean_dec_ref(v___x_5158_);
lean_dec_ref(v___x_5156_);
lean_dec_ref(v___x_5154_);
lean_dec_ref(v_e_5139_);
v___x_5176_ = lean_box(0);
v___x_5177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5177_, 0, v___x_5176_);
return v___x_5177_;
}
else
{
lean_object* v_arg_5178_; lean_object* v_arg_5179_; lean_object* v_arg_5180_; lean_object* v_arg_5181_; lean_object* v_arg_5182_; lean_object* v_arg_5183_; lean_object* v_arg_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; 
v_arg_5178_ = lean_ctor_get(v___x_5154_, 1);
lean_inc_ref(v_arg_5178_);
lean_dec_ref(v___x_5154_);
v_arg_5179_ = lean_ctor_get(v___x_5156_, 1);
lean_inc_ref_n(v_arg_5179_, 2);
lean_dec_ref(v___x_5156_);
v_arg_5180_ = lean_ctor_get(v___x_5158_, 1);
lean_inc_ref(v_arg_5180_);
lean_dec_ref(v___x_5158_);
v_arg_5181_ = lean_ctor_get(v___x_5162_, 1);
lean_inc_ref(v_arg_5181_);
lean_dec_ref(v___x_5162_);
v_arg_5182_ = lean_ctor_get(v___x_5164_, 1);
lean_inc_ref(v_arg_5182_);
lean_dec_ref(v___x_5164_);
v_arg_5183_ = lean_ctor_get(v___x_5166_, 1);
lean_inc_ref(v_arg_5183_);
lean_dec_ref(v___x_5166_);
v_arg_5184_ = lean_ctor_get(v___x_5168_, 1);
lean_inc_ref(v_arg_5184_);
lean_dec_ref(v___x_5168_);
v___x_5185_ = lean_st_ref_get(v_a_5140_);
v___x_5186_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_5185_, v_arg_5179_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_);
lean_dec(v___x_5185_);
if (lean_obj_tag(v___x_5186_) == 0)
{
lean_object* v_a_5187_; lean_object* v___x_5188_; 
v_a_5187_ = lean_ctor_get(v___x_5186_, 0);
lean_inc(v_a_5187_);
lean_dec_ref_known(v___x_5186_, 1);
v___x_5188_ = l_Lean_Meta_getNatValue_x3f(v_a_5187_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_);
if (lean_obj_tag(v___x_5188_) == 0)
{
lean_object* v_a_5189_; lean_object* v___x_5191_; uint8_t v_isShared_5192_; uint8_t v_isSharedCheck_5284_; 
v_a_5189_ = lean_ctor_get(v___x_5188_, 0);
v_isSharedCheck_5284_ = !lean_is_exclusive(v___x_5188_);
if (v_isSharedCheck_5284_ == 0)
{
v___x_5191_ = v___x_5188_;
v_isShared_5192_ = v_isSharedCheck_5284_;
goto v_resetjp_5190_;
}
else
{
lean_inc(v_a_5189_);
lean_dec(v___x_5188_);
v___x_5191_ = lean_box(0);
v_isShared_5192_ = v_isSharedCheck_5284_;
goto v_resetjp_5190_;
}
v_resetjp_5190_:
{
if (lean_obj_tag(v_a_5189_) == 1)
{
lean_object* v_val_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; 
lean_del_object(v___x_5191_);
v_val_5193_ = lean_ctor_get(v_a_5189_, 0);
lean_inc(v_val_5193_);
lean_dec_ref_known(v_a_5189_, 1);
v___x_5194_ = lean_st_ref_get(v_a_5140_);
lean_inc_ref(v_arg_5180_);
v___x_5195_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_5194_, v_arg_5180_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_);
lean_dec(v___x_5194_);
if (lean_obj_tag(v___x_5195_) == 0)
{
lean_object* v_a_5196_; lean_object* v___x_5197_; 
v_a_5196_ = lean_ctor_get(v___x_5195_, 0);
lean_inc_n(v_a_5196_, 2);
lean_dec_ref_known(v___x_5195_, 1);
v___x_5197_ = l_Lean_Meta_getBitVecValue_x3f(v_a_5196_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_);
if (lean_obj_tag(v___x_5197_) == 0)
{
lean_object* v_a_5198_; lean_object* v___x_5200_; uint8_t v_isShared_5201_; uint8_t v_isSharedCheck_5263_; 
v_a_5198_ = lean_ctor_get(v___x_5197_, 0);
v_isSharedCheck_5263_ = !lean_is_exclusive(v___x_5197_);
if (v_isSharedCheck_5263_ == 0)
{
v___x_5200_ = v___x_5197_;
v_isShared_5201_ = v_isSharedCheck_5263_;
goto v_resetjp_5199_;
}
else
{
lean_inc(v_a_5198_);
lean_dec(v___x_5197_);
v___x_5200_ = lean_box(0);
v_isShared_5201_ = v_isSharedCheck_5263_;
goto v_resetjp_5199_;
}
v_resetjp_5199_:
{
if (lean_obj_tag(v_a_5198_) == 1)
{
lean_object* v_val_5202_; lean_object* v_fst_5203_; lean_object* v_snd_5204_; uint8_t v___x_5205_; 
v_val_5202_ = lean_ctor_get(v_a_5198_, 0);
lean_inc(v_val_5202_);
lean_dec_ref_known(v_a_5198_, 1);
v_fst_5203_ = lean_ctor_get(v_val_5202_, 0);
lean_inc(v_fst_5203_);
v_snd_5204_ = lean_ctor_get(v_val_5202_, 1);
lean_inc(v_snd_5204_);
lean_dec(v_val_5202_);
v___x_5205_ = lean_nat_dec_lt(v_val_5193_, v_fst_5203_);
lean_dec(v_fst_5203_);
if (v___x_5205_ == 0)
{
lean_object* v___x_5206_; lean_object* v___x_5208_; 
lean_dec(v_snd_5204_);
lean_dec(v_a_5196_);
lean_dec(v_val_5193_);
lean_dec(v_a_5187_);
lean_dec_ref(v_arg_5184_);
lean_dec_ref(v_arg_5183_);
lean_dec_ref(v_arg_5182_);
lean_dec_ref(v_arg_5181_);
lean_dec_ref(v_arg_5180_);
lean_dec_ref(v_arg_5179_);
lean_dec_ref(v_arg_5178_);
lean_dec_ref(v_arg_5173_);
lean_dec_ref(v___x_5170_);
lean_dec_ref(v_e_5139_);
v___x_5206_ = lean_box(0);
if (v_isShared_5201_ == 0)
{
lean_ctor_set(v___x_5200_, 0, v___x_5206_);
v___x_5208_ = v___x_5200_;
goto v_reusejp_5207_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v___x_5206_);
v___x_5208_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5207_;
}
v_reusejp_5207_:
{
return v___x_5208_;
}
}
else
{
uint8_t v___x_5210_; lean_object* v___x_5211_; 
lean_del_object(v___x_5200_);
v___x_5210_ = l_Nat_testBit(v_snd_5204_, v_val_5193_);
lean_dec(v_val_5193_);
lean_dec(v_snd_5204_);
v___x_5211_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v___x_5210_, v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_);
if (lean_obj_tag(v___x_5211_) == 0)
{
lean_object* v_a_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; 
v_a_5212_ = lean_ctor_get(v___x_5211_, 0);
lean_inc_n(v_a_5212_, 2);
lean_dec_ref_known(v___x_5211_, 1);
v___x_5213_ = lean_unsigned_to_nat(0u);
v___x_5214_ = lean_box(0);
lean_inc(v_a_5149_);
lean_inc_ref(v_a_5148_);
lean_inc(v_a_5147_);
lean_inc_ref(v_a_5146_);
lean_inc(v_a_5145_);
lean_inc_ref(v_a_5144_);
lean_inc(v_a_5143_);
lean_inc_ref(v_a_5142_);
lean_inc(v_a_5141_);
lean_inc(v_a_5140_);
v___x_5215_ = lean_grind_internalize(v_a_5212_, v___x_5213_, v___x_5214_, v_a_5140_, v_a_5141_, v_a_5142_, v_a_5143_, v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_);
if (lean_obj_tag(v___x_5215_) == 0)
{
lean_object* v___x_5216_; uint8_t v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; 
lean_dec_ref_known(v___x_5215_, 1);
v___x_5216_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetElem___closed__6));
v___x_5217_ = 0;
lean_inc_n(v_a_5187_, 2);
lean_inc_n(v_a_5196_, 2);
lean_inc_ref(v_arg_5181_);
v___x_5218_ = l_Lean_mkAppB(v_arg_5181_, v_a_5196_, v_a_5187_);
v___x_5219_ = l_Lean_Expr_headBeta(v___x_5218_);
v___x_5220_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11);
lean_inc_n(v_a_5212_, 2);
lean_inc_ref(v_arg_5182_);
v___x_5221_ = l_Lean_mkAppB(v___x_5220_, v_arg_5182_, v_a_5212_);
v___x_5222_ = l_Lean_mkLambda(v___x_5216_, v___x_5217_, v___x_5219_, v___x_5221_);
v___x_5223_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetElem___closed__8));
v___x_5224_ = l_Lean_Expr_constLevels_x21(v___x_5170_);
lean_dec_ref(v___x_5170_);
v___x_5225_ = l_Lean_mkConst(v___x_5223_, v___x_5224_);
lean_inc_ref(v_arg_5180_);
v___x_5226_ = l_Lean_mkApp6(v___x_5225_, v_arg_5184_, v_arg_5183_, v_arg_5182_, v_arg_5181_, v_arg_5173_, v_arg_5180_);
lean_inc_ref(v_arg_5179_);
v___x_5227_ = l_Lean_mkApp5(v___x_5226_, v_a_5196_, v_arg_5179_, v_a_5187_, v_arg_5178_, v_a_5212_);
lean_inc(v_a_5149_);
lean_inc_ref(v_a_5148_);
lean_inc(v_a_5147_);
lean_inc_ref(v_a_5146_);
lean_inc(v_a_5145_);
lean_inc_ref(v_a_5144_);
lean_inc(v_a_5143_);
lean_inc_ref(v_a_5142_);
lean_inc(v_a_5141_);
lean_inc(v_a_5140_);
v___x_5228_ = lean_grind_mk_eq_proof(v_arg_5180_, v_a_5196_, v_a_5140_, v_a_5141_, v_a_5142_, v_a_5143_, v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_);
if (lean_obj_tag(v___x_5228_) == 0)
{
lean_object* v_a_5229_; lean_object* v___x_5230_; 
v_a_5229_ = lean_ctor_get(v___x_5228_, 0);
lean_inc(v_a_5229_);
lean_dec_ref_known(v___x_5228_, 1);
lean_inc(v_a_5149_);
lean_inc_ref(v_a_5148_);
lean_inc(v_a_5147_);
lean_inc_ref(v_a_5146_);
lean_inc(v_a_5145_);
lean_inc_ref(v_a_5144_);
lean_inc(v_a_5143_);
lean_inc_ref(v_a_5142_);
lean_inc(v_a_5141_);
lean_inc(v_a_5140_);
v___x_5230_ = lean_grind_mk_eq_proof(v_arg_5179_, v_a_5187_, v_a_5140_, v_a_5141_, v_a_5142_, v_a_5143_, v_a_5144_, v_a_5145_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_);
if (lean_obj_tag(v___x_5230_) == 0)
{
lean_object* v_a_5231_; lean_object* v___x_5232_; uint8_t v___x_5233_; lean_object* v___x_5234_; 
v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
lean_inc(v_a_5231_);
lean_dec_ref_known(v___x_5230_, 1);
v___x_5232_ = l_Lean_mkApp3(v___x_5227_, v_a_5229_, v_a_5231_, v___x_5222_);
v___x_5233_ = 0;
v___x_5234_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_5139_, v_a_5212_, v___x_5232_, v___x_5233_, v_a_5140_, v_a_5142_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_);
return v___x_5234_;
}
else
{
lean_object* v_a_5235_; lean_object* v___x_5237_; uint8_t v_isShared_5238_; uint8_t v_isSharedCheck_5242_; 
lean_dec(v_a_5229_);
lean_dec_ref(v___x_5227_);
lean_dec_ref(v___x_5222_);
lean_dec(v_a_5212_);
lean_dec_ref(v_e_5139_);
v_a_5235_ = lean_ctor_get(v___x_5230_, 0);
v_isSharedCheck_5242_ = !lean_is_exclusive(v___x_5230_);
if (v_isSharedCheck_5242_ == 0)
{
v___x_5237_ = v___x_5230_;
v_isShared_5238_ = v_isSharedCheck_5242_;
goto v_resetjp_5236_;
}
else
{
lean_inc(v_a_5235_);
lean_dec(v___x_5230_);
v___x_5237_ = lean_box(0);
v_isShared_5238_ = v_isSharedCheck_5242_;
goto v_resetjp_5236_;
}
v_resetjp_5236_:
{
lean_object* v___x_5240_; 
if (v_isShared_5238_ == 0)
{
v___x_5240_ = v___x_5237_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5241_; 
v_reuseFailAlloc_5241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5241_, 0, v_a_5235_);
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
lean_dec_ref(v___x_5227_);
lean_dec_ref(v___x_5222_);
lean_dec(v_a_5212_);
lean_dec(v_a_5187_);
lean_dec_ref(v_arg_5179_);
lean_dec_ref(v_e_5139_);
v_a_5243_ = lean_ctor_get(v___x_5228_, 0);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5228_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_5245_ = v___x_5228_;
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v___x_5228_);
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
lean_dec(v_a_5212_);
lean_dec(v_a_5196_);
lean_dec(v_a_5187_);
lean_dec_ref(v_arg_5184_);
lean_dec_ref(v_arg_5183_);
lean_dec_ref(v_arg_5182_);
lean_dec_ref(v_arg_5181_);
lean_dec_ref(v_arg_5180_);
lean_dec_ref(v_arg_5179_);
lean_dec_ref(v_arg_5178_);
lean_dec_ref(v_arg_5173_);
lean_dec_ref(v___x_5170_);
lean_dec_ref(v_e_5139_);
return v___x_5215_;
}
}
else
{
lean_object* v_a_5251_; lean_object* v___x_5253_; uint8_t v_isShared_5254_; uint8_t v_isSharedCheck_5258_; 
lean_dec(v_a_5196_);
lean_dec(v_a_5187_);
lean_dec_ref(v_arg_5184_);
lean_dec_ref(v_arg_5183_);
lean_dec_ref(v_arg_5182_);
lean_dec_ref(v_arg_5181_);
lean_dec_ref(v_arg_5180_);
lean_dec_ref(v_arg_5179_);
lean_dec_ref(v_arg_5178_);
lean_dec_ref(v_arg_5173_);
lean_dec_ref(v___x_5170_);
lean_dec_ref(v_e_5139_);
v_a_5251_ = lean_ctor_get(v___x_5211_, 0);
v_isSharedCheck_5258_ = !lean_is_exclusive(v___x_5211_);
if (v_isSharedCheck_5258_ == 0)
{
v___x_5253_ = v___x_5211_;
v_isShared_5254_ = v_isSharedCheck_5258_;
goto v_resetjp_5252_;
}
else
{
lean_inc(v_a_5251_);
lean_dec(v___x_5211_);
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
}
else
{
lean_object* v___x_5259_; lean_object* v___x_5261_; 
lean_dec(v_a_5198_);
lean_dec(v_a_5196_);
lean_dec(v_val_5193_);
lean_dec(v_a_5187_);
lean_dec_ref(v_arg_5184_);
lean_dec_ref(v_arg_5183_);
lean_dec_ref(v_arg_5182_);
lean_dec_ref(v_arg_5181_);
lean_dec_ref(v_arg_5180_);
lean_dec_ref(v_arg_5179_);
lean_dec_ref(v_arg_5178_);
lean_dec_ref(v_arg_5173_);
lean_dec_ref(v___x_5170_);
lean_dec_ref(v_e_5139_);
v___x_5259_ = lean_box(0);
if (v_isShared_5201_ == 0)
{
lean_ctor_set(v___x_5200_, 0, v___x_5259_);
v___x_5261_ = v___x_5200_;
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
lean_dec(v_a_5196_);
lean_dec(v_val_5193_);
lean_dec(v_a_5187_);
lean_dec_ref(v_arg_5184_);
lean_dec_ref(v_arg_5183_);
lean_dec_ref(v_arg_5182_);
lean_dec_ref(v_arg_5181_);
lean_dec_ref(v_arg_5180_);
lean_dec_ref(v_arg_5179_);
lean_dec_ref(v_arg_5178_);
lean_dec_ref(v_arg_5173_);
lean_dec_ref(v___x_5170_);
lean_dec_ref(v_e_5139_);
v_a_5264_ = lean_ctor_get(v___x_5197_, 0);
v_isSharedCheck_5271_ = !lean_is_exclusive(v___x_5197_);
if (v_isSharedCheck_5271_ == 0)
{
v___x_5266_ = v___x_5197_;
v_isShared_5267_ = v_isSharedCheck_5271_;
goto v_resetjp_5265_;
}
else
{
lean_inc(v_a_5264_);
lean_dec(v___x_5197_);
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
lean_dec(v_val_5193_);
lean_dec(v_a_5187_);
lean_dec_ref(v_arg_5184_);
lean_dec_ref(v_arg_5183_);
lean_dec_ref(v_arg_5182_);
lean_dec_ref(v_arg_5181_);
lean_dec_ref(v_arg_5180_);
lean_dec_ref(v_arg_5179_);
lean_dec_ref(v_arg_5178_);
lean_dec_ref(v_arg_5173_);
lean_dec_ref(v___x_5170_);
lean_dec_ref(v_e_5139_);
v_a_5272_ = lean_ctor_get(v___x_5195_, 0);
v_isSharedCheck_5279_ = !lean_is_exclusive(v___x_5195_);
if (v_isSharedCheck_5279_ == 0)
{
v___x_5274_ = v___x_5195_;
v_isShared_5275_ = v_isSharedCheck_5279_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_a_5272_);
lean_dec(v___x_5195_);
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
else
{
lean_object* v___x_5280_; lean_object* v___x_5282_; 
lean_dec(v_a_5189_);
lean_dec(v_a_5187_);
lean_dec_ref(v_arg_5184_);
lean_dec_ref(v_arg_5183_);
lean_dec_ref(v_arg_5182_);
lean_dec_ref(v_arg_5181_);
lean_dec_ref(v_arg_5180_);
lean_dec_ref(v_arg_5179_);
lean_dec_ref(v_arg_5178_);
lean_dec_ref(v_arg_5173_);
lean_dec_ref(v___x_5170_);
lean_dec_ref(v_e_5139_);
v___x_5280_ = lean_box(0);
if (v_isShared_5192_ == 0)
{
lean_ctor_set(v___x_5191_, 0, v___x_5280_);
v___x_5282_ = v___x_5191_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v___x_5280_);
v___x_5282_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
return v___x_5282_;
}
}
}
}
else
{
lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5292_; 
lean_dec(v_a_5187_);
lean_dec_ref(v_arg_5184_);
lean_dec_ref(v_arg_5183_);
lean_dec_ref(v_arg_5182_);
lean_dec_ref(v_arg_5181_);
lean_dec_ref(v_arg_5180_);
lean_dec_ref(v_arg_5179_);
lean_dec_ref(v_arg_5178_);
lean_dec_ref(v_arg_5173_);
lean_dec_ref(v___x_5170_);
lean_dec_ref(v_e_5139_);
v_a_5285_ = lean_ctor_get(v___x_5188_, 0);
v_isSharedCheck_5292_ = !lean_is_exclusive(v___x_5188_);
if (v_isSharedCheck_5292_ == 0)
{
v___x_5287_ = v___x_5188_;
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_dec(v___x_5188_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5290_; 
if (v_isShared_5288_ == 0)
{
v___x_5290_ = v___x_5287_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5291_; 
v_reuseFailAlloc_5291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5291_, 0, v_a_5285_);
v___x_5290_ = v_reuseFailAlloc_5291_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
return v___x_5290_;
}
}
}
}
else
{
lean_object* v_a_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5300_; 
lean_dec_ref(v_arg_5184_);
lean_dec_ref(v_arg_5183_);
lean_dec_ref(v_arg_5182_);
lean_dec_ref(v_arg_5181_);
lean_dec_ref(v_arg_5180_);
lean_dec_ref(v_arg_5179_);
lean_dec_ref(v_arg_5178_);
lean_dec_ref(v_arg_5173_);
lean_dec_ref(v___x_5170_);
lean_dec_ref(v_e_5139_);
v_a_5293_ = lean_ctor_get(v___x_5186_, 0);
v_isSharedCheck_5300_ = !lean_is_exclusive(v___x_5186_);
if (v_isSharedCheck_5300_ == 0)
{
v___x_5295_ = v___x_5186_;
v_isShared_5296_ = v_isSharedCheck_5300_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_a_5293_);
lean_dec(v___x_5186_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5300_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v___x_5298_; 
if (v_isShared_5296_ == 0)
{
v___x_5298_ = v___x_5295_;
goto v_reusejp_5297_;
}
else
{
lean_object* v_reuseFailAlloc_5299_; 
v_reuseFailAlloc_5299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_a_5293_);
v___x_5298_ = v_reuseFailAlloc_5299_;
goto v_reusejp_5297_;
}
v_reusejp_5297_:
{
return v___x_5298_;
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
v___jp_5151_:
{
lean_object* v___x_5152_; lean_object* v___x_5153_; 
v___x_5152_ = lean_box(0);
v___x_5153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5153_, 0, v___x_5152_);
return v___x_5153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetElem___boxed(lean_object* v_e_5301_, lean_object* v_a_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_, lean_object* v_a_5305_, lean_object* v_a_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_){
_start:
{
lean_object* v_res_5313_; 
v_res_5313_ = l_Lean_Meta_Grind_propagateBVGetElem(v_e_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_, v_a_5310_, v_a_5311_);
lean_dec(v_a_5311_);
lean_dec_ref(v_a_5310_);
lean_dec(v_a_5309_);
lean_dec_ref(v_a_5308_);
lean_dec(v_a_5307_);
lean_dec_ref(v_a_5306_);
lean_dec(v_a_5305_);
lean_dec_ref(v_a_5304_);
lean_dec(v_a_5303_);
lean_dec(v_a_5302_);
return v_res_5313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetElem___regBuiltin_Lean_Meta_Grind_propagateBVGetElem_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2454187461____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; 
v___x_5315_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetElem___closed__2));
v___x_5316_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVGetElem___boxed), 12, 0);
v___x_5317_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_5315_, v___x_5316_);
return v___x_5317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetElem___regBuiltin_Lean_Meta_Grind_propagateBVGetElem_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2454187461____hygCtx___hyg_9____boxed(lean_object* v_a_5318_){
_start:
{
lean_object* v_res_5319_; 
v_res_5319_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetElem___regBuiltin_Lean_Meta_Grind_propagateBVGetElem_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2454187461____hygCtx___hyg_9_();
return v_res_5319_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_ToExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
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
res = runtime_initialize_Lean_Util_SafeExponentiation(builtin);
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
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1883179728____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4268766526____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2693654335____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2382349498____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_281236239____hygCtx___hyg_9_();
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
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1194477106____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3514232501____hygCtx___hyg_9_();
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
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3470952822____hygCtx___hyg_9_();
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
lean_object* initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
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
res = initialize_Lean_Util_SafeExponentiation(builtin);
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
