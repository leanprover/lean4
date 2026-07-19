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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_BitVec_append___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_BitVec_extractLsb___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_BitVec_signExtend(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_BitVec_rotateLeft(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_clz(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_BitVec_cpop(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_BitVec_replicate(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_setWidth(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofInt(lean_object*, lean_object*);
lean_object* l_BitVec_extractLsb_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_sshiftRight(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_not(lean_object*, lean_object*);
lean_object* l_BitVec_toInt(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVNot___regBuiltin_Lean_Meta_Grind_propagateBVNot_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_524020944____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVNot___regBuiltin_Lean_Meta_Grind_propagateBVNot_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_524020944____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVClz___regBuiltin_Lean_Meta_Grind_propagateBVClz_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3163129259____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVClz___regBuiltin_Lean_Meta_Grind_propagateBVClz_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3163129259____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVCpop___regBuiltin_Lean_Meta_Grind_propagateBVCpop_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4094280043____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVCpop___regBuiltin_Lean_Meta_Grind_propagateBVCpop_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4094280043____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVMsb___regBuiltin_Lean_Meta_Grind_propagateBVMsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1379739246____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVMsb___regBuiltin_Lean_Meta_Grind_propagateBVMsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1379739246____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToNat___regBuiltin_Lean_Meta_Grind_propagateBVToNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1265925494____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToNat___regBuiltin_Lean_Meta_Grind_propagateBVToNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1265925494____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToInt___regBuiltin_Lean_Meta_Grind_propagateBVToInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2998338308____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToInt___regBuiltin_Lean_Meta_Grind_propagateBVToInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2998338308____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVOfNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Grind_propagateBVOfNat___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVOfNat___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVOfNat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVOfNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVOfNat___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVOfNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVOfNat___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVOfNat___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1693823724____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1693823724____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVOfInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofInt"};
static const lean_object* l_Lean_Meta_Grind_propagateBVOfInt___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVOfInt___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVOfInt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVOfInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVOfInt___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVOfInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 33, 171, 14, 158, 104, 202, 91)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVOfInt___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVOfInt___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_16048587____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_16048587____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVSetWidth___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "setWidth"};
static const lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVSetWidth___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVSetWidth___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVSetWidth___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVSetWidth___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVSetWidth___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 6, 252, 142, 19, 176, 54, 12)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVSetWidth___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVSignExtend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "signExtend"};
static const lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVSignExtend___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVSignExtend___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVSignExtend___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVSignExtend___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVSignExtend___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 113, 32, 164, 54, 200, 3, 175)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVSignExtend___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "extractLsb'"};
static const lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 201, 218, 12, 248, 124, 75, 23)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4241407876____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4241407876____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVExtractLsb___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "extractLsb"};
static const lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 192, 253, 234, 186, 255, 105, 184)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3429100332____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3429100332____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateBVReplicate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "replicate"};
static const lean_object* l_Lean_Meta_Grind_propagateBVReplicate___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVReplicate___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVReplicate___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVReplicate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVReplicate___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_propagateBVReplicate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 123, 74, 120, 175, 214, 39, 20)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVReplicate___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVReplicate___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3327375609____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3327375609____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAnd___regBuiltin_Lean_Meta_Grind_propagateBVAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_317501673____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAnd___regBuiltin_Lean_Meta_Grind_propagateBVAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_317501673____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOr___regBuiltin_Lean_Meta_Grind_propagateBVOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4272827602____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOr___regBuiltin_Lean_Meta_Grind_propagateBVOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4272827602____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVXor___regBuiltin_Lean_Meta_Grind_propagateBVXor_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1120302969____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVXor___regBuiltin_Lean_Meta_Grind_propagateBVXor_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1120302969____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4057925374____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4057925374____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3262547096____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3262547096____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVUShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVUShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1878785357____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVUShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVUShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1878785357____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVSShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3342532823____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVSShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3342532823____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateLeft___regBuiltin_Lean_Meta_Grind_propagateBVRotateLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1541346404____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateLeft___regBuiltin_Lean_Meta_Grind_propagateBVRotateLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1541346404____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateRight___regBuiltin_Lean_Meta_Grind_propagateBVRotateRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2456321972____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateRight___regBuiltin_Lean_Meta_Grind_propagateBVRotateRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2456321972____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2458924947____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2458924947____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVHShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1131064821____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVHShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1131064821____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetLsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetLsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1075602488____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetLsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetLsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1075602488____hygCtx___hyg_8____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetMsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetMsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1507361668____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetMsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetMsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1507361668____hygCtx___hyg_8____boxed(lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_propagateBVGetElem___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "getElem_congr"};
static const lean_object* l_Lean_Meta_Grind_propagateBVGetElem___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVGetElem___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVGetElem___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVGetElem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__5_value),LEAN_SCALAR_PTR_LITERAL(245, 93, 18, 95, 170, 237, 152, 145)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVGetElem___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_propagateBVGetElem___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "w"};
static const lean_object* l_Lean_Meta_Grind_propagateBVGetElem___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_propagateBVGetElem___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__7_value),LEAN_SCALAR_PTR_LITERAL(238, 128, 149, 182, 175, 207, 218, 129)}};
static const lean_object* l_Lean_Meta_Grind_propagateBVGetElem___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_propagateBVGetElem___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetElem___regBuiltin_Lean_Meta_Grind_propagateBVGetElem_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2454187461____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetElem___regBuiltin_Lean_Meta_Grind_propagateBVGetElem_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2454187461____hygCtx___hyg_8____boxed(lean_object*);
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
lean_object* v___x_216_; lean_object* v_a_217_; lean_object* v___x_218_; 
v___x_216_ = lean_st_ref_get(v_a_205_);
v_a_217_ = l_Lean_Expr_appArg_x21(v_e_203_);
lean_inc_ref(v_a_217_);
v___x_218_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_216_, v_a_217_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
lean_dec(v___x_216_);
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
lean_inc_ref(v_a_217_);
v___x_231_ = lean_infer_type(v_a_217_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
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
lean_inc_ref(v_a_217_);
lean_inc(v_a_230_);
v___x_235_ = l_Lean_mkApp6(v___x_233_, v_a_232_, v_a_230_, v___x_234_, v_a_217_, v_a_219_, v_val_225_);
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
v___x_236_ = lean_grind_mk_eq_proof(v_a_217_, v_a_219_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
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
lean_dec_ref(v_a_217_);
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
lean_dec_ref(v_a_217_);
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
lean_dec_ref(v_a_217_);
lean_dec_ref(v_e_203_);
return v___x_228_;
}
}
else
{
lean_object* v___x_267_; lean_object* v___x_269_; 
lean_dec(v_a_221_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_217_);
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
lean_dec_ref(v_a_217_);
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
lean_dec_ref(v_a_217_);
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
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_a_u2081_328_; lean_object* v___x_329_; 
v___x_326_ = lean_st_ref_get(v_a_315_);
v___x_327_ = l_Lean_Expr_appFn_x21(v_e_313_);
v_a_u2081_328_ = l_Lean_Expr_appArg_x21(v___x_327_);
lean_inc_ref(v_a_u2081_328_);
v___x_329_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_326_, v_a_u2081_328_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v___x_326_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_331_; lean_object* v_a_u2082_332_; lean_object* v___x_333_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_329_, 1);
v___x_331_ = lean_st_ref_get(v_a_315_);
v_a_u2082_332_ = l_Lean_Expr_appArg_x21(v_e_313_);
lean_inc_ref(v_a_u2082_332_);
v___x_333_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_331_, v_a_u2082_332_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v___x_331_);
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
lean_inc(v_a_330_);
v___x_335_ = lean_apply_13(v_eval_314_, v_a_330_, v_a_334_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, lean_box(0));
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
lean_inc_ref(v_a_u2082_332_);
v___x_348_ = lean_infer_type(v_a_u2082_332_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
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
lean_inc_ref(v_a_u2082_332_);
lean_inc(v_a_330_);
lean_inc_ref(v_a_u2081_328_);
lean_inc(v_a_345_);
v___x_352_ = l_Lean_mkApp9(v___x_350_, v_a_347_, v_a_349_, v_a_345_, v___x_351_, v_a_u2081_328_, v_a_330_, v_a_u2082_332_, v_a_334_, v_val_340_);
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
v___x_353_ = lean_grind_mk_eq_proof(v_a_u2081_328_, v_a_330_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
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
v___x_355_ = lean_grind_mk_eq_proof(v_a_u2082_332_, v_a_334_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
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
lean_dec_ref(v_a_u2082_332_);
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
lean_dec_ref(v_a_u2082_332_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_u2081_328_);
lean_dec_ref(v___x_327_);
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
lean_dec_ref(v_a_u2082_332_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_u2081_328_);
lean_dec_ref(v___x_327_);
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
lean_dec_ref(v_a_u2082_332_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_u2081_328_);
lean_dec_ref(v___x_327_);
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
lean_dec_ref(v_a_u2082_332_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_u2081_328_);
lean_dec_ref(v___x_327_);
lean_dec_ref(v_e_313_);
return v___x_343_;
}
}
else
{
lean_object* v___x_402_; lean_object* v___x_404_; 
lean_dec(v_a_336_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_u2082_332_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_u2081_328_);
lean_dec_ref(v___x_327_);
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
lean_dec_ref(v_a_u2082_332_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_u2081_328_);
lean_dec_ref(v___x_327_);
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
lean_dec_ref(v_a_u2082_332_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_u2081_328_);
lean_dec_ref(v___x_327_);
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
lean_dec_ref(v_eval_314_);
lean_dec_ref(v_e_313_);
v_a_423_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_329_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_329_);
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
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_664_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_664_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_664_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_664_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
if (lean_obj_tag(v_a_653_) == 1)
{
lean_object* v_val_657_; lean_object* v___f_658_; lean_object* v___x_659_; 
lean_del_object(v___x_655_);
v_val_657_ = lean_ctor_get(v_a_653_, 0);
lean_inc(v_val_657_);
lean_dec_ref_known(v_a_653_, 1);
v___f_658_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV___lam__0___boxed), 14, 2);
lean_closure_set(v___f_658_, 0, v_op_630_);
lean_closure_set(v___f_658_, 1, v_val_657_);
v___x_659_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_631_, v___f_658_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
return v___x_659_;
}
else
{
lean_object* v___x_660_; lean_object* v___x_662_; 
lean_dec(v_a_653_);
lean_dec_ref(v_e_631_);
lean_dec_ref(v_op_630_);
v___x_660_ = lean_box(0);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_660_);
v___x_662_ = v___x_655_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref(v_e_631_);
lean_dec_ref(v_op_630_);
v_a_665_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_652_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_652_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV___boxed(lean_object* v_declName_673_, lean_object* v_op_674_, lean_object* v_e_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extendBV(v_declName_673_, v_op_674_, v_e_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec(v_a_676_);
lean_dec(v_declName_673_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0(lean_object* v_op_688_, lean_object* v_val_689_, lean_object* v_val_690_, lean_object* v_r_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_Meta_getBitVecValue_x3f(v_r_691_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_742_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_742_ == 0)
{
v___x_706_ = v___x_703_;
v_isShared_707_ = v_isSharedCheck_742_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_703_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_742_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
if (lean_obj_tag(v_a_704_) == 1)
{
lean_object* v_val_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_737_; 
lean_del_object(v___x_706_);
v_val_708_ = lean_ctor_get(v_a_704_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v_a_704_);
if (v_isSharedCheck_737_ == 0)
{
v___x_710_ = v_a_704_;
v_isShared_711_ = v_isSharedCheck_737_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_val_708_);
lean_dec(v_a_704_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_737_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v_fst_712_; lean_object* v_snd_713_; lean_object* v___x_714_; lean_object* v_fst_715_; lean_object* v_snd_716_; lean_object* v___x_717_; 
v_fst_712_ = lean_ctor_get(v_val_708_, 0);
lean_inc(v_fst_712_);
v_snd_713_ = lean_ctor_get(v_val_708_, 1);
lean_inc(v_snd_713_);
lean_dec(v_val_708_);
v___x_714_ = lean_apply_4(v_op_688_, v_fst_712_, v_val_689_, v_val_690_, v_snd_713_);
v_fst_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_fst_715_);
v_snd_716_ = lean_ctor_get(v___x_714_, 1);
lean_inc(v_snd_716_);
lean_dec_ref(v___x_714_);
v___x_717_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_715_, v_snd_716_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_728_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_728_ == 0)
{
v___x_720_ = v___x_717_;
v_isShared_721_ = v_isSharedCheck_728_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_728_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v_a_718_);
v___x_723_ = v___x_710_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_727_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_725_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_723_);
v___x_725_ = v___x_720_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_del_object(v___x_710_);
v_a_729_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_717_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_717_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
else
{
lean_object* v___x_738_; lean_object* v___x_740_; 
lean_dec(v_a_704_);
lean_dec(v_val_690_);
lean_dec(v_val_689_);
lean_dec_ref(v_op_688_);
v___x_738_ = lean_box(0);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_738_);
v___x_740_ = v___x_706_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec(v_val_690_);
lean_dec(v_val_689_);
lean_dec_ref(v_op_688_);
v_a_743_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_703_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_703_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0___boxed(lean_object* v_op_751_, lean_object* v_val_752_, lean_object* v_val_753_, lean_object* v_r_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0(v_op_751_, v_val_752_, v_val_753_, v_r_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec(v___y_755_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV(lean_object* v_declName_767_, lean_object* v_op_768_, lean_object* v_e_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_781_ = lean_unsigned_to_nat(4u);
v___x_782_ = l_Lean_Expr_isAppOfArity(v_e_769_, v_declName_767_, v___x_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec_ref(v_e_769_);
lean_dec_ref(v_op_768_);
v___x_783_ = lean_box(0);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_785_ = lean_unsigned_to_nat(1u);
v___x_786_ = l_Lean_Expr_getAppNumArgs(v_e_769_);
v___x_787_ = lean_nat_sub(v___x_786_, v___x_785_);
v___x_788_ = lean_nat_sub(v___x_787_, v___x_785_);
lean_dec(v___x_787_);
v___x_789_ = l_Lean_Expr_getRevArg_x21(v_e_769_, v___x_788_);
v___x_790_ = l_Lean_Meta_getNatValue_x3f(v___x_789_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
lean_dec_ref(v___x_789_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_825_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_825_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_825_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_825_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
if (lean_obj_tag(v_a_791_) == 1)
{
lean_object* v_val_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_del_object(v___x_793_);
v_val_795_ = lean_ctor_get(v_a_791_, 0);
lean_inc(v_val_795_);
lean_dec_ref_known(v_a_791_, 1);
v___x_796_ = lean_unsigned_to_nat(2u);
v___x_797_ = lean_nat_sub(v___x_786_, v___x_796_);
lean_dec(v___x_786_);
v___x_798_ = lean_nat_sub(v___x_797_, v___x_785_);
lean_dec(v___x_797_);
v___x_799_ = l_Lean_Expr_getRevArg_x21(v_e_769_, v___x_798_);
v___x_800_ = l_Lean_Meta_getNatValue_x3f(v___x_799_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
lean_dec_ref(v___x_799_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_812_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_812_ == 0)
{
v___x_803_ = v___x_800_;
v_isShared_804_ = v_isSharedCheck_812_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_800_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_812_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
if (lean_obj_tag(v_a_801_) == 1)
{
lean_object* v_val_805_; lean_object* v___f_806_; lean_object* v___x_807_; 
lean_del_object(v___x_803_);
v_val_805_ = lean_ctor_get(v_a_801_, 0);
lean_inc(v_val_805_);
lean_dec_ref_known(v_a_801_, 1);
v___f_806_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___lam__0___boxed), 15, 3);
lean_closure_set(v___f_806_, 0, v_op_768_);
lean_closure_set(v___f_806_, 1, v_val_795_);
lean_closure_set(v___f_806_, 2, v_val_805_);
v___x_807_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_769_, v___f_806_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
return v___x_807_;
}
else
{
lean_object* v___x_808_; lean_object* v___x_810_; 
lean_dec(v_a_801_);
lean_dec(v_val_795_);
lean_dec_ref(v_e_769_);
lean_dec_ref(v_op_768_);
v___x_808_ = lean_box(0);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_808_);
v___x_810_ = v___x_803_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec(v_val_795_);
lean_dec_ref(v_e_769_);
lean_dec_ref(v_op_768_);
v_a_813_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_800_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_800_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
else
{
lean_object* v___x_821_; lean_object* v___x_823_; 
lean_dec(v_a_791_);
lean_dec(v___x_786_);
lean_dec_ref(v_e_769_);
lean_dec_ref(v_op_768_);
v___x_821_ = lean_box(0);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_821_);
v___x_823_ = v___x_793_;
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
lean_dec(v___x_786_);
lean_dec_ref(v_e_769_);
lean_dec_ref(v_op_768_);
v_a_826_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_790_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_790_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV___boxed(lean_object* v_declName_834_, lean_object* v_op_835_, lean_object* v_e_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_extractBV(v_declName_834_, v_op_835_, v_e_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec(v_a_837_);
lean_dec(v_declName_834_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0(lean_object* v_op_849_, lean_object* v_r_u2081_850_, lean_object* v_r_u2082_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_850_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_926_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_926_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_926_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_926_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
if (lean_obj_tag(v_a_864_) == 1)
{
lean_object* v_val_868_; lean_object* v_fst_869_; lean_object* v_snd_870_; lean_object* v___x_871_; 
lean_del_object(v___x_866_);
v_val_868_ = lean_ctor_get(v_a_864_, 0);
lean_inc(v_val_868_);
lean_dec_ref_known(v_a_864_, 1);
v_fst_869_ = lean_ctor_get(v_val_868_, 0);
lean_inc(v_fst_869_);
v_snd_870_ = lean_ctor_get(v_val_868_, 1);
lean_inc(v_snd_870_);
lean_dec(v_val_868_);
v___x_871_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_851_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_913_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_913_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_913_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_913_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
if (lean_obj_tag(v_a_872_) == 1)
{
lean_object* v_val_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_908_; 
v_val_876_ = lean_ctor_get(v_a_872_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v_a_872_);
if (v_isSharedCheck_908_ == 0)
{
v___x_878_ = v_a_872_;
v_isShared_879_ = v_isSharedCheck_908_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_val_876_);
lean_dec(v_a_872_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_908_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_fst_880_; lean_object* v_snd_881_; uint8_t v___x_882_; 
v_fst_880_ = lean_ctor_get(v_val_876_, 0);
lean_inc(v_fst_880_);
v_snd_881_ = lean_ctor_get(v_val_876_, 1);
lean_inc(v_snd_881_);
lean_dec(v_val_876_);
v___x_882_ = lean_nat_dec_eq(v_fst_869_, v_fst_880_);
lean_dec(v_fst_880_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; lean_object* v___x_885_; 
lean_dec(v_snd_881_);
lean_del_object(v___x_878_);
lean_dec(v_snd_870_);
lean_dec(v_fst_869_);
lean_dec_ref(v_op_849_);
v___x_883_ = lean_box(0);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_883_);
v___x_885_ = v___x_874_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; 
lean_del_object(v___x_874_);
lean_inc(v_fst_869_);
v___x_887_ = lean_apply_3(v_op_849_, v_fst_869_, v_snd_870_, v_snd_881_);
v___x_888_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_869_, v___x_887_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_899_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_899_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_899_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_899_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v_a_889_);
v___x_894_ = v___x_878_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_898_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_896_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_894_);
v___x_896_ = v___x_891_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_del_object(v___x_878_);
v_a_900_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_888_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_888_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
}
else
{
lean_object* v___x_909_; lean_object* v___x_911_; 
lean_dec(v_a_872_);
lean_dec(v_snd_870_);
lean_dec(v_fst_869_);
lean_dec_ref(v_op_849_);
v___x_909_ = lean_box(0);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_909_);
v___x_911_ = v___x_874_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec(v_snd_870_);
lean_dec(v_fst_869_);
lean_dec_ref(v_op_849_);
v_a_914_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_871_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_871_);
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
else
{
lean_object* v___x_922_; lean_object* v___x_924_; 
lean_dec(v_a_864_);
lean_dec_ref(v_r_u2082_851_);
lean_dec_ref(v_op_849_);
v___x_922_ = lean_box(0);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_922_);
v___x_924_ = v___x_866_;
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
lean_dec_ref(v_r_u2082_851_);
lean_dec_ref(v_op_849_);
v_a_927_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_863_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_863_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0___boxed(lean_object* v_op_935_, lean_object* v_r_u2081_936_, lean_object* v_r_u2082_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0(v_op_935_, v_r_u2081_936_, v_r_u2082_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec(v___y_938_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV(lean_object* v_declName_950_, lean_object* v_arity_951_, lean_object* v_op_952_, lean_object* v_e_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
uint8_t v___x_965_; 
v___x_965_ = l_Lean_Expr_isAppOfArity(v_e_953_, v_declName_950_, v_arity_951_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; 
lean_dec_ref(v_e_953_);
lean_dec_ref(v_op_952_);
v___x_966_ = lean_box(0);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
else
{
lean_object* v___f_968_; lean_object* v___x_969_; 
v___f_968_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___lam__0___boxed), 14, 1);
lean_closure_set(v___f_968_, 0, v_op_952_);
v___x_969_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_953_, v___f_968_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
return v___x_969_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV___boxed(lean_object* v_declName_970_, lean_object* v_arity_971_, lean_object* v_op_972_, lean_object* v_e_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binBV(v_declName_970_, v_arity_971_, v_op_972_, v_e_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec(v_a_974_);
lean_dec(v_declName_970_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0(lean_object* v_op_986_, lean_object* v_r_u2081_987_, lean_object* v_r_u2082_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_987_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1056_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1056_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1056_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
if (lean_obj_tag(v_a_1001_) == 1)
{
lean_object* v_val_1005_; lean_object* v_fst_1006_; lean_object* v_snd_1007_; lean_object* v___x_1008_; 
lean_del_object(v___x_1003_);
v_val_1005_ = lean_ctor_get(v_a_1001_, 0);
lean_inc(v_val_1005_);
lean_dec_ref_known(v_a_1001_, 1);
v_fst_1006_ = lean_ctor_get(v_val_1005_, 0);
lean_inc(v_fst_1006_);
v_snd_1007_ = lean_ctor_get(v_val_1005_, 1);
lean_inc(v_snd_1007_);
lean_dec(v_val_1005_);
v___x_1008_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_988_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1043_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1043_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1043_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
if (lean_obj_tag(v_a_1009_) == 1)
{
lean_object* v_val_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1038_; 
lean_del_object(v___x_1011_);
v_val_1013_ = lean_ctor_get(v_a_1009_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_a_1009_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1015_ = v_a_1009_;
v_isShared_1016_ = v_isSharedCheck_1038_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_val_1013_);
lean_dec(v_a_1009_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1038_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_inc(v_fst_1006_);
v___x_1017_ = lean_apply_3(v_op_986_, v_fst_1006_, v_snd_1007_, v_val_1013_);
v___x_1018_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_1006_, v___x_1017_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1029_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1029_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1029_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v_a_1019_);
v___x_1024_ = v___x_1015_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1024_);
v___x_1026_ = v___x_1021_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_del_object(v___x_1015_);
v_a_1030_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1018_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1018_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
else
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
lean_dec(v_a_1009_);
lean_dec(v_snd_1007_);
lean_dec(v_fst_1006_);
lean_dec_ref(v_op_986_);
v___x_1039_ = lean_box(0);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1039_);
v___x_1041_ = v___x_1011_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec(v_snd_1007_);
lean_dec(v_fst_1006_);
lean_dec_ref(v_op_986_);
v_a_1044_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1008_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1008_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
lean_dec(v_a_1001_);
lean_dec_ref(v_op_986_);
v___x_1052_ = lean_box(0);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1052_);
v___x_1054_ = v___x_1003_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec_ref(v_op_986_);
v_a_1057_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1000_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1000_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0___boxed(lean_object* v_op_1065_, lean_object* v_r_u2081_1066_, lean_object* v_r_u2082_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0(v_op_1065_, v_r_u2081_1066_, v_r_u2082_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v_r_u2082_1067_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV(lean_object* v_declName_1080_, lean_object* v_arity_1081_, lean_object* v_op_1082_, lean_object* v_e_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
uint8_t v___x_1095_; 
v___x_1095_ = l_Lean_Expr_isAppOfArity(v_e_1083_, v_declName_1080_, v_arity_1081_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec_ref(v_e_1083_);
lean_dec_ref(v_op_1082_);
v___x_1096_ = lean_box(0);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
else
{
lean_object* v___f_1098_; lean_object* v___x_1099_; 
v___f_1098_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___lam__0___boxed), 14, 1);
lean_closure_set(v___f_1098_, 0, v_op_1082_);
v___x_1099_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_1083_, v___f_1098_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
return v___x_1099_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV___boxed(lean_object* v_declName_1100_, lean_object* v_arity_1101_, lean_object* v_op_1102_, lean_object* v_e_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_shiftBV(v_declName_1100_, v_arity_1101_, v_op_1102_, v_e_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec(v_declName_1100_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___lam__0(lean_object* v_op_1116_, lean_object* v_r_u2081_1117_, lean_object* v_r_u2082_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_1117_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1187_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1187_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1187_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
if (lean_obj_tag(v_a_1131_) == 1)
{
lean_object* v_val_1135_; lean_object* v_fst_1136_; lean_object* v_snd_1137_; lean_object* v___x_1138_; 
lean_del_object(v___x_1133_);
v_val_1135_ = lean_ctor_get(v_a_1131_, 0);
lean_inc(v_val_1135_);
lean_dec_ref_known(v_a_1131_, 1);
v_fst_1136_ = lean_ctor_get(v_val_1135_, 0);
lean_inc(v_fst_1136_);
v_snd_1137_ = lean_ctor_get(v_val_1135_, 1);
lean_inc(v_snd_1137_);
lean_dec(v_val_1135_);
v___x_1138_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_1118_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1174_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1174_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1174_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
if (lean_obj_tag(v_a_1139_) == 1)
{
lean_object* v_val_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1169_; 
lean_del_object(v___x_1141_);
v_val_1143_ = lean_ctor_get(v_a_1139_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_a_1139_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1145_ = v_a_1139_;
v_isShared_1146_ = v_isSharedCheck_1169_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_val_1143_);
lean_dec(v_a_1139_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1169_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; uint8_t v___x_1148_; lean_object* v___x_1149_; 
v___x_1147_ = lean_apply_3(v_op_1116_, v_fst_1136_, v_snd_1137_, v_val_1143_);
v___x_1148_ = lean_unbox(v___x_1147_);
v___x_1149_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v___x_1148_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1160_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1160_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1160_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v_a_1150_);
v___x_1155_ = v___x_1145_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1157_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1155_);
v___x_1157_ = v___x_1152_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_del_object(v___x_1145_);
v_a_1161_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1149_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1149_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1172_; 
lean_dec(v_a_1139_);
lean_dec(v_snd_1137_);
lean_dec(v_fst_1136_);
lean_dec_ref(v_op_1116_);
v___x_1170_ = lean_box(0);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1170_);
v___x_1172_ = v___x_1141_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec(v_snd_1137_);
lean_dec(v_fst_1136_);
lean_dec_ref(v_op_1116_);
v_a_1175_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1138_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1138_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
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
else
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
lean_dec(v_a_1131_);
lean_dec_ref(v_op_1116_);
v___x_1183_ = lean_box(0);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1183_);
v___x_1185_ = v___x_1133_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec_ref(v_op_1116_);
v_a_1188_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1130_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1130_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___lam__0___boxed(lean_object* v_op_1196_, lean_object* v_r_u2081_1197_, lean_object* v_r_u2082_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___lam__0(v_op_1196_, v_r_u2081_1197_, v_r_u2082_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v_r_u2082_1198_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV(lean_object* v_declName_1211_, lean_object* v_op_1212_, lean_object* v_e_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = lean_unsigned_to_nat(3u);
v___x_1226_ = l_Lean_Expr_isAppOfArity(v_e_1213_, v_declName_1211_, v___x_1225_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec_ref(v_e_1213_);
lean_dec_ref(v_op_1212_);
v___x_1227_ = lean_box(0);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
else
{
lean_object* v___f_1229_; lean_object* v___x_1230_; 
v___f_1229_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___lam__0___boxed), 14, 1);
lean_closure_set(v___f_1229_, 0, v_op_1212_);
v___x_1230_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_1213_, v___f_1229_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
return v___x_1230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV___boxed(lean_object* v_declName_1231_, lean_object* v_op_1232_, lean_object* v_e_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_getBitBV(v_declName_1231_, v_op_1232_, v_e_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec(v_declName_1231_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVNot___lam__0(lean_object* v_r_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1246_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1295_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1261_ = v___x_1258_;
v_isShared_1262_ = v_isSharedCheck_1295_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1258_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1295_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
if (lean_obj_tag(v_a_1259_) == 1)
{
lean_object* v_val_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1290_; 
lean_del_object(v___x_1261_);
v_val_1263_ = lean_ctor_get(v_a_1259_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_a_1259_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1265_ = v_a_1259_;
v_isShared_1266_ = v_isSharedCheck_1290_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_val_1263_);
lean_dec(v_a_1259_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1290_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v_fst_1267_; lean_object* v_snd_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v_fst_1267_ = lean_ctor_get(v_val_1263_, 0);
lean_inc(v_fst_1267_);
v_snd_1268_ = lean_ctor_get(v_val_1263_, 1);
lean_inc(v_snd_1268_);
lean_dec(v_val_1263_);
v___x_1269_ = l_BitVec_not(v_fst_1267_, v_snd_1268_);
lean_dec(v_snd_1268_);
v___x_1270_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_1267_, v___x_1269_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1281_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1281_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1281_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v_a_1271_);
v___x_1276_ = v___x_1265_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1278_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___x_1276_);
v___x_1278_ = v___x_1273_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_del_object(v___x_1265_);
v_a_1282_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1270_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1270_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1293_; 
lean_dec(v_a_1259_);
v___x_1291_ = lean_box(0);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v___x_1291_);
v___x_1293_ = v___x_1261_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
v_a_1296_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1258_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1258_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVNot___lam__0___boxed(lean_object* v_r_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_Meta_Grind_propagateBVNot___lam__0(v_r_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec(v___y_1305_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVNot(lean_object* v_e_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1335_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVNot___closed__2));
v___x_1336_ = lean_unsigned_to_nat(3u);
v___x_1337_ = l_Lean_Expr_isAppOfArity(v_e_1323_, v___x_1335_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_dec_ref(v_e_1323_);
v___x_1338_ = lean_box(0);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
return v___x_1339_;
}
else
{
lean_object* v___f_1340_; lean_object* v___x_1341_; 
v___f_1340_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVNot___closed__3));
v___x_1341_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1323_, v___f_1340_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVNot___boxed(lean_object* v_e_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_Meta_Grind_propagateBVNot(v_e_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
lean_dec(v_a_1348_);
lean_dec_ref(v_a_1347_);
lean_dec(v_a_1346_);
lean_dec_ref(v_a_1345_);
lean_dec(v_a_1344_);
lean_dec(v_a_1343_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVNot___regBuiltin_Lean_Meta_Grind_propagateBVNot_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_524020944____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVNot___closed__2));
v___x_1357_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVNot___boxed), 12, 0);
v___x_1358_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1356_, v___x_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVNot___regBuiltin_Lean_Meta_Grind_propagateBVNot_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_524020944____hygCtx___hyg_8____boxed(lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVNot___regBuiltin_Lean_Meta_Grind_propagateBVNot_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_524020944____hygCtx___hyg_8_();
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVClz___lam__0(lean_object* v_r_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1361_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1410_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1376_ = v___x_1373_;
v_isShared_1377_ = v_isSharedCheck_1410_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1410_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
if (lean_obj_tag(v_a_1374_) == 1)
{
lean_object* v_val_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1405_; 
lean_del_object(v___x_1376_);
v_val_1378_ = lean_ctor_get(v_a_1374_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_a_1374_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1380_ = v_a_1374_;
v_isShared_1381_ = v_isSharedCheck_1405_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_val_1378_);
lean_dec(v_a_1374_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1405_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v_fst_1382_; lean_object* v_snd_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_fst_1382_ = lean_ctor_get(v_val_1378_, 0);
lean_inc(v_fst_1382_);
v_snd_1383_ = lean_ctor_get(v_val_1378_, 1);
lean_inc(v_snd_1383_);
lean_dec(v_val_1378_);
v___x_1384_ = l_BitVec_clz(v_fst_1382_, v_snd_1383_);
lean_dec(v_snd_1383_);
v___x_1385_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_1382_, v___x_1384_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1396_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1396_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1396_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v_a_1386_);
v___x_1391_ = v___x_1380_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1393_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1391_);
v___x_1393_ = v___x_1388_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_del_object(v___x_1380_);
v_a_1397_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1385_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1385_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
lean_dec(v_a_1374_);
v___x_1406_ = lean_box(0);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v___x_1406_);
v___x_1408_ = v___x_1376_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
v_a_1411_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1373_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1373_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVClz___lam__0___boxed(lean_object* v_r_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_Meta_Grind_propagateBVClz___lam__0(v_r_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec(v___y_1420_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVClz(lean_object* v_e_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1449_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVClz___closed__1));
v___x_1450_ = lean_unsigned_to_nat(2u);
v___x_1451_ = l_Lean_Expr_isAppOfArity(v_e_1437_, v___x_1449_, v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_dec_ref(v_e_1437_);
v___x_1452_ = lean_box(0);
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
return v___x_1453_;
}
else
{
lean_object* v___f_1454_; lean_object* v___x_1455_; 
v___f_1454_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVClz___closed__2));
v___x_1455_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1437_, v___f_1454_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
return v___x_1455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVClz___boxed(lean_object* v_e_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Meta_Grind_propagateBVClz(v_e_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec(v_a_1458_);
lean_dec(v_a_1457_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVClz___regBuiltin_Lean_Meta_Grind_propagateBVClz_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3163129259____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1470_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVClz___closed__1));
v___x_1471_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVClz___boxed), 12, 0);
v___x_1472_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1470_, v___x_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVClz___regBuiltin_Lean_Meta_Grind_propagateBVClz_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3163129259____hygCtx___hyg_8____boxed(lean_object* v_a_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVClz___regBuiltin_Lean_Meta_Grind_propagateBVClz_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3163129259____hygCtx___hyg_8_();
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVCpop___lam__0(lean_object* v_r_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1475_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1524_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1490_ = v___x_1487_;
v_isShared_1491_ = v_isSharedCheck_1524_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1524_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
if (lean_obj_tag(v_a_1488_) == 1)
{
lean_object* v_val_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1519_; 
lean_del_object(v___x_1490_);
v_val_1492_ = lean_ctor_get(v_a_1488_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_a_1488_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1494_ = v_a_1488_;
v_isShared_1495_ = v_isSharedCheck_1519_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_val_1492_);
lean_dec(v_a_1488_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1519_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v_fst_1496_; lean_object* v_snd_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v_fst_1496_ = lean_ctor_get(v_val_1492_, 0);
lean_inc_n(v_fst_1496_, 2);
v_snd_1497_ = lean_ctor_get(v_val_1492_, 1);
lean_inc(v_snd_1497_);
lean_dec(v_val_1492_);
v___x_1498_ = l_BitVec_cpop(v_fst_1496_, v_snd_1497_);
lean_dec(v_snd_1497_);
v___x_1499_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_1496_, v___x_1498_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1510_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1510_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1510_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v_a_1500_);
v___x_1505_ = v___x_1494_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1507_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1505_);
v___x_1507_ = v___x_1502_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_del_object(v___x_1494_);
v_a_1511_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1499_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1499_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
lean_dec(v_a_1488_);
v___x_1520_ = lean_box(0);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v___x_1520_);
v___x_1522_ = v___x_1490_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
v_a_1525_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1487_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1487_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVCpop___lam__0___boxed(lean_object* v_r_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Meta_Grind_propagateBVCpop___lam__0(v_r_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec(v___y_1534_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVCpop(lean_object* v_e_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1563_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVCpop___closed__1));
v___x_1564_ = lean_unsigned_to_nat(2u);
v___x_1565_ = l_Lean_Expr_isAppOfArity(v_e_1551_, v___x_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
lean_dec_ref(v_e_1551_);
v___x_1566_ = lean_box(0);
v___x_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
return v___x_1567_;
}
else
{
lean_object* v___f_1568_; lean_object* v___x_1569_; 
v___f_1568_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVCpop___closed__2));
v___x_1569_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1551_, v___f_1568_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_);
return v___x_1569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVCpop___boxed(lean_object* v_e_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Meta_Grind_propagateBVCpop(v_e_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
lean_dec(v_a_1580_);
lean_dec_ref(v_a_1579_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
lean_dec(v_a_1576_);
lean_dec_ref(v_a_1575_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
lean_dec(v_a_1572_);
lean_dec(v_a_1571_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVCpop___regBuiltin_Lean_Meta_Grind_propagateBVCpop_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4094280043____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVCpop___closed__1));
v___x_1585_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVCpop___boxed), 12, 0);
v___x_1586_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1584_, v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVCpop___regBuiltin_Lean_Meta_Grind_propagateBVCpop_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4094280043____hygCtx___hyg_8____boxed(lean_object* v_a_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVCpop___regBuiltin_Lean_Meta_Grind_propagateBVCpop_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4094280043____hygCtx___hyg_8_();
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVMsb___lam__0(lean_object* v_r_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1589_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1638_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1638_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1638_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
uint8_t v___y_1607_; 
if (lean_obj_tag(v_a_1602_) == 1)
{
lean_object* v_val_1626_; lean_object* v_fst_1627_; lean_object* v_snd_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
lean_del_object(v___x_1604_);
v_val_1626_ = lean_ctor_get(v_a_1602_, 0);
lean_inc(v_val_1626_);
lean_dec_ref_known(v_a_1602_, 1);
v_fst_1627_ = lean_ctor_get(v_val_1626_, 0);
lean_inc(v_fst_1627_);
v_snd_1628_ = lean_ctor_get(v_val_1626_, 1);
lean_inc(v_snd_1628_);
lean_dec(v_val_1626_);
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = lean_nat_dec_lt(v___x_1629_, v_fst_1627_);
if (v___x_1630_ == 0)
{
lean_dec(v_snd_1628_);
lean_dec(v_fst_1627_);
v___y_1607_ = v___x_1630_;
goto v___jp_1606_;
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1631_ = lean_unsigned_to_nat(1u);
v___x_1632_ = lean_nat_sub(v_fst_1627_, v___x_1631_);
lean_dec(v_fst_1627_);
v___x_1633_ = l_Nat_testBit(v_snd_1628_, v___x_1632_);
lean_dec(v___x_1632_);
lean_dec(v_snd_1628_);
v___y_1607_ = v___x_1633_;
goto v___jp_1606_;
}
}
else
{
lean_object* v___x_1634_; lean_object* v___x_1636_; 
lean_dec(v_a_1602_);
v___x_1634_ = lean_box(0);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1634_);
v___x_1636_ = v___x_1604_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
v___jp_1606_:
{
lean_object* v___x_1608_; 
v___x_1608_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v___y_1607_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1617_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1617_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1617_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1613_, 0, v_a_1609_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v___x_1613_);
v___x_1615_ = v___x_1611_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
v_a_1618_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1608_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1608_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
v_a_1639_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1601_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1601_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVMsb___lam__0___boxed(lean_object* v_r_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_Meta_Grind_propagateBVMsb___lam__0(v_r_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec(v___y_1648_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVMsb(lean_object* v_e_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v___x_1677_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVMsb___closed__1));
v___x_1678_ = lean_unsigned_to_nat(2u);
v___x_1679_ = l_Lean_Expr_isAppOfArity(v_e_1665_, v___x_1677_, v___x_1678_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_dec_ref(v_e_1665_);
v___x_1680_ = lean_box(0);
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
return v___x_1681_;
}
else
{
lean_object* v___f_1682_; lean_object* v___x_1683_; 
v___f_1682_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVMsb___closed__2));
v___x_1683_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1665_, v___f_1682_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
return v___x_1683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVMsb___boxed(lean_object* v_e_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_Meta_Grind_propagateBVMsb(v_e_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
lean_dec(v_a_1692_);
lean_dec_ref(v_a_1691_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
lean_dec(v_a_1686_);
lean_dec(v_a_1685_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVMsb___regBuiltin_Lean_Meta_Grind_propagateBVMsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1379739246____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1698_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVMsb___closed__1));
v___x_1699_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVMsb___boxed), 12, 0);
v___x_1700_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1698_, v___x_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVMsb___regBuiltin_Lean_Meta_Grind_propagateBVMsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1379739246____hygCtx___hyg_8____boxed(lean_object* v_a_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVMsb___regBuiltin_Lean_Meta_Grind_propagateBVMsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1379739246____hygCtx___hyg_8_();
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToNat___lam__0(lean_object* v_r_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1703_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1751_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1718_ = v___x_1715_;
v_isShared_1719_ = v_isSharedCheck_1751_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1715_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1751_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
if (lean_obj_tag(v_a_1716_) == 1)
{
lean_object* v_val_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1746_; 
lean_del_object(v___x_1718_);
v_val_1720_ = lean_ctor_get(v_a_1716_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_a_1716_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1722_ = v_a_1716_;
v_isShared_1723_ = v_isSharedCheck_1746_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_val_1720_);
lean_dec(v_a_1716_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1746_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v_snd_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v_snd_1724_ = lean_ctor_get(v_val_1720_, 1);
lean_inc(v_snd_1724_);
lean_dec(v_val_1720_);
v___x_1725_ = l_Lean_mkNatLit(v_snd_1724_);
v___x_1726_ = l_Lean_Meta_Sym_shareCommon(v___x_1725_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1737_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1729_ = v___x_1726_;
v_isShared_1730_ = v_isSharedCheck_1737_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1726_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1737_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v_a_1727_);
v___x_1732_ = v___x_1722_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1734_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v___x_1732_);
v___x_1734_ = v___x_1729_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_del_object(v___x_1722_);
v_a_1738_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1726_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1726_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
lean_dec(v_a_1716_);
v___x_1747_ = lean_box(0);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1747_);
v___x_1749_ = v___x_1718_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
v_a_1752_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1715_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1715_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToNat___lam__0___boxed(lean_object* v_r_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Meta_Grind_propagateBVToNat___lam__0(v_r_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec(v___y_1761_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToNat(lean_object* v_e_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1790_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToNat___closed__1));
v___x_1791_ = lean_unsigned_to_nat(2u);
v___x_1792_ = l_Lean_Expr_isAppOfArity(v_e_1778_, v___x_1790_, v___x_1791_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_dec_ref(v_e_1778_);
v___x_1793_ = lean_box(0);
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
return v___x_1794_;
}
else
{
lean_object* v___f_1795_; lean_object* v___x_1796_; 
v___f_1795_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToNat___closed__2));
v___x_1796_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1778_, v___f_1795_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
return v___x_1796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToNat___boxed(lean_object* v_e_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_Meta_Grind_propagateBVToNat(v_e_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_a_1805_);
lean_dec_ref(v_a_1804_);
lean_dec(v_a_1803_);
lean_dec_ref(v_a_1802_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec(v_a_1798_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToNat___regBuiltin_Lean_Meta_Grind_propagateBVToNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1265925494____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToNat___closed__1));
v___x_1812_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVToNat___boxed), 12, 0);
v___x_1813_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1811_, v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToNat___regBuiltin_Lean_Meta_Grind_propagateBVToNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1265925494____hygCtx___hyg_8____boxed(lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToNat___regBuiltin_Lean_Meta_Grind_propagateBVToNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1265925494____hygCtx___hyg_8_();
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToInt___lam__0(lean_object* v_r_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_Meta_getBitVecValue_x3f(v_r_1816_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1866_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1866_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1866_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
if (lean_obj_tag(v_a_1829_) == 1)
{
lean_object* v_val_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1861_; 
lean_del_object(v___x_1831_);
v_val_1833_ = lean_ctor_get(v_a_1829_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_a_1829_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1835_ = v_a_1829_;
v_isShared_1836_ = v_isSharedCheck_1861_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_val_1833_);
lean_dec(v_a_1829_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1861_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v_fst_1837_; lean_object* v_snd_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v_fst_1837_ = lean_ctor_get(v_val_1833_, 0);
lean_inc(v_fst_1837_);
v_snd_1838_ = lean_ctor_get(v_val_1833_, 1);
lean_inc(v_snd_1838_);
lean_dec(v_val_1833_);
v___x_1839_ = l_BitVec_toInt(v_fst_1837_, v_snd_1838_);
lean_dec(v_fst_1837_);
v___x_1840_ = l_Lean_mkIntLit(v___x_1839_);
lean_dec(v___x_1839_);
v___x_1841_ = l_Lean_Meta_Sym_shareCommon(v___x_1840_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1852_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1852_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1852_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v_a_1842_);
v___x_1847_ = v___x_1835_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1849_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1847_);
v___x_1849_ = v___x_1844_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_del_object(v___x_1835_);
v_a_1853_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1841_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1841_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1864_; 
lean_dec(v_a_1829_);
v___x_1862_ = lean_box(0);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1862_);
v___x_1864_ = v___x_1831_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
v_a_1867_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1828_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1828_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToInt___lam__0___boxed(lean_object* v_r_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_Meta_Grind_propagateBVToInt___lam__0(v_r_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec(v___y_1876_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToInt(lean_object* v_e_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1905_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToInt___closed__1));
v___x_1906_ = lean_unsigned_to_nat(2u);
v___x_1907_ = l_Lean_Expr_isAppOfArity(v_e_1893_, v___x_1905_, v___x_1906_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
lean_dec_ref(v_e_1893_);
v___x_1908_ = lean_box(0);
v___x_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
return v___x_1909_;
}
else
{
lean_object* v___f_1910_; lean_object* v___x_1911_; 
v___f_1910_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToInt___closed__2));
v___x_1911_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_1893_, v___f_1910_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
return v___x_1911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVToInt___boxed(lean_object* v_e_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_Meta_Grind_propagateBVToInt(v_e_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec(v_a_1916_);
lean_dec_ref(v_a_1915_);
lean_dec(v_a_1914_);
lean_dec(v_a_1913_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToInt___regBuiltin_Lean_Meta_Grind_propagateBVToInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2998338308____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1926_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVToInt___closed__1));
v___x_1927_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVToInt___boxed), 12, 0);
v___x_1928_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1926_, v___x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToInt___regBuiltin_Lean_Meta_Grind_propagateBVToInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2998338308____hygCtx___hyg_8____boxed(lean_object* v_a_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToInt___regBuiltin_Lean_Meta_Grind_propagateBVToInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2998338308____hygCtx___hyg_8_();
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat___lam__0(lean_object* v_val_1931_, lean_object* v_r_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_Meta_getNatValue_x3f(v_r_1932_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1979_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1947_ = v___x_1944_;
v_isShared_1948_ = v_isSharedCheck_1979_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1979_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
if (lean_obj_tag(v_a_1945_) == 1)
{
lean_object* v_val_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1974_; 
lean_del_object(v___x_1947_);
v_val_1949_ = lean_ctor_get(v_a_1945_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_a_1945_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1951_ = v_a_1945_;
v_isShared_1952_ = v_isSharedCheck_1974_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_val_1949_);
lean_dec(v_a_1945_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1974_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = l_BitVec_ofNat(v_val_1931_, v_val_1949_);
lean_dec(v_val_1949_);
v___x_1954_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_val_1931_, v___x_1953_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1965_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1965_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1965_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v_a_1955_);
v___x_1960_ = v___x_1951_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1962_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1960_);
v___x_1962_ = v___x_1957_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_del_object(v___x_1951_);
v_a_1966_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1954_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1954_);
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
else
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
lean_dec(v_a_1945_);
lean_dec(v_val_1931_);
v___x_1975_ = lean_box(0);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1975_);
v___x_1977_ = v___x_1947_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v_val_1931_);
v_a_1980_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1944_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1944_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat___lam__0___boxed(lean_object* v_val_1988_, lean_object* v_r_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_Meta_Grind_propagateBVOfNat___lam__0(v_val_1988_, v_r_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v_r_1989_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat(lean_object* v_e_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2018_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOfNat___closed__1));
v___x_2019_ = lean_unsigned_to_nat(2u);
v___x_2020_ = l_Lean_Expr_isAppOfArity(v_e_2006_, v___x_2018_, v___x_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec_ref(v_e_2006_);
v___x_2021_ = lean_box(0);
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
return v___x_2022_;
}
else
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2023_ = l_Lean_Expr_getAppNumArgs(v_e_2006_);
v___x_2024_ = lean_unsigned_to_nat(1u);
v___x_2025_ = lean_nat_sub(v___x_2023_, v___x_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = l_Lean_Expr_getRevArg_x21(v_e_2006_, v___x_2025_);
v___x_2027_ = l_Lean_Meta_getNatValue_x3f(v___x_2026_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
lean_dec_ref(v___x_2026_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2039_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2039_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2039_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
if (lean_obj_tag(v_a_2028_) == 1)
{
lean_object* v_val_2032_; lean_object* v___f_2033_; lean_object* v___x_2034_; 
lean_del_object(v___x_2030_);
v_val_2032_ = lean_ctor_get(v_a_2028_, 0);
lean_inc(v_val_2032_);
lean_dec_ref_known(v_a_2028_, 1);
v___f_2033_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVOfNat___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2033_, 0, v_val_2032_);
v___x_2034_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2006_, v___f_2033_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
return v___x_2034_;
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2037_; 
lean_dec(v_a_2028_);
lean_dec_ref(v_e_2006_);
v___x_2035_ = lean_box(0);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2035_);
v___x_2037_ = v___x_2030_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec_ref(v_e_2006_);
v_a_2040_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2027_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2027_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfNat___boxed(lean_object* v_e_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_Meta_Grind_propagateBVOfNat(v_e_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
lean_dec(v_a_2050_);
lean_dec(v_a_2049_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1693823724____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOfNat___closed__1));
v___x_2063_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVOfNat___boxed), 12, 0);
v___x_2064_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2062_, v___x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1693823724____hygCtx___hyg_8____boxed(lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1693823724____hygCtx___hyg_8_();
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt___lam__0(lean_object* v_val_2067_, lean_object* v_r_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_Meta_getIntValue_x3f(v_r_2068_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2115_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2115_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2115_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
if (lean_obj_tag(v_a_2081_) == 1)
{
lean_object* v_val_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2110_; 
lean_del_object(v___x_2083_);
v_val_2085_ = lean_ctor_get(v_a_2081_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_a_2081_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2087_ = v_a_2081_;
v_isShared_2088_ = v_isSharedCheck_2110_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_val_2085_);
lean_dec(v_a_2081_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2110_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = l_BitVec_ofInt(v_val_2067_, v_val_2085_);
lean_dec(v_val_2085_);
v___x_2090_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_val_2067_, v___x_2089_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2101_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2093_ = v___x_2090_;
v_isShared_2094_ = v_isSharedCheck_2101_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2090_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2101_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v_a_2091_);
v___x_2096_ = v___x_2087_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2098_; 
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2096_);
v___x_2098_ = v___x_2093_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_del_object(v___x_2087_);
v_a_2102_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2090_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2090_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
else
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
lean_dec(v_a_2081_);
lean_dec(v_val_2067_);
v___x_2111_ = lean_box(0);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2111_);
v___x_2113_ = v___x_2083_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec(v_val_2067_);
v_a_2116_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2080_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2080_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt___lam__0___boxed(lean_object* v_val_2124_, lean_object* v_r_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_Meta_Grind_propagateBVOfInt___lam__0(v_val_2124_, v_r_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec(v___y_2126_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt(lean_object* v_e_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2154_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOfInt___closed__1));
v___x_2155_ = lean_unsigned_to_nat(2u);
v___x_2156_ = l_Lean_Expr_isAppOfArity(v_e_2142_, v___x_2154_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
lean_dec_ref(v_e_2142_);
v___x_2157_ = lean_box(0);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2159_ = l_Lean_Expr_getAppNumArgs(v_e_2142_);
v___x_2160_ = lean_unsigned_to_nat(1u);
v___x_2161_ = lean_nat_sub(v___x_2159_, v___x_2160_);
lean_dec(v___x_2159_);
v___x_2162_ = l_Lean_Expr_getRevArg_x21(v_e_2142_, v___x_2161_);
v___x_2163_ = l_Lean_Meta_getNatValue_x3f(v___x_2162_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
lean_dec_ref(v___x_2162_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2175_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2175_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2175_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
if (lean_obj_tag(v_a_2164_) == 1)
{
lean_object* v_val_2168_; lean_object* v___f_2169_; lean_object* v___x_2170_; 
lean_del_object(v___x_2166_);
v_val_2168_ = lean_ctor_get(v_a_2164_, 0);
lean_inc(v_val_2168_);
lean_dec_ref_known(v_a_2164_, 1);
v___f_2169_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVOfInt___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2169_, 0, v_val_2168_);
v___x_2170_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2142_, v___f_2169_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
return v___x_2170_;
}
else
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
lean_dec(v_a_2164_);
lean_dec_ref(v_e_2142_);
v___x_2171_ = lean_box(0);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2171_);
v___x_2173_ = v___x_2166_;
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
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec_ref(v_e_2142_);
v_a_2176_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2163_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2163_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOfInt___boxed(lean_object* v_e_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lean_Meta_Grind_propagateBVOfInt(v_e_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
lean_dec(v_a_2186_);
lean_dec(v_a_2185_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_16048587____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOfInt___closed__1));
v___x_2199_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVOfInt___boxed), 12, 0);
v___x_2200_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2198_, v___x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_16048587____hygCtx___hyg_8____boxed(lean_object* v_a_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_16048587____hygCtx___hyg_8_();
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___lam__0(lean_object* v_val_2203_, lean_object* v_r_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Lean_Meta_getBitVecValue_x3f(v_r_2204_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2253_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2219_ = v___x_2216_;
v_isShared_2220_ = v_isSharedCheck_2253_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2216_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2253_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
if (lean_obj_tag(v_a_2217_) == 1)
{
lean_object* v_val_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2248_; 
lean_del_object(v___x_2219_);
v_val_2221_ = lean_ctor_get(v_a_2217_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_a_2217_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2223_ = v_a_2217_;
v_isShared_2224_ = v_isSharedCheck_2248_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_val_2221_);
lean_dec(v_a_2217_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2248_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v_fst_2225_; lean_object* v_snd_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v_fst_2225_ = lean_ctor_get(v_val_2221_, 0);
lean_inc(v_fst_2225_);
v_snd_2226_ = lean_ctor_get(v_val_2221_, 1);
lean_inc(v_snd_2226_);
lean_dec(v_val_2221_);
v___x_2227_ = l_BitVec_setWidth(v_fst_2225_, v_val_2203_, v_snd_2226_);
lean_dec(v_snd_2226_);
lean_dec(v_fst_2225_);
v___x_2228_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_val_2203_, v___x_2227_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2239_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2239_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2239_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v_a_2229_);
v___x_2234_ = v___x_2223_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2236_; 
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v___x_2234_);
v___x_2236_ = v___x_2231_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_del_object(v___x_2223_);
v_a_2240_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2228_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2228_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
}
else
{
lean_object* v___x_2249_; lean_object* v___x_2251_; 
lean_dec(v_a_2217_);
lean_dec(v_val_2203_);
v___x_2249_ = lean_box(0);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 0, v___x_2249_);
v___x_2251_ = v___x_2219_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec(v_val_2203_);
v_a_2254_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2216_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2216_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___lam__0___boxed(lean_object* v_val_2262_, lean_object* v_r_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Meta_Grind_propagateBVSetWidth___lam__0(v_val_2262_, v_r_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec(v___y_2264_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth(lean_object* v_e_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; 
v___x_2292_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSetWidth___closed__1));
v___x_2293_ = lean_unsigned_to_nat(3u);
v___x_2294_ = l_Lean_Expr_isAppOfArity(v_e_2280_, v___x_2292_, v___x_2293_);
if (v___x_2294_ == 0)
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
lean_dec_ref(v_e_2280_);
v___x_2295_ = lean_box(0);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
return v___x_2296_;
}
else
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2297_ = lean_unsigned_to_nat(1u);
v___x_2298_ = l_Lean_Expr_getAppNumArgs(v_e_2280_);
v___x_2299_ = lean_nat_sub(v___x_2298_, v___x_2297_);
lean_dec(v___x_2298_);
v___x_2300_ = lean_nat_sub(v___x_2299_, v___x_2297_);
lean_dec(v___x_2299_);
v___x_2301_ = l_Lean_Expr_getRevArg_x21(v_e_2280_, v___x_2300_);
v___x_2302_ = l_Lean_Meta_getNatValue_x3f(v___x_2301_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
lean_dec_ref(v___x_2301_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2314_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2314_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2314_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
if (lean_obj_tag(v_a_2303_) == 1)
{
lean_object* v_val_2307_; lean_object* v___f_2308_; lean_object* v___x_2309_; 
lean_del_object(v___x_2305_);
v_val_2307_ = lean_ctor_get(v_a_2303_, 0);
lean_inc(v_val_2307_);
lean_dec_ref_known(v_a_2303_, 1);
v___f_2308_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVSetWidth___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2308_, 0, v_val_2307_);
v___x_2309_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2280_, v___f_2308_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
return v___x_2309_;
}
else
{
lean_object* v___x_2310_; lean_object* v___x_2312_; 
lean_dec(v_a_2303_);
lean_dec_ref(v_e_2280_);
v___x_2310_ = lean_box(0);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v___x_2310_);
v___x_2312_ = v___x_2305_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec_ref(v_e_2280_);
v_a_2315_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2302_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2302_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSetWidth___boxed(lean_object* v_e_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_Meta_Grind_propagateBVSetWidth(v_e_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
lean_dec(v_a_2327_);
lean_dec_ref(v_a_2326_);
lean_dec(v_a_2325_);
lean_dec(v_a_2324_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2337_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSetWidth___closed__1));
v___x_2338_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVSetWidth___boxed), 12, 0);
v___x_2339_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2337_, v___x_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_8____boxed(lean_object* v_a_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_8_();
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___lam__0(lean_object* v_val_2342_, lean_object* v_r_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Lean_Meta_getBitVecValue_x3f(v_r_2343_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2392_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2358_ = v___x_2355_;
v_isShared_2359_ = v_isSharedCheck_2392_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2355_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2392_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
if (lean_obj_tag(v_a_2356_) == 1)
{
lean_object* v_val_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2387_; 
lean_del_object(v___x_2358_);
v_val_2360_ = lean_ctor_get(v_a_2356_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_a_2356_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2362_ = v_a_2356_;
v_isShared_2363_ = v_isSharedCheck_2387_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_val_2360_);
lean_dec(v_a_2356_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2387_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v_fst_2364_; lean_object* v_snd_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v_fst_2364_ = lean_ctor_get(v_val_2360_, 0);
lean_inc(v_fst_2364_);
v_snd_2365_ = lean_ctor_get(v_val_2360_, 1);
lean_inc(v_snd_2365_);
lean_dec(v_val_2360_);
v___x_2366_ = l_BitVec_signExtend(v_fst_2364_, v_val_2342_, v_snd_2365_);
lean_dec(v_fst_2364_);
v___x_2367_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_val_2342_, v___x_2366_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2378_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2370_ = v___x_2367_;
v_isShared_2371_ = v_isSharedCheck_2378_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2367_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2378_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v_a_2368_);
v___x_2373_ = v___x_2362_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
lean_object* v___x_2375_; 
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 0, v___x_2373_);
v___x_2375_ = v___x_2370_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_del_object(v___x_2362_);
v_a_2379_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2367_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2367_);
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
lean_object* v___x_2388_; lean_object* v___x_2390_; 
lean_dec(v_a_2356_);
lean_dec(v_val_2342_);
v___x_2388_ = lean_box(0);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v___x_2388_);
v___x_2390_ = v___x_2358_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec(v_val_2342_);
v_a_2393_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2355_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2355_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___lam__0___boxed(lean_object* v_val_2401_, lean_object* v_r_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_Meta_Grind_propagateBVSignExtend___lam__0(v_val_2401_, v_r_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec(v___y_2403_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend(lean_object* v_e_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
v___x_2431_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSignExtend___closed__1));
v___x_2432_ = lean_unsigned_to_nat(3u);
v___x_2433_ = l_Lean_Expr_isAppOfArity(v_e_2419_, v___x_2431_, v___x_2432_);
if (v___x_2433_ == 0)
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
lean_dec_ref(v_e_2419_);
v___x_2434_ = lean_box(0);
v___x_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
return v___x_2435_;
}
else
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2436_ = lean_unsigned_to_nat(1u);
v___x_2437_ = l_Lean_Expr_getAppNumArgs(v_e_2419_);
v___x_2438_ = lean_nat_sub(v___x_2437_, v___x_2436_);
lean_dec(v___x_2437_);
v___x_2439_ = lean_nat_sub(v___x_2438_, v___x_2436_);
lean_dec(v___x_2438_);
v___x_2440_ = l_Lean_Expr_getRevArg_x21(v_e_2419_, v___x_2439_);
v___x_2441_ = l_Lean_Meta_getNatValue_x3f(v___x_2440_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
lean_dec_ref(v___x_2440_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2453_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2444_ = v___x_2441_;
v_isShared_2445_ = v_isSharedCheck_2453_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2441_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2453_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
if (lean_obj_tag(v_a_2442_) == 1)
{
lean_object* v_val_2446_; lean_object* v___f_2447_; lean_object* v___x_2448_; 
lean_del_object(v___x_2444_);
v_val_2446_ = lean_ctor_get(v_a_2442_, 0);
lean_inc(v_val_2446_);
lean_dec_ref_known(v_a_2442_, 1);
v___f_2447_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVSignExtend___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2447_, 0, v_val_2446_);
v___x_2448_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2419_, v___f_2447_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
return v___x_2448_;
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2451_; 
lean_dec(v_a_2442_);
lean_dec_ref(v_e_2419_);
v___x_2449_ = lean_box(0);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 0, v___x_2449_);
v___x_2451_ = v___x_2444_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2449_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec_ref(v_e_2419_);
v_a_2454_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2441_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2441_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSignExtend___boxed(lean_object* v_e_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Lean_Meta_Grind_propagateBVSignExtend(v_e_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
lean_dec(v_a_2468_);
lean_dec_ref(v_a_2467_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
lean_dec(v_a_2464_);
lean_dec(v_a_2463_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSignExtend___closed__1));
v___x_2477_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVSignExtend___boxed), 12, 0);
v___x_2478_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2476_, v___x_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_8____boxed(lean_object* v_a_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_8_();
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0(lean_object* v_val_2481_, lean_object* v_val_2482_, lean_object* v_r_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lean_Meta_getBitVecValue_x3f(v_r_2483_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2531_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2531_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2531_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
if (lean_obj_tag(v_a_2496_) == 1)
{
lean_object* v_val_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2526_; 
lean_del_object(v___x_2498_);
v_val_2500_ = lean_ctor_get(v_a_2496_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_a_2496_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2502_ = v_a_2496_;
v_isShared_2503_ = v_isSharedCheck_2526_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_val_2500_);
lean_dec(v_a_2496_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2526_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v_snd_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v_snd_2504_ = lean_ctor_get(v_val_2500_, 1);
lean_inc(v_snd_2504_);
lean_dec(v_val_2500_);
v___x_2505_ = l_BitVec_extractLsb_x27___redArg(v_val_2481_, v_val_2482_, v_snd_2504_);
lean_dec(v_snd_2504_);
v___x_2506_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_val_2482_, v___x_2505_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2517_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2509_ = v___x_2506_;
v_isShared_2510_ = v_isSharedCheck_2517_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2506_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2517_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v_a_2507_);
v___x_2512_ = v___x_2502_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2514_; 
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 0, v___x_2512_);
v___x_2514_ = v___x_2509_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2512_);
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
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_del_object(v___x_2502_);
v_a_2518_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2506_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2506_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
else
{
lean_object* v___x_2527_; lean_object* v___x_2529_; 
lean_dec(v_a_2496_);
lean_dec(v_val_2482_);
v___x_2527_ = lean_box(0);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 0, v___x_2527_);
v___x_2529_ = v___x_2498_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
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
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_dec(v_val_2482_);
v_a_2532_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2495_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2495_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0___boxed(lean_object* v_val_2540_, lean_object* v_val_2541_, lean_object* v_r_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0(v_val_2540_, v_val_2541_, v_r_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec(v_val_2540_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27(lean_object* v_e_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2571_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__1));
v___x_2572_ = lean_unsigned_to_nat(4u);
v___x_2573_ = l_Lean_Expr_isAppOfArity(v_e_2559_, v___x_2571_, v___x_2572_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_dec_ref(v_e_2559_);
v___x_2574_ = lean_box(0);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
return v___x_2575_;
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2576_ = lean_unsigned_to_nat(1u);
v___x_2577_ = l_Lean_Expr_getAppNumArgs(v_e_2559_);
v___x_2578_ = lean_nat_sub(v___x_2577_, v___x_2576_);
v___x_2579_ = lean_nat_sub(v___x_2578_, v___x_2576_);
lean_dec(v___x_2578_);
v___x_2580_ = l_Lean_Expr_getRevArg_x21(v_e_2559_, v___x_2579_);
v___x_2581_ = l_Lean_Meta_getNatValue_x3f(v___x_2580_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
lean_dec_ref(v___x_2580_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2616_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2584_ = v___x_2581_;
v_isShared_2585_ = v_isSharedCheck_2616_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2616_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
if (lean_obj_tag(v_a_2582_) == 1)
{
lean_object* v_val_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_del_object(v___x_2584_);
v_val_2586_ = lean_ctor_get(v_a_2582_, 0);
lean_inc(v_val_2586_);
lean_dec_ref_known(v_a_2582_, 1);
v___x_2587_ = lean_unsigned_to_nat(2u);
v___x_2588_ = lean_nat_sub(v___x_2577_, v___x_2587_);
lean_dec(v___x_2577_);
v___x_2589_ = lean_nat_sub(v___x_2588_, v___x_2576_);
lean_dec(v___x_2588_);
v___x_2590_ = l_Lean_Expr_getRevArg_x21(v_e_2559_, v___x_2589_);
v___x_2591_ = l_Lean_Meta_getNatValue_x3f(v___x_2590_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
lean_dec_ref(v___x_2590_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2603_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2603_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2603_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
if (lean_obj_tag(v_a_2592_) == 1)
{
lean_object* v_val_2596_; lean_object* v___f_2597_; lean_object* v___x_2598_; 
lean_del_object(v___x_2594_);
v_val_2596_ = lean_ctor_get(v_a_2592_, 0);
lean_inc(v_val_2596_);
lean_dec_ref_known(v_a_2592_, 1);
v___f_2597_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVExtractLsb_x27___lam__0___boxed), 14, 2);
lean_closure_set(v___f_2597_, 0, v_val_2586_);
lean_closure_set(v___f_2597_, 1, v_val_2596_);
v___x_2598_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2559_, v___f_2597_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
return v___x_2598_;
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2601_; 
lean_dec(v_a_2592_);
lean_dec(v_val_2586_);
lean_dec_ref(v_e_2559_);
v___x_2599_ = lean_box(0);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2599_);
v___x_2601_ = v___x_2594_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2599_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec(v_val_2586_);
lean_dec_ref(v_e_2559_);
v_a_2604_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2591_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2591_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
else
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
lean_dec(v_a_2582_);
lean_dec(v___x_2577_);
lean_dec_ref(v_e_2559_);
v___x_2612_ = lean_box(0);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v___x_2612_);
v___x_2614_ = v___x_2584_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec(v___x_2577_);
lean_dec_ref(v_e_2559_);
v_a_2617_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2581_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2581_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb_x27___boxed(lean_object* v_e_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_Lean_Meta_Grind_propagateBVExtractLsb_x27(v_e_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_);
lean_dec(v_a_2635_);
lean_dec_ref(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
lean_dec(v_a_2631_);
lean_dec_ref(v_a_2630_);
lean_dec(v_a_2629_);
lean_dec_ref(v_a_2628_);
lean_dec(v_a_2627_);
lean_dec(v_a_2626_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4241407876____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2639_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVExtractLsb_x27___closed__1));
v___x_2640_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVExtractLsb_x27___boxed), 12, 0);
v___x_2641_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2639_, v___x_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4241407876____hygCtx___hyg_8____boxed(lean_object* v_a_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4241407876____hygCtx___hyg_8_();
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0(lean_object* v_val_2644_, lean_object* v_val_2645_, lean_object* v___x_2646_, lean_object* v_r_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lean_Meta_getBitVecValue_x3f(v_r_2647_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2697_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2662_ = v___x_2659_;
v_isShared_2663_ = v_isSharedCheck_2697_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2697_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
if (lean_obj_tag(v_a_2660_) == 1)
{
lean_object* v_val_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2692_; 
lean_del_object(v___x_2662_);
v_val_2664_ = lean_ctor_get(v_a_2660_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_a_2660_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2666_ = v_a_2660_;
v_isShared_2667_ = v_isSharedCheck_2692_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_val_2664_);
lean_dec(v_a_2660_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2692_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v_snd_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v_snd_2668_ = lean_ctor_get(v_val_2664_, 1);
lean_inc(v_snd_2668_);
lean_dec(v_val_2664_);
v___x_2669_ = lean_nat_sub(v_val_2644_, v_val_2645_);
v___x_2670_ = lean_nat_add(v___x_2669_, v___x_2646_);
lean_dec(v___x_2669_);
v___x_2671_ = l_BitVec_extractLsb___redArg(v_val_2644_, v_val_2645_, v_snd_2668_);
lean_dec(v_snd_2668_);
v___x_2672_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v___x_2670_, v___x_2671_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2683_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2683_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2683_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v_a_2673_);
v___x_2678_ = v___x_2666_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
lean_object* v___x_2680_; 
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v___x_2678_);
v___x_2680_ = v___x_2675_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_del_object(v___x_2666_);
v_a_2684_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2672_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2672_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
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
}
else
{
lean_object* v___x_2693_; lean_object* v___x_2695_; 
lean_dec(v_a_2660_);
v___x_2693_ = lean_box(0);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v___x_2693_);
v___x_2695_ = v___x_2662_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
v_a_2698_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2659_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2659_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0___boxed(lean_object* v_val_2706_, lean_object* v_val_2707_, lean_object* v___x_2708_, lean_object* v_r_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0(v_val_2706_, v_val_2707_, v___x_2708_, v_r_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec(v___x_2708_);
lean_dec(v_val_2707_);
lean_dec(v_val_2706_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb(lean_object* v_e_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2738_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1));
v___x_2739_ = lean_unsigned_to_nat(4u);
v___x_2740_ = l_Lean_Expr_isAppOfArity(v_e_2726_, v___x_2738_, v___x_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
lean_dec_ref(v_e_2726_);
v___x_2741_ = lean_box(0);
v___x_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2741_);
return v___x_2742_;
}
else
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2743_ = lean_unsigned_to_nat(1u);
v___x_2744_ = l_Lean_Expr_getAppNumArgs(v_e_2726_);
v___x_2745_ = lean_nat_sub(v___x_2744_, v___x_2743_);
v___x_2746_ = lean_nat_sub(v___x_2745_, v___x_2743_);
lean_dec(v___x_2745_);
v___x_2747_ = l_Lean_Expr_getRevArg_x21(v_e_2726_, v___x_2746_);
v___x_2748_ = l_Lean_Meta_getNatValue_x3f(v___x_2747_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
lean_dec_ref(v___x_2747_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2783_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2751_ = v___x_2748_;
v_isShared_2752_ = v_isSharedCheck_2783_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2748_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2783_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
if (lean_obj_tag(v_a_2749_) == 1)
{
lean_object* v_val_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
lean_del_object(v___x_2751_);
v_val_2753_ = lean_ctor_get(v_a_2749_, 0);
lean_inc(v_val_2753_);
lean_dec_ref_known(v_a_2749_, 1);
v___x_2754_ = lean_unsigned_to_nat(2u);
v___x_2755_ = lean_nat_sub(v___x_2744_, v___x_2754_);
lean_dec(v___x_2744_);
v___x_2756_ = lean_nat_sub(v___x_2755_, v___x_2743_);
lean_dec(v___x_2755_);
v___x_2757_ = l_Lean_Expr_getRevArg_x21(v_e_2726_, v___x_2756_);
v___x_2758_ = l_Lean_Meta_getNatValue_x3f(v___x_2757_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
lean_dec_ref(v___x_2757_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2770_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2761_ = v___x_2758_;
v_isShared_2762_ = v_isSharedCheck_2770_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2758_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2770_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
if (lean_obj_tag(v_a_2759_) == 1)
{
lean_object* v_val_2763_; lean_object* v___f_2764_; lean_object* v___x_2765_; 
lean_del_object(v___x_2761_);
v_val_2763_ = lean_ctor_get(v_a_2759_, 0);
lean_inc(v_val_2763_);
lean_dec_ref_known(v_a_2759_, 1);
v___f_2764_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVExtractLsb___lam__0___boxed), 15, 3);
lean_closure_set(v___f_2764_, 0, v_val_2753_);
lean_closure_set(v___f_2764_, 1, v_val_2763_);
lean_closure_set(v___f_2764_, 2, v___x_2743_);
v___x_2765_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2726_, v___f_2764_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
return v___x_2765_;
}
else
{
lean_object* v___x_2766_; lean_object* v___x_2768_; 
lean_dec(v_a_2759_);
lean_dec(v_val_2753_);
lean_dec_ref(v_e_2726_);
v___x_2766_ = lean_box(0);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v___x_2766_);
v___x_2768_ = v___x_2761_;
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
lean_dec(v_val_2753_);
lean_dec_ref(v_e_2726_);
v_a_2771_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2758_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2758_);
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
else
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
lean_dec(v_a_2749_);
lean_dec(v___x_2744_);
lean_dec_ref(v_e_2726_);
v___x_2779_ = lean_box(0);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 0, v___x_2779_);
v___x_2781_ = v___x_2751_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec(v___x_2744_);
lean_dec_ref(v_e_2726_);
v_a_2784_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2748_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2748_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVExtractLsb___boxed(lean_object* v_e_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_Meta_Grind_propagateBVExtractLsb(v_e_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2796_);
lean_dec_ref(v_a_2795_);
lean_dec(v_a_2794_);
lean_dec(v_a_2793_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3429100332____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2806_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVExtractLsb___closed__1));
v___x_2807_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVExtractLsb___boxed), 12, 0);
v___x_2808_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2806_, v___x_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3429100332____hygCtx___hyg_8____boxed(lean_object* v_a_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3429100332____hygCtx___hyg_8_();
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate___lam__0(lean_object* v_val_2811_, lean_object* v_r_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Lean_Meta_getBitVecValue_x3f(v_r_2812_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2862_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2827_ = v___x_2824_;
v_isShared_2828_ = v_isSharedCheck_2862_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2824_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2862_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
if (lean_obj_tag(v_a_2825_) == 1)
{
lean_object* v_val_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2857_; 
lean_del_object(v___x_2827_);
v_val_2829_ = lean_ctor_get(v_a_2825_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_a_2825_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2831_ = v_a_2825_;
v_isShared_2832_ = v_isSharedCheck_2857_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_val_2829_);
lean_dec(v_a_2825_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2857_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v_fst_2833_; lean_object* v_snd_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v_fst_2833_ = lean_ctor_get(v_val_2829_, 0);
lean_inc(v_fst_2833_);
v_snd_2834_ = lean_ctor_get(v_val_2829_, 1);
lean_inc(v_snd_2834_);
lean_dec(v_val_2829_);
v___x_2835_ = lean_nat_mul(v_fst_2833_, v_val_2811_);
v___x_2836_ = l_BitVec_replicate(v_fst_2833_, v_val_2811_, v_snd_2834_);
lean_dec(v_snd_2834_);
lean_dec(v_fst_2833_);
v___x_2837_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v___x_2835_, v___x_2836_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2848_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2840_ = v___x_2837_;
v_isShared_2841_ = v_isSharedCheck_2848_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2837_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2848_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 0, v_a_2838_);
v___x_2843_ = v___x_2831_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
lean_object* v___x_2845_; 
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2843_);
v___x_2845_ = v___x_2840_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_del_object(v___x_2831_);
v_a_2849_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2837_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2837_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
}
else
{
lean_object* v___x_2858_; lean_object* v___x_2860_; 
lean_dec(v_a_2825_);
v___x_2858_ = lean_box(0);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 0, v___x_2858_);
v___x_2860_ = v___x_2827_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2858_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
v_a_2863_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2824_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2824_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate___lam__0___boxed(lean_object* v_val_2871_, lean_object* v_r_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_Meta_Grind_propagateBVReplicate___lam__0(v_val_2871_, v_r_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v_val_2871_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate(lean_object* v_e_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; uint8_t v___x_2903_; 
v___x_2901_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVReplicate___closed__1));
v___x_2902_ = lean_unsigned_to_nat(3u);
v___x_2903_ = l_Lean_Expr_isAppOfArity(v_e_2889_, v___x_2901_, v___x_2902_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
lean_dec_ref(v_e_2889_);
v___x_2904_ = lean_box(0);
v___x_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2904_);
return v___x_2905_;
}
else
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2906_ = lean_unsigned_to_nat(1u);
v___x_2907_ = l_Lean_Expr_getAppNumArgs(v_e_2889_);
v___x_2908_ = lean_nat_sub(v___x_2907_, v___x_2906_);
lean_dec(v___x_2907_);
v___x_2909_ = lean_nat_sub(v___x_2908_, v___x_2906_);
lean_dec(v___x_2908_);
v___x_2910_ = l_Lean_Expr_getRevArg_x21(v_e_2889_, v___x_2909_);
v___x_2911_ = l_Lean_Meta_getNatValue_x3f(v___x_2910_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
lean_dec_ref(v___x_2910_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2923_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2914_ = v___x_2911_;
v_isShared_2915_ = v_isSharedCheck_2923_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2911_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2923_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
if (lean_obj_tag(v_a_2912_) == 1)
{
lean_object* v_val_2916_; lean_object* v___f_2917_; lean_object* v___x_2918_; 
lean_del_object(v___x_2914_);
v_val_2916_ = lean_ctor_get(v_a_2912_, 0);
lean_inc(v_val_2916_);
lean_dec_ref_known(v_a_2912_, 1);
v___f_2917_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVReplicate___lam__0___boxed), 13, 1);
lean_closure_set(v___f_2917_, 0, v_val_2916_);
v___x_2918_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp(v_e_2889_, v___f_2917_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
return v___x_2918_;
}
else
{
lean_object* v___x_2919_; lean_object* v___x_2921_; 
lean_dec(v_a_2912_);
lean_dec_ref(v_e_2889_);
v___x_2919_ = lean_box(0);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2919_);
v___x_2921_ = v___x_2914_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2919_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
else
{
lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
lean_dec_ref(v_e_2889_);
v_a_2924_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2911_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2911_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVReplicate___boxed(lean_object* v_e_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Lean_Meta_Grind_propagateBVReplicate(v_e_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
lean_dec(v_a_2938_);
lean_dec_ref(v_a_2937_);
lean_dec(v_a_2936_);
lean_dec_ref(v_a_2935_);
lean_dec(v_a_2934_);
lean_dec(v_a_2933_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3327375609____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2946_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVReplicate___closed__1));
v___x_2947_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVReplicate___boxed), 12, 0);
v___x_2948_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2946_, v___x_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3327375609____hygCtx___hyg_8____boxed(lean_object* v_a_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3327375609____hygCtx___hyg_8_();
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAnd___lam__0(lean_object* v_r_u2081_2951_, lean_object* v_r_u2082_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v___x_2964_; 
v___x_2964_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_2951_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_3027_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_2967_ = v___x_2964_;
v_isShared_2968_ = v_isSharedCheck_3027_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2964_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_3027_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
if (lean_obj_tag(v_a_2965_) == 1)
{
lean_object* v_val_2969_; lean_object* v_fst_2970_; lean_object* v_snd_2971_; lean_object* v___x_2972_; 
lean_del_object(v___x_2967_);
v_val_2969_ = lean_ctor_get(v_a_2965_, 0);
lean_inc(v_val_2969_);
lean_dec_ref_known(v_a_2965_, 1);
v_fst_2970_ = lean_ctor_get(v_val_2969_, 0);
lean_inc(v_fst_2970_);
v_snd_2971_ = lean_ctor_get(v_val_2969_, 1);
lean_inc(v_snd_2971_);
lean_dec(v_val_2969_);
v___x_2972_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_2952_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_3014_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_2975_ = v___x_2972_;
v_isShared_2976_ = v_isSharedCheck_3014_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2972_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_3014_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
if (lean_obj_tag(v_a_2973_) == 1)
{
lean_object* v_val_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_3009_; 
v_val_2977_ = lean_ctor_get(v_a_2973_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v_a_2973_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_2979_ = v_a_2973_;
v_isShared_2980_ = v_isSharedCheck_3009_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_val_2977_);
lean_dec(v_a_2973_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_3009_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v_fst_2981_; lean_object* v_snd_2982_; uint8_t v___x_2983_; 
v_fst_2981_ = lean_ctor_get(v_val_2977_, 0);
lean_inc(v_fst_2981_);
v_snd_2982_ = lean_ctor_get(v_val_2977_, 1);
lean_inc(v_snd_2982_);
lean_dec(v_val_2977_);
v___x_2983_ = lean_nat_dec_eq(v_fst_2970_, v_fst_2981_);
lean_dec(v_fst_2981_);
if (v___x_2983_ == 0)
{
lean_object* v___x_2984_; lean_object* v___x_2986_; 
lean_dec(v_snd_2982_);
lean_del_object(v___x_2979_);
lean_dec(v_snd_2971_);
lean_dec(v_fst_2970_);
v___x_2984_ = lean_box(0);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v___x_2984_);
v___x_2986_ = v___x_2975_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2984_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
else
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_del_object(v___x_2975_);
v___x_2988_ = lean_nat_land(v_snd_2971_, v_snd_2982_);
lean_dec(v_snd_2982_);
lean_dec(v_snd_2971_);
v___x_2989_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_2970_, v___x_2988_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3000_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2992_ = v___x_2989_;
v_isShared_2993_ = v_isSharedCheck_3000_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2989_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3000_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 0, v_a_2990_);
v___x_2995_ = v___x_2979_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2997_; 
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v___x_2995_);
v___x_2997_ = v___x_2992_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
lean_del_object(v___x_2979_);
v_a_3001_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_2989_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_2989_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
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
}
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3012_; 
lean_dec(v_a_2973_);
lean_dec(v_snd_2971_);
lean_dec(v_fst_2970_);
v___x_3010_ = lean_box(0);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v___x_3010_);
v___x_3012_ = v___x_2975_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3010_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec(v_snd_2971_);
lean_dec(v_fst_2970_);
v_a_3015_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_2972_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_2972_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
lean_dec(v_a_2965_);
lean_dec_ref(v_r_u2082_2952_);
v___x_3023_ = lean_box(0);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 0, v___x_3023_);
v___x_3025_ = v___x_2967_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec_ref(v_r_u2082_2952_);
v_a_3028_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_2964_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_2964_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAnd___lam__0___boxed(lean_object* v_r_u2081_3036_, lean_object* v_r_u2082_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_Meta_Grind_propagateBVAnd___lam__0(v_r_u2081_3036_, v_r_u2082_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec(v___y_3038_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAnd(lean_object* v_e_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; uint8_t v___x_3070_; 
v___x_3068_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAnd___closed__2));
v___x_3069_ = lean_unsigned_to_nat(6u);
v___x_3070_ = l_Lean_Expr_isAppOfArity(v_e_3056_, v___x_3068_, v___x_3069_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
lean_dec_ref(v_e_3056_);
v___x_3071_ = lean_box(0);
v___x_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
return v___x_3072_;
}
else
{
lean_object* v___f_3073_; lean_object* v___x_3074_; 
v___f_3073_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAnd___closed__3));
v___x_3074_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3056_, v___f_3073_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
return v___x_3074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAnd___boxed(lean_object* v_e_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l_Lean_Meta_Grind_propagateBVAnd(v_e_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_);
lean_dec(v_a_3085_);
lean_dec_ref(v_a_3084_);
lean_dec(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
lean_dec(v_a_3077_);
lean_dec(v_a_3076_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAnd___regBuiltin_Lean_Meta_Grind_propagateBVAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_317501673____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3089_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAnd___closed__2));
v___x_3090_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVAnd___boxed), 12, 0);
v___x_3091_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3089_, v___x_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAnd___regBuiltin_Lean_Meta_Grind_propagateBVAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_317501673____hygCtx___hyg_8____boxed(lean_object* v_a_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAnd___regBuiltin_Lean_Meta_Grind_propagateBVAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_317501673____hygCtx___hyg_8_();
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOr___lam__0(lean_object* v_r_u2081_3094_, lean_object* v_r_u2082_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v___x_3107_; 
v___x_3107_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3094_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3170_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3110_ = v___x_3107_;
v_isShared_3111_ = v_isSharedCheck_3170_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3170_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
if (lean_obj_tag(v_a_3108_) == 1)
{
lean_object* v_val_3112_; lean_object* v_fst_3113_; lean_object* v_snd_3114_; lean_object* v___x_3115_; 
lean_del_object(v___x_3110_);
v_val_3112_ = lean_ctor_get(v_a_3108_, 0);
lean_inc(v_val_3112_);
lean_dec_ref_known(v_a_3108_, 1);
v_fst_3113_ = lean_ctor_get(v_val_3112_, 0);
lean_inc(v_fst_3113_);
v_snd_3114_ = lean_ctor_get(v_val_3112_, 1);
lean_inc(v_snd_3114_);
lean_dec(v_val_3112_);
v___x_3115_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_3095_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3157_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3118_ = v___x_3115_;
v_isShared_3119_ = v_isSharedCheck_3157_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3115_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3157_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
if (lean_obj_tag(v_a_3116_) == 1)
{
lean_object* v_val_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3152_; 
v_val_3120_ = lean_ctor_get(v_a_3116_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_a_3116_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3122_ = v_a_3116_;
v_isShared_3123_ = v_isSharedCheck_3152_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_val_3120_);
lean_dec(v_a_3116_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3152_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v_fst_3124_; lean_object* v_snd_3125_; uint8_t v___x_3126_; 
v_fst_3124_ = lean_ctor_get(v_val_3120_, 0);
lean_inc(v_fst_3124_);
v_snd_3125_ = lean_ctor_get(v_val_3120_, 1);
lean_inc(v_snd_3125_);
lean_dec(v_val_3120_);
v___x_3126_ = lean_nat_dec_eq(v_fst_3113_, v_fst_3124_);
lean_dec(v_fst_3124_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; lean_object* v___x_3129_; 
lean_dec(v_snd_3125_);
lean_del_object(v___x_3122_);
lean_dec(v_snd_3114_);
lean_dec(v_fst_3113_);
v___x_3127_ = lean_box(0);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v___x_3127_);
v___x_3129_ = v___x_3118_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3127_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
else
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
lean_del_object(v___x_3118_);
v___x_3131_ = lean_nat_lor(v_snd_3114_, v_snd_3125_);
lean_dec(v_snd_3125_);
lean_dec(v_snd_3114_);
v___x_3132_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3113_, v___x_3131_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3143_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3135_ = v___x_3132_;
v_isShared_3136_ = v_isSharedCheck_3143_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3132_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3143_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v_a_3133_);
v___x_3138_ = v___x_3122_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
lean_object* v___x_3140_; 
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 0, v___x_3138_);
v___x_3140_ = v___x_3135_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3138_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_del_object(v___x_3122_);
v_a_3144_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3132_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3132_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
}
}
else
{
lean_object* v___x_3153_; lean_object* v___x_3155_; 
lean_dec(v_a_3116_);
lean_dec(v_snd_3114_);
lean_dec(v_fst_3113_);
v___x_3153_ = lean_box(0);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v___x_3153_);
v___x_3155_ = v___x_3118_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3153_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec(v_snd_3114_);
lean_dec(v_fst_3113_);
v_a_3158_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3115_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3115_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
else
{
lean_object* v___x_3166_; lean_object* v___x_3168_; 
lean_dec(v_a_3108_);
lean_dec_ref(v_r_u2082_3095_);
v___x_3166_ = lean_box(0);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v___x_3166_);
v___x_3168_ = v___x_3110_;
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
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec_ref(v_r_u2082_3095_);
v_a_3171_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3107_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3107_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOr___lam__0___boxed(lean_object* v_r_u2081_3179_, lean_object* v_r_u2082_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_Lean_Meta_Grind_propagateBVOr___lam__0(v_r_u2081_3179_, v_r_u2082_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec(v___y_3181_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOr(lean_object* v_e_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; 
v___x_3211_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOr___closed__2));
v___x_3212_ = lean_unsigned_to_nat(6u);
v___x_3213_ = l_Lean_Expr_isAppOfArity(v_e_3199_, v___x_3211_, v___x_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
lean_dec_ref(v_e_3199_);
v___x_3214_ = lean_box(0);
v___x_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
return v___x_3215_;
}
else
{
lean_object* v___f_3216_; lean_object* v___x_3217_; 
v___f_3216_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOr___closed__3));
v___x_3217_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3199_, v___f_3216_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_);
return v___x_3217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVOr___boxed(lean_object* v_e_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l_Lean_Meta_Grind_propagateBVOr(v_e_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
lean_dec(v_a_3228_);
lean_dec_ref(v_a_3227_);
lean_dec(v_a_3226_);
lean_dec_ref(v_a_3225_);
lean_dec(v_a_3224_);
lean_dec_ref(v_a_3223_);
lean_dec(v_a_3222_);
lean_dec_ref(v_a_3221_);
lean_dec(v_a_3220_);
lean_dec(v_a_3219_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOr___regBuiltin_Lean_Meta_Grind_propagateBVOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4272827602____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVOr___closed__2));
v___x_3233_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVOr___boxed), 12, 0);
v___x_3234_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3232_, v___x_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOr___regBuiltin_Lean_Meta_Grind_propagateBVOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4272827602____hygCtx___hyg_8____boxed(lean_object* v_a_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOr___regBuiltin_Lean_Meta_Grind_propagateBVOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4272827602____hygCtx___hyg_8_();
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVXor___lam__0(lean_object* v_r_u2081_3237_, lean_object* v_r_u2082_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3237_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3313_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3253_ = v___x_3250_;
v_isShared_3254_ = v_isSharedCheck_3313_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3250_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3313_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
if (lean_obj_tag(v_a_3251_) == 1)
{
lean_object* v_val_3255_; lean_object* v_fst_3256_; lean_object* v_snd_3257_; lean_object* v___x_3258_; 
lean_del_object(v___x_3253_);
v_val_3255_ = lean_ctor_get(v_a_3251_, 0);
lean_inc(v_val_3255_);
lean_dec_ref_known(v_a_3251_, 1);
v_fst_3256_ = lean_ctor_get(v_val_3255_, 0);
lean_inc(v_fst_3256_);
v_snd_3257_ = lean_ctor_get(v_val_3255_, 1);
lean_inc(v_snd_3257_);
lean_dec(v_val_3255_);
v___x_3258_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_3238_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3300_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3261_ = v___x_3258_;
v_isShared_3262_ = v_isSharedCheck_3300_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3258_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3300_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
if (lean_obj_tag(v_a_3259_) == 1)
{
lean_object* v_val_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3295_; 
v_val_3263_ = lean_ctor_get(v_a_3259_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v_a_3259_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3265_ = v_a_3259_;
v_isShared_3266_ = v_isSharedCheck_3295_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_val_3263_);
lean_dec(v_a_3259_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3295_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v_fst_3267_; lean_object* v_snd_3268_; uint8_t v___x_3269_; 
v_fst_3267_ = lean_ctor_get(v_val_3263_, 0);
lean_inc(v_fst_3267_);
v_snd_3268_ = lean_ctor_get(v_val_3263_, 1);
lean_inc(v_snd_3268_);
lean_dec(v_val_3263_);
v___x_3269_ = lean_nat_dec_eq(v_fst_3256_, v_fst_3267_);
lean_dec(v_fst_3267_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; lean_object* v___x_3272_; 
lean_dec(v_snd_3268_);
lean_del_object(v___x_3265_);
lean_dec(v_snd_3257_);
lean_dec(v_fst_3256_);
v___x_3270_ = lean_box(0);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 0, v___x_3270_);
v___x_3272_ = v___x_3261_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3270_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
lean_del_object(v___x_3261_);
v___x_3274_ = lean_nat_lxor(v_snd_3257_, v_snd_3268_);
lean_dec(v_snd_3268_);
lean_dec(v_snd_3257_);
v___x_3275_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3256_, v___x_3274_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3286_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3278_ = v___x_3275_;
v_isShared_3279_ = v_isSharedCheck_3286_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3275_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3286_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 0, v_a_3276_);
v___x_3281_ = v___x_3265_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
lean_object* v___x_3283_; 
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 0, v___x_3281_);
v___x_3283_ = v___x_3278_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
else
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3294_; 
lean_del_object(v___x_3265_);
v_a_3287_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3289_ = v___x_3275_;
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3275_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3292_; 
if (v_isShared_3290_ == 0)
{
v___x_3292_ = v___x_3289_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
}
}
else
{
lean_object* v___x_3296_; lean_object* v___x_3298_; 
lean_dec(v_a_3259_);
lean_dec(v_snd_3257_);
lean_dec(v_fst_3256_);
v___x_3296_ = lean_box(0);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 0, v___x_3296_);
v___x_3298_ = v___x_3261_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec(v_snd_3257_);
lean_dec(v_fst_3256_);
v_a_3301_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3258_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3258_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
else
{
lean_object* v___x_3309_; lean_object* v___x_3311_; 
lean_dec(v_a_3251_);
lean_dec_ref(v_r_u2082_3238_);
v___x_3309_ = lean_box(0);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v___x_3309_);
v___x_3311_ = v___x_3253_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
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
else
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
lean_dec_ref(v_r_u2082_3238_);
v_a_3314_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3250_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3250_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVXor___lam__0___boxed(lean_object* v_r_u2081_3322_, lean_object* v_r_u2082_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lean_Meta_Grind_propagateBVXor___lam__0(v_r_u2081_3322_, v_r_u2082_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec(v___y_3324_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVXor(lean_object* v_e_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_){
_start:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; uint8_t v___x_3356_; 
v___x_3354_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVXor___closed__2));
v___x_3355_ = lean_unsigned_to_nat(6u);
v___x_3356_ = l_Lean_Expr_isAppOfArity(v_e_3342_, v___x_3354_, v___x_3355_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
lean_dec_ref(v_e_3342_);
v___x_3357_ = lean_box(0);
v___x_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
return v___x_3358_;
}
else
{
lean_object* v___f_3359_; lean_object* v___x_3360_; 
v___f_3359_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVXor___closed__3));
v___x_3360_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3342_, v___f_3359_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
return v___x_3360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVXor___boxed(lean_object* v_e_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_Lean_Meta_Grind_propagateBVXor(v_e_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_);
lean_dec(v_a_3371_);
lean_dec_ref(v_a_3370_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
lean_dec(v_a_3365_);
lean_dec_ref(v_a_3364_);
lean_dec(v_a_3363_);
lean_dec(v_a_3362_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVXor___regBuiltin_Lean_Meta_Grind_propagateBVXor_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1120302969____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3375_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVXor___closed__2));
v___x_3376_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVXor___boxed), 12, 0);
v___x_3377_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3375_, v___x_3376_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVXor___regBuiltin_Lean_Meta_Grind_propagateBVXor_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1120302969____hygCtx___hyg_8____boxed(lean_object* v_a_3378_){
_start:
{
lean_object* v_res_3379_; 
v_res_3379_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVXor___regBuiltin_Lean_Meta_Grind_propagateBVXor_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1120302969____hygCtx___hyg_8_();
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAppend___lam__0(lean_object* v_r_u2081_3380_, lean_object* v_r_u2082_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v___x_3393_; 
v___x_3393_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3380_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3452_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3396_ = v___x_3393_;
v_isShared_3397_ = v_isSharedCheck_3452_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3393_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3452_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
if (lean_obj_tag(v_a_3394_) == 1)
{
lean_object* v_val_3398_; lean_object* v_fst_3399_; lean_object* v_snd_3400_; lean_object* v___x_3401_; 
lean_del_object(v___x_3396_);
v_val_3398_ = lean_ctor_get(v_a_3394_, 0);
lean_inc(v_val_3398_);
lean_dec_ref_known(v_a_3394_, 1);
v_fst_3399_ = lean_ctor_get(v_val_3398_, 0);
lean_inc(v_fst_3399_);
v_snd_3400_ = lean_ctor_get(v_val_3398_, 1);
lean_inc(v_snd_3400_);
lean_dec(v_val_3398_);
v___x_3401_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_3381_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3439_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3404_ = v___x_3401_;
v_isShared_3405_ = v_isSharedCheck_3439_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3401_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3439_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
if (lean_obj_tag(v_a_3402_) == 1)
{
lean_object* v_val_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3434_; 
lean_del_object(v___x_3404_);
v_val_3406_ = lean_ctor_get(v_a_3402_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v_a_3402_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3408_ = v_a_3402_;
v_isShared_3409_ = v_isSharedCheck_3434_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_val_3406_);
lean_dec(v_a_3402_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3434_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v_fst_3410_; lean_object* v_snd_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v_fst_3410_ = lean_ctor_get(v_val_3406_, 0);
lean_inc(v_fst_3410_);
v_snd_3411_ = lean_ctor_get(v_val_3406_, 1);
lean_inc(v_snd_3411_);
lean_dec(v_val_3406_);
v___x_3412_ = lean_nat_add(v_fst_3399_, v_fst_3410_);
lean_dec(v_fst_3399_);
v___x_3413_ = l_BitVec_append___redArg(v_fst_3410_, v_snd_3400_, v_snd_3411_);
lean_dec(v_snd_3411_);
lean_dec(v_snd_3400_);
lean_dec(v_fst_3410_);
v___x_3414_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v___x_3412_, v___x_3413_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3425_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3417_ = v___x_3414_;
v_isShared_3418_ = v_isSharedCheck_3425_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3414_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3425_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v_a_3415_);
v___x_3420_ = v___x_3408_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3422_; 
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 0, v___x_3420_);
v___x_3422_ = v___x_3417_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_del_object(v___x_3408_);
v_a_3426_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3414_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3414_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
}
else
{
lean_object* v___x_3435_; lean_object* v___x_3437_; 
lean_dec(v_a_3402_);
lean_dec(v_snd_3400_);
lean_dec(v_fst_3399_);
v___x_3435_ = lean_box(0);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 0, v___x_3435_);
v___x_3437_ = v___x_3404_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec(v_snd_3400_);
lean_dec(v_fst_3399_);
v_a_3440_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3401_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3401_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
else
{
lean_object* v___x_3448_; lean_object* v___x_3450_; 
lean_dec(v_a_3394_);
lean_dec_ref(v_r_u2082_3381_);
v___x_3448_ = lean_box(0);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v___x_3448_);
v___x_3450_ = v___x_3396_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_dec_ref(v_r_u2082_3381_);
v_a_3453_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3393_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3393_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAppend___lam__0___boxed(lean_object* v_r_u2081_3461_, lean_object* v_r_u2082_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_Lean_Meta_Grind_propagateBVAppend___lam__0(v_r_u2081_3461_, v_r_u2082_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec(v___y_3463_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAppend(lean_object* v_e_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_){
_start:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; uint8_t v___x_3495_; 
v___x_3493_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAppend___closed__2));
v___x_3494_ = lean_unsigned_to_nat(6u);
v___x_3495_ = l_Lean_Expr_isAppOfArity(v_e_3481_, v___x_3493_, v___x_3494_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
lean_dec_ref(v_e_3481_);
v___x_3496_ = lean_box(0);
v___x_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
return v___x_3497_;
}
else
{
lean_object* v___x_3498_; 
lean_inc(v_a_3491_);
lean_inc_ref(v_a_3490_);
lean_inc(v_a_3489_);
lean_inc_ref(v_a_3488_);
lean_inc_ref(v_e_3481_);
v___x_3498_ = lean_infer_type(v_e_3481_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3511_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3501_ = v___x_3498_;
v_isShared_3502_ = v_isSharedCheck_3511_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3498_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3511_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3503_; uint8_t v___x_3504_; 
v___x_3503_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg___closed__1));
v___x_3504_ = l_Lean_Expr_isAppOf(v_a_3499_, v___x_3503_);
lean_dec(v_a_3499_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; lean_object* v___x_3507_; 
lean_dec_ref(v_e_3481_);
v___x_3505_ = lean_box(0);
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 0, v___x_3505_);
v___x_3507_ = v___x_3501_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
else
{
lean_object* v___f_3509_; lean_object* v___x_3510_; 
lean_del_object(v___x_3501_);
v___f_3509_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAppend___closed__3));
v___x_3510_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3481_, v___f_3509_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
return v___x_3510_;
}
}
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_dec_ref(v_e_3481_);
v_a_3512_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3498_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3498_);
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
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVAppend___boxed(lean_object* v_e_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l_Lean_Meta_Grind_propagateBVAppend(v_e_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_);
lean_dec(v_a_3530_);
lean_dec_ref(v_a_3529_);
lean_dec(v_a_3528_);
lean_dec_ref(v_a_3527_);
lean_dec(v_a_3526_);
lean_dec_ref(v_a_3525_);
lean_dec(v_a_3524_);
lean_dec_ref(v_a_3523_);
lean_dec(v_a_3522_);
lean_dec(v_a_3521_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4057925374____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3534_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVAppend___closed__2));
v___x_3535_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVAppend___boxed), 12, 0);
v___x_3536_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3534_, v___x_3535_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4057925374____hygCtx___hyg_8____boxed(lean_object* v_a_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4057925374____hygCtx___hyg_8_();
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___lam__0(lean_object* v_r_u2081_3539_, lean_object* v_r_u2082_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3539_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3608_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3555_ = v___x_3552_;
v_isShared_3556_ = v_isSharedCheck_3608_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3552_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3608_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
if (lean_obj_tag(v_a_3553_) == 1)
{
lean_object* v_val_3557_; lean_object* v_fst_3558_; lean_object* v_snd_3559_; lean_object* v___x_3560_; 
lean_del_object(v___x_3555_);
v_val_3557_ = lean_ctor_get(v_a_3553_, 0);
lean_inc(v_val_3557_);
lean_dec_ref_known(v_a_3553_, 1);
v_fst_3558_ = lean_ctor_get(v_val_3557_, 0);
lean_inc(v_fst_3558_);
v_snd_3559_ = lean_ctor_get(v_val_3557_, 1);
lean_inc(v_snd_3559_);
lean_dec(v_val_3557_);
v___x_3560_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_3540_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3595_; 
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3563_ = v___x_3560_;
v_isShared_3564_ = v_isSharedCheck_3595_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3560_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3595_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
if (lean_obj_tag(v_a_3561_) == 1)
{
lean_object* v_val_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3590_; 
lean_del_object(v___x_3563_);
v_val_3565_ = lean_ctor_get(v_a_3561_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v_a_3561_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3567_ = v_a_3561_;
v_isShared_3568_ = v_isSharedCheck_3590_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_val_3565_);
lean_dec(v_a_3561_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3590_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3569_ = l_BitVec_shiftLeft(v_fst_3558_, v_snd_3559_, v_val_3565_);
lean_dec(v_val_3565_);
lean_dec(v_snd_3559_);
v___x_3570_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3558_, v___x_3569_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3581_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3573_ = v___x_3570_;
v_isShared_3574_ = v_isSharedCheck_3581_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3570_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3581_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 0, v_a_3571_);
v___x_3576_ = v___x_3567_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
lean_object* v___x_3578_; 
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3576_);
v___x_3578_ = v___x_3573_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3576_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
else
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_del_object(v___x_3567_);
v_a_3582_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3570_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3570_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
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
else
{
lean_object* v___x_3591_; lean_object* v___x_3593_; 
lean_dec(v_a_3561_);
lean_dec(v_snd_3559_);
lean_dec(v_fst_3558_);
v___x_3591_ = lean_box(0);
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 0, v___x_3591_);
v___x_3593_ = v___x_3563_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3591_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
else
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
lean_dec(v_snd_3559_);
lean_dec(v_fst_3558_);
v_a_3596_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3560_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3560_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
else
{
lean_object* v___x_3604_; lean_object* v___x_3606_; 
lean_dec(v_a_3553_);
v___x_3604_ = lean_box(0);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 0, v___x_3604_);
v___x_3606_ = v___x_3555_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
v_a_3609_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3552_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3552_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___lam__0___boxed(lean_object* v_r_u2081_3617_, lean_object* v_r_u2082_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l_Lean_Meta_Grind_propagateBVShiftLeft___lam__0(v_r_u2081_3617_, v_r_u2082_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec_ref(v_r_u2082_3618_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft(lean_object* v_e_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; 
v___x_3648_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVShiftLeft___closed__1));
v___x_3649_ = lean_unsigned_to_nat(3u);
v___x_3650_ = l_Lean_Expr_isAppOfArity(v_e_3636_, v___x_3648_, v___x_3649_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; lean_object* v___x_3652_; 
lean_dec_ref(v_e_3636_);
v___x_3651_ = lean_box(0);
v___x_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3651_);
return v___x_3652_;
}
else
{
lean_object* v___f_3653_; lean_object* v___x_3654_; 
v___f_3653_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVShiftLeft___closed__2));
v___x_3654_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3636_, v___f_3653_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_);
return v___x_3654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVShiftLeft___boxed(lean_object* v_e_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lean_Meta_Grind_propagateBVShiftLeft(v_e_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
lean_dec(v_a_3665_);
lean_dec_ref(v_a_3664_);
lean_dec(v_a_3663_);
lean_dec_ref(v_a_3662_);
lean_dec(v_a_3661_);
lean_dec_ref(v_a_3660_);
lean_dec(v_a_3659_);
lean_dec_ref(v_a_3658_);
lean_dec(v_a_3657_);
lean_dec(v_a_3656_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3262547096____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3669_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVShiftLeft___closed__1));
v___x_3670_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVShiftLeft___boxed), 12, 0);
v___x_3671_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3669_, v___x_3670_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3262547096____hygCtx___hyg_8____boxed(lean_object* v_a_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3262547096____hygCtx___hyg_8_();
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight___lam__0(lean_object* v_r_u2081_3674_, lean_object* v_r_u2082_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v___x_3687_; 
v___x_3687_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3674_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3743_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3690_ = v___x_3687_;
v_isShared_3691_ = v_isSharedCheck_3743_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3687_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3743_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
if (lean_obj_tag(v_a_3688_) == 1)
{
lean_object* v_val_3692_; lean_object* v_fst_3693_; lean_object* v_snd_3694_; lean_object* v___x_3695_; 
lean_del_object(v___x_3690_);
v_val_3692_ = lean_ctor_get(v_a_3688_, 0);
lean_inc(v_val_3692_);
lean_dec_ref_known(v_a_3688_, 1);
v_fst_3693_ = lean_ctor_get(v_val_3692_, 0);
lean_inc(v_fst_3693_);
v_snd_3694_ = lean_ctor_get(v_val_3692_, 1);
lean_inc(v_snd_3694_);
lean_dec(v_val_3692_);
v___x_3695_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_3675_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3730_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3698_ = v___x_3695_;
v_isShared_3699_ = v_isSharedCheck_3730_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3695_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3730_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
if (lean_obj_tag(v_a_3696_) == 1)
{
lean_object* v_val_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3725_; 
lean_del_object(v___x_3698_);
v_val_3700_ = lean_ctor_get(v_a_3696_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v_a_3696_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3702_ = v_a_3696_;
v_isShared_3703_ = v_isSharedCheck_3725_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_val_3700_);
lean_dec(v_a_3696_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3725_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3704_ = lean_nat_shiftr(v_snd_3694_, v_val_3700_);
lean_dec(v_val_3700_);
lean_dec(v_snd_3694_);
v___x_3705_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3693_, v___x_3704_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3716_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3708_ = v___x_3705_;
v_isShared_3709_ = v_isSharedCheck_3716_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3705_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3716_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 0, v_a_3706_);
v___x_3711_ = v___x_3702_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
lean_object* v___x_3713_; 
if (v_isShared_3709_ == 0)
{
lean_ctor_set(v___x_3708_, 0, v___x_3711_);
v___x_3713_ = v___x_3708_;
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
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_del_object(v___x_3702_);
v_a_3717_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3705_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3705_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
}
else
{
lean_object* v___x_3726_; lean_object* v___x_3728_; 
lean_dec(v_a_3696_);
lean_dec(v_snd_3694_);
lean_dec(v_fst_3693_);
v___x_3726_ = lean_box(0);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 0, v___x_3726_);
v___x_3728_ = v___x_3698_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3726_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_dec(v_snd_3694_);
lean_dec(v_fst_3693_);
v_a_3731_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3695_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3695_);
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
else
{
lean_object* v___x_3739_; lean_object* v___x_3741_; 
lean_dec(v_a_3688_);
v___x_3739_ = lean_box(0);
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 0, v___x_3739_);
v___x_3741_ = v___x_3690_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3739_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
else
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3751_; 
v_a_3744_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3746_ = v___x_3687_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3687_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3749_; 
if (v_isShared_3747_ == 0)
{
v___x_3749_ = v___x_3746_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3744_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight___lam__0___boxed(lean_object* v_r_u2081_3752_, lean_object* v_r_u2082_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_Meta_Grind_propagateBVUShiftRight___lam__0(v_r_u2081_3752_, v_r_u2082_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v_r_u2082_3753_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight(lean_object* v_e_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_){
_start:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; uint8_t v___x_3785_; 
v___x_3783_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVUShiftRight___closed__1));
v___x_3784_ = lean_unsigned_to_nat(3u);
v___x_3785_ = l_Lean_Expr_isAppOfArity(v_e_3771_, v___x_3783_, v___x_3784_);
if (v___x_3785_ == 0)
{
lean_object* v___x_3786_; lean_object* v___x_3787_; 
lean_dec_ref(v_e_3771_);
v___x_3786_ = lean_box(0);
v___x_3787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3786_);
return v___x_3787_;
}
else
{
lean_object* v___f_3788_; lean_object* v___x_3789_; 
v___f_3788_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVUShiftRight___closed__2));
v___x_3789_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3771_, v___f_3788_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
return v___x_3789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVUShiftRight___boxed(lean_object* v_e_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_Lean_Meta_Grind_propagateBVUShiftRight(v_e_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_);
lean_dec(v_a_3800_);
lean_dec_ref(v_a_3799_);
lean_dec(v_a_3798_);
lean_dec_ref(v_a_3797_);
lean_dec(v_a_3796_);
lean_dec_ref(v_a_3795_);
lean_dec(v_a_3794_);
lean_dec_ref(v_a_3793_);
lean_dec(v_a_3792_);
lean_dec(v_a_3791_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVUShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVUShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1878785357____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3804_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVUShiftRight___closed__1));
v___x_3805_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVUShiftRight___boxed), 12, 0);
v___x_3806_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3804_, v___x_3805_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVUShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVUShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1878785357____hygCtx___hyg_8____boxed(lean_object* v_a_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVUShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVUShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1878785357____hygCtx___hyg_8_();
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight___lam__0(lean_object* v_r_u2081_3809_, lean_object* v_r_u2082_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v___x_3822_; 
v___x_3822_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3809_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3878_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3825_ = v___x_3822_;
v_isShared_3826_ = v_isSharedCheck_3878_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3822_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3878_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
if (lean_obj_tag(v_a_3823_) == 1)
{
lean_object* v_val_3827_; lean_object* v_fst_3828_; lean_object* v_snd_3829_; lean_object* v___x_3830_; 
lean_del_object(v___x_3825_);
v_val_3827_ = lean_ctor_get(v_a_3823_, 0);
lean_inc(v_val_3827_);
lean_dec_ref_known(v_a_3823_, 1);
v_fst_3828_ = lean_ctor_get(v_val_3827_, 0);
lean_inc(v_fst_3828_);
v_snd_3829_ = lean_ctor_get(v_val_3827_, 1);
lean_inc(v_snd_3829_);
lean_dec(v_val_3827_);
v___x_3830_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_3810_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3865_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3833_ = v___x_3830_;
v_isShared_3834_ = v_isSharedCheck_3865_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3830_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3865_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
if (lean_obj_tag(v_a_3831_) == 1)
{
lean_object* v_val_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3860_; 
lean_del_object(v___x_3833_);
v_val_3835_ = lean_ctor_get(v_a_3831_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v_a_3831_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3837_ = v_a_3831_;
v_isShared_3838_ = v_isSharedCheck_3860_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_val_3835_);
lean_dec(v_a_3831_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3860_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3839_ = l_BitVec_sshiftRight(v_fst_3828_, v_snd_3829_, v_val_3835_);
lean_dec(v_val_3835_);
v___x_3840_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3828_, v___x_3839_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3851_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3843_ = v___x_3840_;
v_isShared_3844_ = v_isSharedCheck_3851_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3840_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3851_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 0, v_a_3841_);
v___x_3846_ = v___x_3837_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
lean_object* v___x_3848_; 
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 0, v___x_3846_);
v___x_3848_ = v___x_3843_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3846_);
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
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
lean_del_object(v___x_3837_);
v_a_3852_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3840_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3840_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
}
else
{
lean_object* v___x_3861_; lean_object* v___x_3863_; 
lean_dec(v_a_3831_);
lean_dec(v_snd_3829_);
lean_dec(v_fst_3828_);
v___x_3861_ = lean_box(0);
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 0, v___x_3861_);
v___x_3863_ = v___x_3833_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
lean_dec(v_snd_3829_);
lean_dec(v_fst_3828_);
v_a_3866_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3830_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3830_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
else
{
lean_object* v___x_3874_; lean_object* v___x_3876_; 
lean_dec(v_a_3823_);
v___x_3874_ = lean_box(0);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v___x_3874_);
v___x_3876_ = v___x_3825_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3874_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
return v___x_3876_;
}
}
}
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
v_a_3879_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3822_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3822_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight___lam__0___boxed(lean_object* v_r_u2081_3887_, lean_object* v_r_u2082_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_Meta_Grind_propagateBVSShiftRight___lam__0(v_r_u2081_3887_, v_r_u2082_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v_r_u2082_3888_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight(lean_object* v_e_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_){
_start:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; uint8_t v___x_3920_; 
v___x_3918_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSShiftRight___closed__1));
v___x_3919_ = lean_unsigned_to_nat(3u);
v___x_3920_ = l_Lean_Expr_isAppOfArity(v_e_3906_, v___x_3918_, v___x_3919_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
lean_dec_ref(v_e_3906_);
v___x_3921_ = lean_box(0);
v___x_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
return v___x_3922_;
}
else
{
lean_object* v___f_3923_; lean_object* v___x_3924_; 
v___f_3923_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSShiftRight___closed__2));
v___x_3924_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_3906_, v___f_3923_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_);
return v___x_3924_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVSShiftRight___boxed(lean_object* v_e_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_){
_start:
{
lean_object* v_res_3937_; 
v_res_3937_ = l_Lean_Meta_Grind_propagateBVSShiftRight(v_e_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_);
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
lean_dec(v_a_3929_);
lean_dec_ref(v_a_3928_);
lean_dec(v_a_3927_);
lean_dec(v_a_3926_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVSShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3342532823____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3939_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVSShiftRight___closed__1));
v___x_3940_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVSShiftRight___boxed), 12, 0);
v___x_3941_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_3939_, v___x_3940_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVSShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3342532823____hygCtx___hyg_8____boxed(lean_object* v_a_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVSShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3342532823____hygCtx___hyg_8_();
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft___lam__0(lean_object* v_r_u2081_3944_, lean_object* v_r_u2082_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
lean_object* v___x_3957_; 
v___x_3957_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_3944_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_4013_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_3960_ = v___x_3957_;
v_isShared_3961_ = v_isSharedCheck_4013_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3957_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_4013_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
if (lean_obj_tag(v_a_3958_) == 1)
{
lean_object* v_val_3962_; lean_object* v_fst_3963_; lean_object* v_snd_3964_; lean_object* v___x_3965_; 
lean_del_object(v___x_3960_);
v_val_3962_ = lean_ctor_get(v_a_3958_, 0);
lean_inc(v_val_3962_);
lean_dec_ref_known(v_a_3958_, 1);
v_fst_3963_ = lean_ctor_get(v_val_3962_, 0);
lean_inc(v_fst_3963_);
v_snd_3964_ = lean_ctor_get(v_val_3962_, 1);
lean_inc(v_snd_3964_);
lean_dec(v_val_3962_);
v___x_3965_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_3945_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_4000_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3968_ = v___x_3965_;
v_isShared_3969_ = v_isSharedCheck_4000_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3965_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_4000_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
if (lean_obj_tag(v_a_3966_) == 1)
{
lean_object* v_val_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3995_; 
lean_del_object(v___x_3968_);
v_val_3970_ = lean_ctor_get(v_a_3966_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v_a_3966_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3972_ = v_a_3966_;
v_isShared_3973_ = v_isSharedCheck_3995_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_val_3970_);
lean_dec(v_a_3966_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3995_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = l_BitVec_rotateLeft(v_fst_3963_, v_snd_3964_, v_val_3970_);
lean_dec(v_val_3970_);
lean_dec(v_snd_3964_);
v___x_3975_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_3963_, v___x_3974_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3986_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3978_ = v___x_3975_;
v_isShared_3979_ = v_isSharedCheck_3986_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3975_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3986_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3981_; 
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 0, v_a_3976_);
v___x_3981_ = v___x_3972_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_a_3976_);
v___x_3981_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
lean_object* v___x_3983_; 
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 0, v___x_3981_);
v___x_3983_ = v___x_3978_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v___x_3981_);
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
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
lean_del_object(v___x_3972_);
v_a_3987_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3989_ = v___x_3975_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3975_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
}
}
else
{
lean_object* v___x_3996_; lean_object* v___x_3998_; 
lean_dec(v_a_3966_);
lean_dec(v_snd_3964_);
lean_dec(v_fst_3963_);
v___x_3996_ = lean_box(0);
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 0, v___x_3996_);
v___x_3998_ = v___x_3968_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3996_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
lean_dec(v_snd_3964_);
lean_dec(v_fst_3963_);
v_a_4001_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3965_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3965_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
else
{
lean_object* v___x_4009_; lean_object* v___x_4011_; 
lean_dec(v_a_3958_);
v___x_4009_ = lean_box(0);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v___x_4009_);
v___x_4011_ = v___x_3960_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_4009_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
v_a_4014_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_3957_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_3957_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft___lam__0___boxed(lean_object* v_r_u2081_4022_, lean_object* v_r_u2082_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_Meta_Grind_propagateBVRotateLeft___lam__0(v_r_u2081_4022_, v_r_u2082_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v_r_u2082_4023_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft(lean_object* v_e_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_){
_start:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; uint8_t v___x_4055_; 
v___x_4053_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateLeft___closed__1));
v___x_4054_ = lean_unsigned_to_nat(3u);
v___x_4055_ = l_Lean_Expr_isAppOfArity(v_e_4041_, v___x_4053_, v___x_4054_);
if (v___x_4055_ == 0)
{
lean_object* v___x_4056_; lean_object* v___x_4057_; 
lean_dec_ref(v_e_4041_);
v___x_4056_ = lean_box(0);
v___x_4057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4056_);
return v___x_4057_;
}
else
{
lean_object* v___f_4058_; lean_object* v___x_4059_; 
v___f_4058_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateLeft___closed__2));
v___x_4059_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4041_, v___f_4058_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_);
return v___x_4059_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateLeft___boxed(lean_object* v_e_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l_Lean_Meta_Grind_propagateBVRotateLeft(v_e_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_);
lean_dec(v_a_4070_);
lean_dec_ref(v_a_4069_);
lean_dec(v_a_4068_);
lean_dec_ref(v_a_4067_);
lean_dec(v_a_4066_);
lean_dec_ref(v_a_4065_);
lean_dec(v_a_4064_);
lean_dec_ref(v_a_4063_);
lean_dec(v_a_4062_);
lean_dec(v_a_4061_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateLeft___regBuiltin_Lean_Meta_Grind_propagateBVRotateLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1541346404____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4074_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateLeft___closed__1));
v___x_4075_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVRotateLeft___boxed), 12, 0);
v___x_4076_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4074_, v___x_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateLeft___regBuiltin_Lean_Meta_Grind_propagateBVRotateLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1541346404____hygCtx___hyg_8____boxed(lean_object* v_a_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateLeft___regBuiltin_Lean_Meta_Grind_propagateBVRotateLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1541346404____hygCtx___hyg_8_();
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateRight___lam__0(lean_object* v_r_u2081_4079_, lean_object* v_r_u2082_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
lean_object* v___x_4092_; 
v___x_4092_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4079_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4148_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4095_ = v___x_4092_;
v_isShared_4096_ = v_isSharedCheck_4148_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4092_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4148_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
if (lean_obj_tag(v_a_4093_) == 1)
{
lean_object* v_val_4097_; lean_object* v_fst_4098_; lean_object* v_snd_4099_; lean_object* v___x_4100_; 
lean_del_object(v___x_4095_);
v_val_4097_ = lean_ctor_get(v_a_4093_, 0);
lean_inc(v_val_4097_);
lean_dec_ref_known(v_a_4093_, 1);
v_fst_4098_ = lean_ctor_get(v_val_4097_, 0);
lean_inc(v_fst_4098_);
v_snd_4099_ = lean_ctor_get(v_val_4097_, 1);
lean_inc(v_snd_4099_);
lean_dec(v_val_4097_);
v___x_4100_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4080_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4135_; 
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4103_ = v___x_4100_;
v_isShared_4104_ = v_isSharedCheck_4135_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4100_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4135_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
if (lean_obj_tag(v_a_4101_) == 1)
{
lean_object* v_val_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4130_; 
lean_del_object(v___x_4103_);
v_val_4105_ = lean_ctor_get(v_a_4101_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v_a_4101_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4107_ = v_a_4101_;
v_isShared_4108_ = v_isSharedCheck_4130_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_val_4105_);
lean_dec(v_a_4101_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4130_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4109_ = l_BitVec_rotateRight(v_fst_4098_, v_snd_4099_, v_val_4105_);
lean_dec(v_val_4105_);
lean_dec(v_snd_4099_);
v___x_4110_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4098_, v___x_4109_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4121_; 
v_a_4111_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4113_ = v___x_4110_;
v_isShared_4114_ = v_isSharedCheck_4121_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4110_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4121_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4108_ == 0)
{
lean_ctor_set(v___x_4107_, 0, v_a_4111_);
v___x_4116_ = v___x_4107_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
lean_object* v___x_4118_; 
if (v_isShared_4114_ == 0)
{
lean_ctor_set(v___x_4113_, 0, v___x_4116_);
v___x_4118_ = v___x_4113_;
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
else
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
lean_del_object(v___x_4107_);
v_a_4122_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___x_4110_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4110_);
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
lean_object* v___x_4131_; lean_object* v___x_4133_; 
lean_dec(v_a_4101_);
lean_dec(v_snd_4099_);
lean_dec(v_fst_4098_);
v___x_4131_ = lean_box(0);
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 0, v___x_4131_);
v___x_4133_ = v___x_4103_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4131_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_dec(v_snd_4099_);
lean_dec(v_fst_4098_);
v_a_4136_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4100_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4100_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
else
{
lean_object* v___x_4144_; lean_object* v___x_4146_; 
lean_dec(v_a_4093_);
v___x_4144_ = lean_box(0);
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 0, v___x_4144_);
v___x_4146_ = v___x_4095_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v___x_4144_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
v_a_4149_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4151_ = v___x_4092_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___x_4092_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateRight___lam__0___boxed(lean_object* v_r_u2081_4157_, lean_object* v_r_u2082_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Lean_Meta_Grind_propagateBVRotateRight___lam__0(v_r_u2081_4157_, v_r_u2082_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec(v___y_4159_);
lean_dec_ref(v_r_u2082_4158_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateRight(lean_object* v_e_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_){
_start:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; 
v___x_4188_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateRight___closed__1));
v___x_4189_ = lean_unsigned_to_nat(3u);
v___x_4190_ = l_Lean_Expr_isAppOfArity(v_e_4176_, v___x_4188_, v___x_4189_);
if (v___x_4190_ == 0)
{
lean_object* v___x_4191_; lean_object* v___x_4192_; 
lean_dec_ref(v_e_4176_);
v___x_4191_ = lean_box(0);
v___x_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
return v___x_4192_;
}
else
{
lean_object* v___f_4193_; lean_object* v___x_4194_; 
v___f_4193_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateRight___closed__2));
v___x_4194_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4176_, v___f_4193_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_);
return v___x_4194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVRotateRight___boxed(lean_object* v_e_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_Meta_Grind_propagateBVRotateRight(v_e_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_);
lean_dec(v_a_4205_);
lean_dec_ref(v_a_4204_);
lean_dec(v_a_4203_);
lean_dec_ref(v_a_4202_);
lean_dec(v_a_4201_);
lean_dec_ref(v_a_4200_);
lean_dec(v_a_4199_);
lean_dec_ref(v_a_4198_);
lean_dec(v_a_4197_);
lean_dec(v_a_4196_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateRight___regBuiltin_Lean_Meta_Grind_propagateBVRotateRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2456321972____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4209_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVRotateRight___closed__1));
v___x_4210_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVRotateRight___boxed), 12, 0);
v___x_4211_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4209_, v___x_4210_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateRight___regBuiltin_Lean_Meta_Grind_propagateBVRotateRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2456321972____hygCtx___hyg_8____boxed(lean_object* v_a_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateRight___regBuiltin_Lean_Meta_Grind_propagateBVRotateRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2456321972____hygCtx___hyg_8_();
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0(lean_object* v_op_4214_, lean_object* v_r_u2081_4215_, lean_object* v_r_u2082_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4215_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
if (lean_obj_tag(v___x_4228_) == 0)
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4321_; 
v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4231_ = v___x_4228_;
v_isShared_4232_ = v_isSharedCheck_4321_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4228_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4321_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
if (lean_obj_tag(v_a_4229_) == 1)
{
lean_object* v_val_4233_; lean_object* v_fst_4234_; lean_object* v_snd_4235_; lean_object* v___x_4236_; 
lean_del_object(v___x_4231_);
v_val_4233_ = lean_ctor_get(v_a_4229_, 0);
lean_inc(v_val_4233_);
lean_dec_ref_known(v_a_4229_, 1);
v_fst_4234_ = lean_ctor_get(v_val_4233_, 0);
lean_inc(v_fst_4234_);
v_snd_4235_ = lean_ctor_get(v_val_4233_, 1);
lean_inc(v_snd_4235_);
lean_dec(v_val_4233_);
v___x_4236_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4216_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4237_);
lean_dec_ref_known(v___x_4236_, 1);
if (lean_obj_tag(v_a_4237_) == 1)
{
lean_object* v_val_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4263_; 
lean_dec_ref(v_r_u2082_4216_);
v_val_4238_ = lean_ctor_get(v_a_4237_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v_a_4237_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4240_ = v_a_4237_;
v_isShared_4241_ = v_isSharedCheck_4263_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_val_4238_);
lean_dec(v_a_4237_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4263_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; 
lean_inc(v_fst_4234_);
v___x_4242_ = lean_apply_3(v_op_4214_, v_fst_4234_, v_snd_4235_, v_val_4238_);
v___x_4243_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4234_, v___x_4242_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4254_; 
v_a_4244_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4246_ = v___x_4243_;
v_isShared_4247_ = v_isSharedCheck_4254_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4243_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4254_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 0, v_a_4244_);
v___x_4249_ = v___x_4240_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4244_);
v___x_4249_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
lean_object* v___x_4251_; 
if (v_isShared_4247_ == 0)
{
lean_ctor_set(v___x_4246_, 0, v___x_4249_);
v___x_4251_ = v___x_4246_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4249_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
else
{
lean_object* v_a_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4262_; 
lean_del_object(v___x_4240_);
v_a_4255_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4262_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4257_ = v___x_4243_;
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_a_4255_);
lean_dec(v___x_4243_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___x_4260_; 
if (v_isShared_4258_ == 0)
{
v___x_4260_ = v___x_4257_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_a_4255_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
return v___x_4260_;
}
}
}
}
}
else
{
lean_object* v___x_4264_; 
lean_dec(v_a_4237_);
v___x_4264_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_4216_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4300_; 
v_a_4265_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4267_ = v___x_4264_;
v_isShared_4268_ = v_isSharedCheck_4300_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4264_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4300_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
if (lean_obj_tag(v_a_4265_) == 1)
{
lean_object* v_val_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4295_; 
lean_del_object(v___x_4267_);
v_val_4269_ = lean_ctor_get(v_a_4265_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v_a_4265_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4271_ = v_a_4265_;
v_isShared_4272_ = v_isSharedCheck_4295_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_val_4269_);
lean_dec(v_a_4265_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4295_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v_snd_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v_snd_4273_ = lean_ctor_get(v_val_4269_, 1);
lean_inc(v_snd_4273_);
lean_dec(v_val_4269_);
lean_inc(v_fst_4234_);
v___x_4274_ = lean_apply_3(v_op_4214_, v_fst_4234_, v_snd_4235_, v_snd_4273_);
v___x_4275_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4234_, v___x_4274_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4286_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4278_ = v___x_4275_;
v_isShared_4279_ = v_isSharedCheck_4286_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4275_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4286_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4281_; 
if (v_isShared_4272_ == 0)
{
lean_ctor_set(v___x_4271_, 0, v_a_4276_);
v___x_4281_ = v___x_4271_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4276_);
v___x_4281_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
lean_object* v___x_4283_; 
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 0, v___x_4281_);
v___x_4283_ = v___x_4278_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v___x_4281_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
}
else
{
lean_object* v_a_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4294_; 
lean_del_object(v___x_4271_);
v_a_4287_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4289_ = v___x_4275_;
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_a_4287_);
lean_dec(v___x_4275_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
if (v_isShared_4290_ == 0)
{
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4287_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
}
}
else
{
lean_object* v___x_4296_; lean_object* v___x_4298_; 
lean_dec(v_a_4265_);
lean_dec(v_snd_4235_);
lean_dec(v_fst_4234_);
lean_dec_ref(v_op_4214_);
v___x_4296_ = lean_box(0);
if (v_isShared_4268_ == 0)
{
lean_ctor_set(v___x_4267_, 0, v___x_4296_);
v___x_4298_ = v___x_4267_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v___x_4296_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
}
else
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4308_; 
lean_dec(v_snd_4235_);
lean_dec(v_fst_4234_);
lean_dec_ref(v_op_4214_);
v_a_4301_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4303_ = v___x_4264_;
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4264_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4306_; 
if (v_isShared_4304_ == 0)
{
v___x_4306_ = v___x_4303_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4301_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
}
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
lean_dec(v_snd_4235_);
lean_dec(v_fst_4234_);
lean_dec_ref(v_r_u2082_4216_);
lean_dec_ref(v_op_4214_);
v_a_4309_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v___x_4236_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4236_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
}
}
else
{
lean_object* v___x_4317_; lean_object* v___x_4319_; 
lean_dec(v_a_4229_);
lean_dec_ref(v_r_u2082_4216_);
lean_dec_ref(v_op_4214_);
v___x_4317_ = lean_box(0);
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 0, v___x_4317_);
v___x_4319_ = v___x_4231_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v___x_4317_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
}
else
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4329_; 
lean_dec_ref(v_r_u2082_4216_);
lean_dec_ref(v_op_4214_);
v_a_4322_ = lean_ctor_get(v___x_4228_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4324_ = v___x_4228_;
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4228_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4327_; 
if (v_isShared_4325_ == 0)
{
v___x_4327_ = v___x_4324_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0___boxed(lean_object* v_op_4330_, lean_object* v_r_u2081_4331_, lean_object* v_r_u2082_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0(v_op_4330_, v_r_u2081_4331_, v_r_u2082_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
lean_dec(v___y_4334_);
lean_dec(v___y_4333_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV(lean_object* v_declName_4345_, lean_object* v_op_4346_, lean_object* v_e_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_){
_start:
{
lean_object* v___x_4359_; uint8_t v___x_4360_; 
v___x_4359_ = lean_unsigned_to_nat(6u);
v___x_4360_ = l_Lean_Expr_isAppOfArity(v_e_4347_, v_declName_4345_, v___x_4359_);
if (v___x_4360_ == 0)
{
lean_object* v___x_4361_; lean_object* v___x_4362_; 
lean_dec_ref(v_e_4347_);
lean_dec_ref(v_op_4346_);
v___x_4361_ = lean_box(0);
v___x_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4361_);
return v___x_4362_;
}
else
{
lean_object* v___f_4363_; lean_object* v___x_4364_; 
v___f_4363_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___lam__0___boxed), 14, 1);
lean_closure_set(v___f_4363_, 0, v_op_4346_);
v___x_4364_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4347_, v___f_4363_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
return v___x_4364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV___boxed(lean_object* v_declName_4365_, lean_object* v_op_4366_, lean_object* v_e_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_hShiftBV(v_declName_4365_, v_op_4366_, v_e_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
lean_dec(v_a_4377_);
lean_dec_ref(v_a_4376_);
lean_dec(v_a_4375_);
lean_dec_ref(v_a_4374_);
lean_dec(v_a_4373_);
lean_dec_ref(v_a_4372_);
lean_dec(v_a_4371_);
lean_dec_ref(v_a_4370_);
lean_dec(v_a_4369_);
lean_dec(v_a_4368_);
lean_dec(v_declName_4365_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___lam__0(lean_object* v_r_u2081_4380_, lean_object* v_r_u2082_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_){
_start:
{
lean_object* v___x_4393_; 
v___x_4393_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4380_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4393_) == 0)
{
lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4486_; 
v_a_4394_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4396_ = v___x_4393_;
v_isShared_4397_ = v_isSharedCheck_4486_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v___x_4393_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4486_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
if (lean_obj_tag(v_a_4394_) == 1)
{
lean_object* v_val_4398_; lean_object* v_fst_4399_; lean_object* v_snd_4400_; lean_object* v___x_4401_; 
lean_del_object(v___x_4396_);
v_val_4398_ = lean_ctor_get(v_a_4394_, 0);
lean_inc(v_val_4398_);
lean_dec_ref_known(v_a_4394_, 1);
v_fst_4399_ = lean_ctor_get(v_val_4398_, 0);
lean_inc(v_fst_4399_);
v_snd_4400_ = lean_ctor_get(v_val_4398_, 1);
lean_inc(v_snd_4400_);
lean_dec(v_val_4398_);
v___x_4401_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4381_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_a_4402_);
lean_dec_ref_known(v___x_4401_, 1);
if (lean_obj_tag(v_a_4402_) == 1)
{
lean_object* v_val_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4428_; 
lean_dec_ref(v_r_u2082_4381_);
v_val_4403_ = lean_ctor_get(v_a_4402_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v_a_4402_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4405_ = v_a_4402_;
v_isShared_4406_ = v_isSharedCheck_4428_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_val_4403_);
lean_dec(v_a_4402_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4428_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4407_ = l_BitVec_shiftLeft(v_fst_4399_, v_snd_4400_, v_val_4403_);
lean_dec(v_val_4403_);
lean_dec(v_snd_4400_);
v___x_4408_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4399_, v___x_4407_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4419_; 
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4411_ = v___x_4408_;
v_isShared_4412_ = v_isSharedCheck_4419_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4408_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4419_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4406_ == 0)
{
lean_ctor_set(v___x_4405_, 0, v_a_4409_);
v___x_4414_ = v___x_4405_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4409_);
v___x_4414_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
lean_object* v___x_4416_; 
if (v_isShared_4412_ == 0)
{
lean_ctor_set(v___x_4411_, 0, v___x_4414_);
v___x_4416_ = v___x_4411_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v___x_4414_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
else
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4427_; 
lean_del_object(v___x_4405_);
v_a_4420_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v___x_4408_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4408_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4425_; 
if (v_isShared_4423_ == 0)
{
v___x_4425_ = v___x_4422_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4420_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
return v___x_4425_;
}
}
}
}
}
else
{
lean_object* v___x_4429_; 
lean_dec(v_a_4402_);
v___x_4429_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_4381_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4465_; 
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4432_ = v___x_4429_;
v_isShared_4433_ = v_isSharedCheck_4465_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4429_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4465_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
if (lean_obj_tag(v_a_4430_) == 1)
{
lean_object* v_val_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4460_; 
lean_del_object(v___x_4432_);
v_val_4434_ = lean_ctor_get(v_a_4430_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v_a_4430_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4436_ = v_a_4430_;
v_isShared_4437_ = v_isSharedCheck_4460_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_val_4434_);
lean_dec(v_a_4430_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4460_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v_snd_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
v_snd_4438_ = lean_ctor_get(v_val_4434_, 1);
lean_inc(v_snd_4438_);
lean_dec(v_val_4434_);
v___x_4439_ = l_BitVec_shiftLeft(v_fst_4399_, v_snd_4400_, v_snd_4438_);
lean_dec(v_snd_4438_);
lean_dec(v_snd_4400_);
v___x_4440_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4399_, v___x_4439_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_object* v_a_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4451_; 
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4443_ = v___x_4440_;
v_isShared_4444_ = v_isSharedCheck_4451_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_a_4441_);
lean_dec(v___x_4440_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4451_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4446_; 
if (v_isShared_4437_ == 0)
{
lean_ctor_set(v___x_4436_, 0, v_a_4441_);
v___x_4446_ = v___x_4436_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_a_4441_);
v___x_4446_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
lean_object* v___x_4448_; 
if (v_isShared_4444_ == 0)
{
lean_ctor_set(v___x_4443_, 0, v___x_4446_);
v___x_4448_ = v___x_4443_;
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
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_del_object(v___x_4436_);
v_a_4452_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4440_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4440_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4452_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
}
else
{
lean_object* v___x_4461_; lean_object* v___x_4463_; 
lean_dec(v_a_4430_);
lean_dec(v_snd_4400_);
lean_dec(v_fst_4399_);
v___x_4461_ = lean_box(0);
if (v_isShared_4433_ == 0)
{
lean_ctor_set(v___x_4432_, 0, v___x_4461_);
v___x_4463_ = v___x_4432_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v___x_4461_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
}
else
{
lean_object* v_a_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4473_; 
lean_dec(v_snd_4400_);
lean_dec(v_fst_4399_);
v_a_4466_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4468_ = v___x_4429_;
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_a_4466_);
lean_dec(v___x_4429_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4471_; 
if (v_isShared_4469_ == 0)
{
v___x_4471_ = v___x_4468_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4466_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
}
}
else
{
lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4481_; 
lean_dec(v_snd_4400_);
lean_dec(v_fst_4399_);
lean_dec_ref(v_r_u2082_4381_);
v_a_4474_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4476_ = v___x_4401_;
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v___x_4401_);
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
else
{
lean_object* v___x_4482_; lean_object* v___x_4484_; 
lean_dec(v_a_4394_);
lean_dec_ref(v_r_u2082_4381_);
v___x_4482_ = lean_box(0);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 0, v___x_4482_);
v___x_4484_ = v___x_4396_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v___x_4482_);
v___x_4484_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
return v___x_4484_;
}
}
}
}
else
{
lean_object* v_a_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4494_; 
lean_dec_ref(v_r_u2082_4381_);
v_a_4487_ = lean_ctor_get(v___x_4393_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4489_ = v___x_4393_;
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_a_4487_);
lean_dec(v___x_4393_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4492_; 
if (v_isShared_4490_ == 0)
{
v___x_4492_ = v___x_4489_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_a_4487_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___lam__0___boxed(lean_object* v_r_u2081_4495_, lean_object* v_r_u2082_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l_Lean_Meta_Grind_propagateBVHShiftLeft___lam__0(v_r_u2081_4495_, v_r_u2082_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_);
lean_dec(v___y_4506_);
lean_dec_ref(v___y_4505_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec(v___y_4497_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft(lean_object* v_e_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_){
_start:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; uint8_t v___x_4529_; 
v___x_4527_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__2));
v___x_4528_ = lean_unsigned_to_nat(6u);
v___x_4529_ = l_Lean_Expr_isAppOfArity(v_e_4515_, v___x_4527_, v___x_4528_);
if (v___x_4529_ == 0)
{
lean_object* v___x_4530_; lean_object* v___x_4531_; 
lean_dec_ref(v_e_4515_);
v___x_4530_ = lean_box(0);
v___x_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
return v___x_4531_;
}
else
{
lean_object* v___f_4532_; lean_object* v___x_4533_; 
v___f_4532_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__3));
v___x_4533_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4515_, v___f_4532_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_);
return v___x_4533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftLeft___boxed(lean_object* v_e_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l_Lean_Meta_Grind_propagateBVHShiftLeft(v_e_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_);
lean_dec(v_a_4544_);
lean_dec_ref(v_a_4543_);
lean_dec(v_a_4542_);
lean_dec_ref(v_a_4541_);
lean_dec(v_a_4540_);
lean_dec_ref(v_a_4539_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
lean_dec(v_a_4536_);
lean_dec(v_a_4535_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2458924947____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; 
v___x_4548_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVHShiftLeft___closed__2));
v___x_4549_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVHShiftLeft___boxed), 12, 0);
v___x_4550_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4548_, v___x_4549_);
return v___x_4550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2458924947____hygCtx___hyg_8____boxed(lean_object* v_a_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2458924947____hygCtx___hyg_8_();
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight___lam__0(lean_object* v_r_u2081_4553_, lean_object* v_r_u2082_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v___x_4566_; 
v___x_4566_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4553_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4566_) == 0)
{
lean_object* v_a_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4659_; 
v_a_4567_ = lean_ctor_get(v___x_4566_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4566_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4569_ = v___x_4566_;
v_isShared_4570_ = v_isSharedCheck_4659_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_a_4567_);
lean_dec(v___x_4566_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4659_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
if (lean_obj_tag(v_a_4567_) == 1)
{
lean_object* v_val_4571_; lean_object* v_fst_4572_; lean_object* v_snd_4573_; lean_object* v___x_4574_; 
lean_del_object(v___x_4569_);
v_val_4571_ = lean_ctor_get(v_a_4567_, 0);
lean_inc(v_val_4571_);
lean_dec_ref_known(v_a_4567_, 1);
v_fst_4572_ = lean_ctor_get(v_val_4571_, 0);
lean_inc(v_fst_4572_);
v_snd_4573_ = lean_ctor_get(v_val_4571_, 1);
lean_inc(v_snd_4573_);
lean_dec(v_val_4571_);
v___x_4574_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4554_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
lean_inc(v_a_4575_);
lean_dec_ref_known(v___x_4574_, 1);
if (lean_obj_tag(v_a_4575_) == 1)
{
lean_object* v_val_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4601_; 
lean_dec_ref(v_r_u2082_4554_);
v_val_4576_ = lean_ctor_get(v_a_4575_, 0);
v_isSharedCheck_4601_ = !lean_is_exclusive(v_a_4575_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4578_ = v_a_4575_;
v_isShared_4579_ = v_isSharedCheck_4601_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_val_4576_);
lean_dec(v_a_4575_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4601_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4580_; lean_object* v___x_4581_; 
v___x_4580_ = lean_nat_shiftr(v_snd_4573_, v_val_4576_);
lean_dec(v_val_4576_);
lean_dec(v_snd_4573_);
v___x_4581_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4572_, v___x_4580_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4581_) == 0)
{
lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4592_; 
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4584_ = v___x_4581_;
v_isShared_4585_ = v_isSharedCheck_4592_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___x_4581_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4592_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4587_; 
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 0, v_a_4582_);
v___x_4587_ = v___x_4578_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4582_);
v___x_4587_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
lean_object* v___x_4589_; 
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 0, v___x_4587_);
v___x_4589_ = v___x_4584_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v___x_4587_);
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
else
{
lean_object* v_a_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4600_; 
lean_del_object(v___x_4578_);
v_a_4593_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4595_ = v___x_4581_;
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_a_4593_);
lean_dec(v___x_4581_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4600_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4598_; 
if (v_isShared_4596_ == 0)
{
v___x_4598_ = v___x_4595_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4593_);
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
}
else
{
lean_object* v___x_4602_; 
lean_dec(v_a_4575_);
v___x_4602_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2082_4554_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4638_; 
v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4605_ = v___x_4602_;
v_isShared_4606_ = v_isSharedCheck_4638_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4602_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4638_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
if (lean_obj_tag(v_a_4603_) == 1)
{
lean_object* v_val_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4633_; 
lean_del_object(v___x_4605_);
v_val_4607_ = lean_ctor_get(v_a_4603_, 0);
v_isSharedCheck_4633_ = !lean_is_exclusive(v_a_4603_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4609_ = v_a_4603_;
v_isShared_4610_ = v_isSharedCheck_4633_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_val_4607_);
lean_dec(v_a_4603_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4633_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v_snd_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; 
v_snd_4611_ = lean_ctor_get(v_val_4607_, 1);
lean_inc(v_snd_4611_);
lean_dec(v_val_4607_);
v___x_4612_ = lean_nat_shiftr(v_snd_4573_, v_snd_4611_);
lean_dec(v_snd_4611_);
lean_dec(v_snd_4573_);
v___x_4613_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBVLit___redArg(v_fst_4572_, v___x_4612_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4624_; 
v_a_4614_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4616_ = v___x_4613_;
v_isShared_4617_ = v_isSharedCheck_4624_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4613_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4624_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4619_; 
if (v_isShared_4610_ == 0)
{
lean_ctor_set(v___x_4609_, 0, v_a_4614_);
v___x_4619_ = v___x_4609_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_a_4614_);
v___x_4619_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
lean_object* v___x_4621_; 
if (v_isShared_4617_ == 0)
{
lean_ctor_set(v___x_4616_, 0, v___x_4619_);
v___x_4621_ = v___x_4616_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4619_);
v___x_4621_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
return v___x_4621_;
}
}
}
}
else
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4632_; 
lean_del_object(v___x_4609_);
v_a_4625_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4627_ = v___x_4613_;
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4613_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4628_ == 0)
{
v___x_4630_ = v___x_4627_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4625_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
}
}
else
{
lean_object* v___x_4634_; lean_object* v___x_4636_; 
lean_dec(v_a_4603_);
lean_dec(v_snd_4573_);
lean_dec(v_fst_4572_);
v___x_4634_ = lean_box(0);
if (v_isShared_4606_ == 0)
{
lean_ctor_set(v___x_4605_, 0, v___x_4634_);
v___x_4636_ = v___x_4605_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v___x_4634_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
}
else
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4646_; 
lean_dec(v_snd_4573_);
lean_dec(v_fst_4572_);
v_a_4639_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4641_ = v___x_4602_;
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v___x_4602_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4644_; 
if (v_isShared_4642_ == 0)
{
v___x_4644_ = v___x_4641_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
v___x_4644_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
return v___x_4644_;
}
}
}
}
}
else
{
lean_object* v_a_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4654_; 
lean_dec(v_snd_4573_);
lean_dec(v_fst_4572_);
lean_dec_ref(v_r_u2082_4554_);
v_a_4647_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4654_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4654_ == 0)
{
v___x_4649_ = v___x_4574_;
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_a_4647_);
lean_dec(v___x_4574_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4654_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4652_; 
if (v_isShared_4650_ == 0)
{
v___x_4652_ = v___x_4649_;
goto v_reusejp_4651_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_a_4647_);
v___x_4652_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4651_;
}
v_reusejp_4651_:
{
return v___x_4652_;
}
}
}
}
else
{
lean_object* v___x_4655_; lean_object* v___x_4657_; 
lean_dec(v_a_4567_);
lean_dec_ref(v_r_u2082_4554_);
v___x_4655_ = lean_box(0);
if (v_isShared_4570_ == 0)
{
lean_ctor_set(v___x_4569_, 0, v___x_4655_);
v___x_4657_ = v___x_4569_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v___x_4655_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
}
}
else
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4667_; 
lean_dec_ref(v_r_u2082_4554_);
v_a_4660_ = lean_ctor_get(v___x_4566_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4566_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4662_ = v___x_4566_;
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4566_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4665_; 
if (v_isShared_4663_ == 0)
{
v___x_4665_ = v___x_4662_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_a_4660_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight___lam__0___boxed(lean_object* v_r_u2081_4668_, lean_object* v_r_u2082_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_){
_start:
{
lean_object* v_res_4681_; 
v_res_4681_ = l_Lean_Meta_Grind_propagateBVHShiftRight___lam__0(v_r_u2081_4668_, v_r_u2082_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_);
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4678_);
lean_dec(v___y_4677_);
lean_dec_ref(v___y_4676_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec(v___y_4671_);
lean_dec(v___y_4670_);
return v_res_4681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight(lean_object* v_e_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_){
_start:
{
lean_object* v___x_4700_; lean_object* v___x_4701_; uint8_t v___x_4702_; 
v___x_4700_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVHShiftRight___closed__2));
v___x_4701_ = lean_unsigned_to_nat(6u);
v___x_4702_ = l_Lean_Expr_isAppOfArity(v_e_4688_, v___x_4700_, v___x_4701_);
if (v___x_4702_ == 0)
{
lean_object* v___x_4703_; lean_object* v___x_4704_; 
lean_dec_ref(v_e_4688_);
v___x_4703_ = lean_box(0);
v___x_4704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4703_);
return v___x_4704_;
}
else
{
lean_object* v___f_4705_; lean_object* v___x_4706_; 
v___f_4705_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVHShiftRight___closed__3));
v___x_4706_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4688_, v___f_4705_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_);
return v___x_4706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVHShiftRight___boxed(lean_object* v_e_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_){
_start:
{
lean_object* v_res_4719_; 
v_res_4719_ = l_Lean_Meta_Grind_propagateBVHShiftRight(v_e_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_);
lean_dec(v_a_4717_);
lean_dec_ref(v_a_4716_);
lean_dec(v_a_4715_);
lean_dec_ref(v_a_4714_);
lean_dec(v_a_4713_);
lean_dec_ref(v_a_4712_);
lean_dec(v_a_4711_);
lean_dec_ref(v_a_4710_);
lean_dec(v_a_4709_);
lean_dec(v_a_4708_);
return v_res_4719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVHShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1131064821____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4721_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVHShiftRight___closed__2));
v___x_4722_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVHShiftRight___boxed), 12, 0);
v___x_4723_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4721_, v___x_4722_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVHShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1131064821____hygCtx___hyg_8____boxed(lean_object* v_a_4724_){
_start:
{
lean_object* v_res_4725_; 
v_res_4725_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVHShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1131064821____hygCtx___hyg_8_();
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD___lam__0(lean_object* v_r_u2081_4726_, lean_object* v_r_u2082_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
lean_object* v___x_4739_; 
v___x_4739_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4726_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
if (lean_obj_tag(v___x_4739_) == 0)
{
lean_object* v_a_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4794_; 
v_a_4740_ = lean_ctor_get(v___x_4739_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4742_ = v___x_4739_;
v_isShared_4743_ = v_isSharedCheck_4794_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_a_4740_);
lean_dec(v___x_4739_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4794_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
if (lean_obj_tag(v_a_4740_) == 1)
{
lean_object* v_val_4744_; lean_object* v_snd_4745_; lean_object* v___x_4746_; 
lean_del_object(v___x_4742_);
v_val_4744_ = lean_ctor_get(v_a_4740_, 0);
lean_inc(v_val_4744_);
lean_dec_ref_known(v_a_4740_, 1);
v_snd_4745_ = lean_ctor_get(v_val_4744_, 1);
lean_inc(v_snd_4745_);
lean_dec(v_val_4744_);
v___x_4746_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4727_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
if (lean_obj_tag(v___x_4746_) == 0)
{
lean_object* v_a_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4781_; 
v_a_4747_ = lean_ctor_get(v___x_4746_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4749_ = v___x_4746_;
v_isShared_4750_ = v_isSharedCheck_4781_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_a_4747_);
lean_dec(v___x_4746_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4781_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
if (lean_obj_tag(v_a_4747_) == 1)
{
lean_object* v_val_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4776_; 
lean_del_object(v___x_4749_);
v_val_4751_ = lean_ctor_get(v_a_4747_, 0);
v_isSharedCheck_4776_ = !lean_is_exclusive(v_a_4747_);
if (v_isSharedCheck_4776_ == 0)
{
v___x_4753_ = v_a_4747_;
v_isShared_4754_ = v_isSharedCheck_4776_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_val_4751_);
lean_dec(v_a_4747_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4776_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
uint8_t v___x_4755_; lean_object* v___x_4756_; 
v___x_4755_ = l_Nat_testBit(v_snd_4745_, v_val_4751_);
lean_dec(v_val_4751_);
lean_dec(v_snd_4745_);
v___x_4756_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v___x_4755_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
if (lean_obj_tag(v___x_4756_) == 0)
{
lean_object* v_a_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4767_; 
v_a_4757_ = lean_ctor_get(v___x_4756_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4756_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4759_ = v___x_4756_;
v_isShared_4760_ = v_isSharedCheck_4767_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_a_4757_);
lean_dec(v___x_4756_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4767_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4762_; 
if (v_isShared_4754_ == 0)
{
lean_ctor_set(v___x_4753_, 0, v_a_4757_);
v___x_4762_ = v___x_4753_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4757_);
v___x_4762_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
lean_object* v___x_4764_; 
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 0, v___x_4762_);
v___x_4764_ = v___x_4759_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4762_);
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
else
{
lean_object* v_a_4768_; lean_object* v___x_4770_; uint8_t v_isShared_4771_; uint8_t v_isSharedCheck_4775_; 
lean_del_object(v___x_4753_);
v_a_4768_ = lean_ctor_get(v___x_4756_, 0);
v_isSharedCheck_4775_ = !lean_is_exclusive(v___x_4756_);
if (v_isSharedCheck_4775_ == 0)
{
v___x_4770_ = v___x_4756_;
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
else
{
lean_inc(v_a_4768_);
lean_dec(v___x_4756_);
v___x_4770_ = lean_box(0);
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
v_resetjp_4769_:
{
lean_object* v___x_4773_; 
if (v_isShared_4771_ == 0)
{
v___x_4773_ = v___x_4770_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v_a_4768_);
v___x_4773_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
return v___x_4773_;
}
}
}
}
}
else
{
lean_object* v___x_4777_; lean_object* v___x_4779_; 
lean_dec(v_a_4747_);
lean_dec(v_snd_4745_);
v___x_4777_ = lean_box(0);
if (v_isShared_4750_ == 0)
{
lean_ctor_set(v___x_4749_, 0, v___x_4777_);
v___x_4779_ = v___x_4749_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v___x_4777_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
}
}
}
}
else
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4789_; 
lean_dec(v_snd_4745_);
v_a_4782_ = lean_ctor_get(v___x_4746_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4784_ = v___x_4746_;
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4746_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4787_; 
if (v_isShared_4785_ == 0)
{
v___x_4787_ = v___x_4784_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4782_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
}
else
{
lean_object* v___x_4790_; lean_object* v___x_4792_; 
lean_dec(v_a_4740_);
v___x_4790_ = lean_box(0);
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 0, v___x_4790_);
v___x_4792_ = v___x_4742_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___x_4790_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
else
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4802_; 
v_a_4795_ = lean_ctor_get(v___x_4739_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4797_ = v___x_4739_;
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4739_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD___lam__0___boxed(lean_object* v_r_u2081_4803_, lean_object* v_r_u2082_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_){
_start:
{
lean_object* v_res_4816_; 
v_res_4816_ = l_Lean_Meta_Grind_propagateBVGetLsbD___lam__0(v_r_u2081_4803_, v_r_u2082_4804_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_);
lean_dec(v___y_4814_);
lean_dec_ref(v___y_4813_);
lean_dec(v___y_4812_);
lean_dec_ref(v___y_4811_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
lean_dec(v___y_4808_);
lean_dec_ref(v___y_4807_);
lean_dec(v___y_4806_);
lean_dec(v___y_4805_);
lean_dec_ref(v_r_u2082_4804_);
return v_res_4816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD(lean_object* v_e_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_){
_start:
{
lean_object* v___x_4834_; lean_object* v___x_4835_; uint8_t v___x_4836_; 
v___x_4834_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetLsbD___closed__1));
v___x_4835_ = lean_unsigned_to_nat(3u);
v___x_4836_ = l_Lean_Expr_isAppOfArity(v_e_4822_, v___x_4834_, v___x_4835_);
if (v___x_4836_ == 0)
{
lean_object* v___x_4837_; lean_object* v___x_4838_; 
lean_dec_ref(v_e_4822_);
v___x_4837_ = lean_box(0);
v___x_4838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4838_, 0, v___x_4837_);
return v___x_4838_;
}
else
{
lean_object* v___f_4839_; lean_object* v___x_4840_; 
v___f_4839_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetLsbD___closed__2));
v___x_4840_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4822_, v___f_4839_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_);
return v___x_4840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetLsbD___boxed(lean_object* v_e_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_){
_start:
{
lean_object* v_res_4853_; 
v_res_4853_ = l_Lean_Meta_Grind_propagateBVGetLsbD(v_e_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_, v_a_4851_);
lean_dec(v_a_4851_);
lean_dec_ref(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec_ref(v_a_4848_);
lean_dec(v_a_4847_);
lean_dec_ref(v_a_4846_);
lean_dec(v_a_4845_);
lean_dec_ref(v_a_4844_);
lean_dec(v_a_4843_);
lean_dec(v_a_4842_);
return v_res_4853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetLsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetLsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1075602488____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; 
v___x_4855_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetLsbD___closed__1));
v___x_4856_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVGetLsbD___boxed), 12, 0);
v___x_4857_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4855_, v___x_4856_);
return v___x_4857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetLsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetLsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1075602488____hygCtx___hyg_8____boxed(lean_object* v_a_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetLsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetLsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1075602488____hygCtx___hyg_8_();
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD___lam__0(lean_object* v_r_u2081_4860_, lean_object* v_r_u2082_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_){
_start:
{
lean_object* v___x_4873_; 
v___x_4873_ = l_Lean_Meta_getBitVecValue_x3f(v_r_u2081_4860_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4935_; 
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4876_ = v___x_4873_;
v_isShared_4877_ = v_isSharedCheck_4935_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4873_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4935_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
if (lean_obj_tag(v_a_4874_) == 1)
{
lean_object* v_val_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4930_; 
lean_del_object(v___x_4876_);
v_val_4878_ = lean_ctor_get(v_a_4874_, 0);
v_isSharedCheck_4930_ = !lean_is_exclusive(v_a_4874_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4880_ = v_a_4874_;
v_isShared_4881_ = v_isSharedCheck_4930_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_val_4878_);
lean_dec(v_a_4874_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4930_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v_fst_4882_; lean_object* v_snd_4883_; lean_object* v___x_4884_; 
v_fst_4882_ = lean_ctor_get(v_val_4878_, 0);
lean_inc(v_fst_4882_);
v_snd_4883_ = lean_ctor_get(v_val_4878_, 1);
lean_inc(v_snd_4883_);
lean_dec(v_val_4878_);
v___x_4884_ = l_Lean_Meta_getNatValue_x3f(v_r_u2082_4861_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
if (lean_obj_tag(v___x_4884_) == 0)
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4921_; 
v_a_4885_ = lean_ctor_get(v___x_4884_, 0);
v_isSharedCheck_4921_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4921_ == 0)
{
v___x_4887_ = v___x_4884_;
v_isShared_4888_ = v_isSharedCheck_4921_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4884_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4921_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
uint8_t v___y_4890_; 
if (lean_obj_tag(v_a_4885_) == 1)
{
lean_object* v_val_4911_; uint8_t v___x_4912_; 
lean_del_object(v___x_4887_);
v_val_4911_ = lean_ctor_get(v_a_4885_, 0);
lean_inc(v_val_4911_);
lean_dec_ref_known(v_a_4885_, 1);
v___x_4912_ = lean_nat_dec_lt(v_val_4911_, v_fst_4882_);
if (v___x_4912_ == 0)
{
lean_dec(v_val_4911_);
lean_dec(v_snd_4883_);
lean_dec(v_fst_4882_);
v___y_4890_ = v___x_4912_;
goto v___jp_4889_;
}
else
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; uint8_t v___x_4916_; 
v___x_4913_ = lean_unsigned_to_nat(1u);
v___x_4914_ = lean_nat_sub(v_fst_4882_, v___x_4913_);
lean_dec(v_fst_4882_);
v___x_4915_ = lean_nat_sub(v___x_4914_, v_val_4911_);
lean_dec(v_val_4911_);
lean_dec(v___x_4914_);
v___x_4916_ = l_Nat_testBit(v_snd_4883_, v___x_4915_);
lean_dec(v___x_4915_);
lean_dec(v_snd_4883_);
v___y_4890_ = v___x_4916_;
goto v___jp_4889_;
}
}
else
{
lean_object* v___x_4917_; lean_object* v___x_4919_; 
lean_dec(v_a_4885_);
lean_dec(v_snd_4883_);
lean_dec(v_fst_4882_);
lean_del_object(v___x_4880_);
v___x_4917_ = lean_box(0);
if (v_isShared_4888_ == 0)
{
lean_ctor_set(v___x_4887_, 0, v___x_4917_);
v___x_4919_ = v___x_4887_;
goto v_reusejp_4918_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v___x_4917_);
v___x_4919_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4918_;
}
v_reusejp_4918_:
{
return v___x_4919_;
}
}
v___jp_4889_:
{
lean_object* v___x_4891_; 
v___x_4891_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v___y_4890_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
if (lean_obj_tag(v___x_4891_) == 0)
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4902_; 
v_a_4892_ = lean_ctor_get(v___x_4891_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4894_ = v___x_4891_;
v_isShared_4895_ = v_isSharedCheck_4902_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4891_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4902_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4881_ == 0)
{
lean_ctor_set(v___x_4880_, 0, v_a_4892_);
v___x_4897_ = v___x_4880_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_a_4892_);
v___x_4897_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
lean_object* v___x_4899_; 
if (v_isShared_4895_ == 0)
{
lean_ctor_set(v___x_4894_, 0, v___x_4897_);
v___x_4899_ = v___x_4894_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v___x_4897_);
v___x_4899_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
return v___x_4899_;
}
}
}
}
else
{
lean_object* v_a_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4910_; 
lean_del_object(v___x_4880_);
v_a_4903_ = lean_ctor_get(v___x_4891_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4905_ = v___x_4891_;
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_a_4903_);
lean_dec(v___x_4891_);
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
}
}
else
{
lean_object* v_a_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4929_; 
lean_dec(v_snd_4883_);
lean_dec(v_fst_4882_);
lean_del_object(v___x_4880_);
v_a_4922_ = lean_ctor_get(v___x_4884_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4924_ = v___x_4884_;
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_a_4922_);
lean_dec(v___x_4884_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4927_; 
if (v_isShared_4925_ == 0)
{
v___x_4927_ = v___x_4924_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v_a_4922_);
v___x_4927_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
return v___x_4927_;
}
}
}
}
}
else
{
lean_object* v___x_4931_; lean_object* v___x_4933_; 
lean_dec(v_a_4874_);
v___x_4931_ = lean_box(0);
if (v_isShared_4877_ == 0)
{
lean_ctor_set(v___x_4876_, 0, v___x_4931_);
v___x_4933_ = v___x_4876_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v___x_4931_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
}
else
{
lean_object* v_a_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4943_; 
v_a_4936_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4938_ = v___x_4873_;
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_a_4936_);
lean_dec(v___x_4873_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4943_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
lean_object* v___x_4941_; 
if (v_isShared_4939_ == 0)
{
v___x_4941_ = v___x_4938_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_a_4936_);
v___x_4941_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4940_;
}
v_reusejp_4940_:
{
return v___x_4941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD___lam__0___boxed(lean_object* v_r_u2081_4944_, lean_object* v_r_u2082_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_){
_start:
{
lean_object* v_res_4957_; 
v_res_4957_ = l_Lean_Meta_Grind_propagateBVGetMsbD___lam__0(v_r_u2081_4944_, v_r_u2082_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
lean_dec(v___y_4955_);
lean_dec_ref(v___y_4954_);
lean_dec(v___y_4953_);
lean_dec_ref(v___y_4952_);
lean_dec(v___y_4951_);
lean_dec_ref(v___y_4950_);
lean_dec(v___y_4949_);
lean_dec_ref(v___y_4948_);
lean_dec(v___y_4947_);
lean_dec(v___y_4946_);
lean_dec_ref(v_r_u2082_4945_);
return v_res_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD(lean_object* v_e_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_, lean_object* v_a_4969_, lean_object* v_a_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_){
_start:
{
lean_object* v___x_4975_; lean_object* v___x_4976_; uint8_t v___x_4977_; 
v___x_4975_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetMsbD___closed__1));
v___x_4976_ = lean_unsigned_to_nat(3u);
v___x_4977_ = l_Lean_Expr_isAppOfArity(v_e_4963_, v___x_4975_, v___x_4976_);
if (v___x_4977_ == 0)
{
lean_object* v___x_4978_; lean_object* v___x_4979_; 
lean_dec_ref(v_e_4963_);
v___x_4978_ = lean_box(0);
v___x_4979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4978_);
return v___x_4979_;
}
else
{
lean_object* v___f_4980_; lean_object* v___x_4981_; 
v___f_4980_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetMsbD___closed__2));
v___x_4981_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_binOp(v_e_4963_, v___f_4980_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_, v_a_4973_);
return v___x_4981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetMsbD___boxed(lean_object* v_e_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_){
_start:
{
lean_object* v_res_4994_; 
v_res_4994_ = l_Lean_Meta_Grind_propagateBVGetMsbD(v_e_4982_, v_a_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_);
lean_dec(v_a_4992_);
lean_dec_ref(v_a_4991_);
lean_dec(v_a_4990_);
lean_dec_ref(v_a_4989_);
lean_dec(v_a_4988_);
lean_dec_ref(v_a_4987_);
lean_dec(v_a_4986_);
lean_dec_ref(v_a_4985_);
lean_dec(v_a_4984_);
lean_dec(v_a_4983_);
return v_res_4994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetMsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetMsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1507361668____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; 
v___x_4996_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetMsbD___closed__1));
v___x_4997_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVGetMsbD___boxed), 12, 0);
v___x_4998_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_4996_, v___x_4997_);
return v___x_4998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetMsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetMsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1507361668____hygCtx___hyg_8____boxed(lean_object* v_a_4999_){
_start:
{
lean_object* v_res_5000_; 
v_res_5000_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetMsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetMsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1507361668____hygCtx___hyg_8_();
return v_res_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetElem(lean_object* v_e_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_){
_start:
{
lean_object* v___x_5033_; uint8_t v___x_5034_; 
lean_inc_ref(v_e_5018_);
v___x_5033_ = l_Lean_Expr_cleanupAnnotations(v_e_5018_);
v___x_5034_ = l_Lean_Expr_isApp(v___x_5033_);
if (v___x_5034_ == 0)
{
lean_dec_ref(v___x_5033_);
lean_dec_ref(v_e_5018_);
goto v___jp_5030_;
}
else
{
lean_object* v_arg_5035_; lean_object* v___x_5036_; uint8_t v___x_5037_; 
v_arg_5035_ = lean_ctor_get(v___x_5033_, 1);
lean_inc_ref(v_arg_5035_);
v___x_5036_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5033_);
v___x_5037_ = l_Lean_Expr_isApp(v___x_5036_);
if (v___x_5037_ == 0)
{
lean_dec_ref(v___x_5036_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
goto v___jp_5030_;
}
else
{
lean_object* v_arg_5038_; lean_object* v___x_5039_; uint8_t v___x_5040_; 
v_arg_5038_ = lean_ctor_get(v___x_5036_, 1);
lean_inc_ref(v_arg_5038_);
v___x_5039_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5036_);
v___x_5040_ = l_Lean_Expr_isApp(v___x_5039_);
if (v___x_5040_ == 0)
{
lean_dec_ref(v___x_5039_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
goto v___jp_5030_;
}
else
{
lean_object* v_arg_5041_; lean_object* v___x_5042_; uint8_t v___x_5043_; 
v_arg_5041_ = lean_ctor_get(v___x_5039_, 1);
lean_inc_ref(v_arg_5041_);
v___x_5042_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5039_);
v___x_5043_ = l_Lean_Expr_isApp(v___x_5042_);
if (v___x_5043_ == 0)
{
lean_dec_ref(v___x_5042_);
lean_dec_ref(v_arg_5041_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
goto v___jp_5030_;
}
else
{
lean_object* v_arg_5044_; lean_object* v___x_5045_; uint8_t v___x_5046_; 
v_arg_5044_ = lean_ctor_get(v___x_5042_, 1);
lean_inc_ref(v_arg_5044_);
v___x_5045_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5042_);
v___x_5046_ = l_Lean_Expr_isApp(v___x_5045_);
if (v___x_5046_ == 0)
{
lean_dec_ref(v___x_5045_);
lean_dec_ref(v_arg_5044_);
lean_dec_ref(v_arg_5041_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
goto v___jp_5030_;
}
else
{
lean_object* v_arg_5047_; lean_object* v___x_5048_; uint8_t v___x_5049_; 
v_arg_5047_ = lean_ctor_get(v___x_5045_, 1);
lean_inc_ref(v_arg_5047_);
v___x_5048_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5045_);
v___x_5049_ = l_Lean_Expr_isApp(v___x_5048_);
if (v___x_5049_ == 0)
{
lean_dec_ref(v___x_5048_);
lean_dec_ref(v_arg_5047_);
lean_dec_ref(v_arg_5044_);
lean_dec_ref(v_arg_5041_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
goto v___jp_5030_;
}
else
{
lean_object* v_arg_5050_; lean_object* v___x_5051_; uint8_t v___x_5052_; 
v_arg_5050_ = lean_ctor_get(v___x_5048_, 1);
lean_inc_ref(v_arg_5050_);
v___x_5051_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5048_);
v___x_5052_ = l_Lean_Expr_isApp(v___x_5051_);
if (v___x_5052_ == 0)
{
lean_dec_ref(v___x_5051_);
lean_dec_ref(v_arg_5050_);
lean_dec_ref(v_arg_5047_);
lean_dec_ref(v_arg_5044_);
lean_dec_ref(v_arg_5041_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
goto v___jp_5030_;
}
else
{
lean_object* v_arg_5053_; lean_object* v___x_5054_; uint8_t v___x_5055_; 
v_arg_5053_ = lean_ctor_get(v___x_5051_, 1);
lean_inc_ref(v_arg_5053_);
v___x_5054_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5051_);
v___x_5055_ = l_Lean_Expr_isApp(v___x_5054_);
if (v___x_5055_ == 0)
{
lean_dec_ref(v___x_5054_);
lean_dec_ref(v_arg_5053_);
lean_dec_ref(v_arg_5050_);
lean_dec_ref(v_arg_5047_);
lean_dec_ref(v_arg_5044_);
lean_dec_ref(v_arg_5041_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
goto v___jp_5030_;
}
else
{
lean_object* v_arg_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; uint8_t v___x_5059_; 
v_arg_5056_ = lean_ctor_get(v___x_5054_, 1);
lean_inc_ref(v_arg_5056_);
v___x_5057_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5054_);
v___x_5058_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetElem___closed__2));
v___x_5059_ = l_Lean_Expr_isConstOf(v___x_5057_, v___x_5058_);
if (v___x_5059_ == 0)
{
lean_dec_ref(v___x_5057_);
lean_dec_ref(v_arg_5056_);
lean_dec_ref(v_arg_5053_);
lean_dec_ref(v_arg_5050_);
lean_dec_ref(v_arg_5047_);
lean_dec_ref(v_arg_5044_);
lean_dec_ref(v_arg_5041_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
goto v___jp_5030_;
}
else
{
lean_object* v___x_5060_; uint8_t v___x_5061_; 
v___x_5060_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetElem___closed__4));
v___x_5061_ = l_Lean_Expr_isAppOf(v_arg_5044_, v___x_5060_);
if (v___x_5061_ == 0)
{
lean_object* v___x_5062_; lean_object* v___x_5063_; 
lean_dec_ref(v___x_5057_);
lean_dec_ref(v_arg_5056_);
lean_dec_ref(v_arg_5053_);
lean_dec_ref(v_arg_5050_);
lean_dec_ref(v_arg_5047_);
lean_dec_ref(v_arg_5044_);
lean_dec_ref(v_arg_5041_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
v___x_5062_ = lean_box(0);
v___x_5063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5063_, 0, v___x_5062_);
return v___x_5063_;
}
else
{
lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5064_ = lean_st_ref_get(v_a_5019_);
lean_inc_ref(v_arg_5038_);
v___x_5065_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_5064_, v_arg_5038_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_);
lean_dec(v___x_5064_);
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_object* v_a_5066_; lean_object* v___x_5067_; 
v_a_5066_ = lean_ctor_get(v___x_5065_, 0);
lean_inc(v_a_5066_);
lean_dec_ref_known(v___x_5065_, 1);
v___x_5067_ = l_Lean_Meta_getNatValue_x3f(v_a_5066_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_);
if (lean_obj_tag(v___x_5067_) == 0)
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5163_; 
v_a_5068_ = lean_ctor_get(v___x_5067_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5067_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5070_ = v___x_5067_;
v_isShared_5071_ = v_isSharedCheck_5163_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_5067_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5163_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
if (lean_obj_tag(v_a_5068_) == 1)
{
lean_object* v_val_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; 
lean_del_object(v___x_5070_);
v_val_5072_ = lean_ctor_get(v_a_5068_, 0);
lean_inc(v_val_5072_);
lean_dec_ref_known(v_a_5068_, 1);
v___x_5073_ = lean_st_ref_get(v_a_5019_);
lean_inc_ref(v_arg_5041_);
v___x_5074_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_5073_, v_arg_5041_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_);
lean_dec(v___x_5073_);
if (lean_obj_tag(v___x_5074_) == 0)
{
lean_object* v_a_5075_; lean_object* v___x_5076_; 
v_a_5075_ = lean_ctor_get(v___x_5074_, 0);
lean_inc_n(v_a_5075_, 2);
lean_dec_ref_known(v___x_5074_, 1);
v___x_5076_ = l_Lean_Meta_getBitVecValue_x3f(v_a_5075_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_);
if (lean_obj_tag(v___x_5076_) == 0)
{
lean_object* v_a_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5142_; 
v_a_5077_ = lean_ctor_get(v___x_5076_, 0);
v_isSharedCheck_5142_ = !lean_is_exclusive(v___x_5076_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_5079_ = v___x_5076_;
v_isShared_5080_ = v_isSharedCheck_5142_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_a_5077_);
lean_dec(v___x_5076_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5142_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
if (lean_obj_tag(v_a_5077_) == 1)
{
lean_object* v_val_5081_; lean_object* v_fst_5082_; lean_object* v_snd_5083_; uint8_t v___x_5084_; 
v_val_5081_ = lean_ctor_get(v_a_5077_, 0);
lean_inc(v_val_5081_);
lean_dec_ref_known(v_a_5077_, 1);
v_fst_5082_ = lean_ctor_get(v_val_5081_, 0);
lean_inc(v_fst_5082_);
v_snd_5083_ = lean_ctor_get(v_val_5081_, 1);
lean_inc(v_snd_5083_);
lean_dec(v_val_5081_);
v___x_5084_ = lean_nat_dec_lt(v_val_5072_, v_fst_5082_);
lean_dec(v_fst_5082_);
if (v___x_5084_ == 0)
{
lean_object* v___x_5085_; lean_object* v___x_5087_; 
lean_dec(v_snd_5083_);
lean_dec(v_a_5075_);
lean_dec(v_val_5072_);
lean_dec(v_a_5066_);
lean_dec_ref(v___x_5057_);
lean_dec_ref(v_arg_5056_);
lean_dec_ref(v_arg_5053_);
lean_dec_ref(v_arg_5050_);
lean_dec_ref(v_arg_5047_);
lean_dec_ref(v_arg_5044_);
lean_dec_ref(v_arg_5041_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
v___x_5085_ = lean_box(0);
if (v_isShared_5080_ == 0)
{
lean_ctor_set(v___x_5079_, 0, v___x_5085_);
v___x_5087_ = v___x_5079_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v___x_5085_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
}
}
else
{
uint8_t v___x_5089_; lean_object* v___x_5090_; 
lean_del_object(v___x_5079_);
v___x_5089_ = l_Nat_testBit(v_snd_5083_, v_val_5072_);
lean_dec(v_val_5072_);
lean_dec(v_snd_5083_);
v___x_5090_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_mkBoolLit___redArg(v___x_5089_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_);
if (lean_obj_tag(v___x_5090_) == 0)
{
lean_object* v_a_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; 
v_a_5091_ = lean_ctor_get(v___x_5090_, 0);
lean_inc_n(v_a_5091_, 2);
lean_dec_ref_known(v___x_5090_, 1);
v___x_5092_ = lean_unsigned_to_nat(0u);
v___x_5093_ = lean_box(0);
lean_inc(v_a_5028_);
lean_inc_ref(v_a_5027_);
lean_inc(v_a_5026_);
lean_inc_ref(v_a_5025_);
lean_inc(v_a_5024_);
lean_inc_ref(v_a_5023_);
lean_inc(v_a_5022_);
lean_inc_ref(v_a_5021_);
lean_inc(v_a_5020_);
lean_inc(v_a_5019_);
v___x_5094_ = lean_grind_internalize(v_a_5091_, v___x_5092_, v___x_5093_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_);
if (lean_obj_tag(v___x_5094_) == 0)
{
lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; 
lean_dec_ref_known(v___x_5094_, 1);
lean_inc_n(v_a_5066_, 2);
lean_inc_n(v_a_5075_, 2);
lean_inc_ref(v_arg_5047_);
v___x_5095_ = l_Lean_mkAppB(v_arg_5047_, v_a_5075_, v_a_5066_);
v___x_5096_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11, &l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_unaryOp___closed__11);
lean_inc_n(v_a_5091_, 2);
lean_inc_ref(v_arg_5050_);
v___x_5097_ = l_Lean_mkAppB(v___x_5096_, v_arg_5050_, v_a_5091_);
v___x_5098_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetElem___closed__6));
v___x_5099_ = l_Lean_Expr_constLevels_x21(v___x_5057_);
lean_dec_ref(v___x_5057_);
v___x_5100_ = l_Lean_mkConst(v___x_5098_, v___x_5099_);
lean_inc_ref(v_arg_5041_);
v___x_5101_ = l_Lean_mkApp6(v___x_5100_, v_arg_5056_, v_arg_5053_, v_arg_5050_, v_arg_5047_, v_arg_5044_, v_arg_5041_);
lean_inc_ref(v_arg_5038_);
v___x_5102_ = l_Lean_mkApp5(v___x_5101_, v_a_5075_, v_arg_5038_, v_a_5066_, v_arg_5035_, v_a_5091_);
lean_inc(v_a_5028_);
lean_inc_ref(v_a_5027_);
lean_inc(v_a_5026_);
lean_inc_ref(v_a_5025_);
lean_inc(v_a_5024_);
lean_inc_ref(v_a_5023_);
lean_inc(v_a_5022_);
lean_inc_ref(v_a_5021_);
lean_inc(v_a_5020_);
lean_inc(v_a_5019_);
v___x_5103_ = lean_grind_mk_eq_proof(v_arg_5041_, v_a_5075_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_);
if (lean_obj_tag(v___x_5103_) == 0)
{
lean_object* v_a_5104_; lean_object* v___x_5105_; 
v_a_5104_ = lean_ctor_get(v___x_5103_, 0);
lean_inc(v_a_5104_);
lean_dec_ref_known(v___x_5103_, 1);
lean_inc(v_a_5028_);
lean_inc_ref(v_a_5027_);
lean_inc(v_a_5026_);
lean_inc_ref(v_a_5025_);
lean_inc(v_a_5024_);
lean_inc_ref(v_a_5023_);
lean_inc(v_a_5022_);
lean_inc_ref(v_a_5021_);
lean_inc(v_a_5020_);
lean_inc(v_a_5019_);
v___x_5105_ = lean_grind_mk_eq_proof(v_arg_5038_, v_a_5066_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_);
if (lean_obj_tag(v___x_5105_) == 0)
{
lean_object* v_a_5106_; lean_object* v___x_5107_; uint8_t v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; uint8_t v___x_5112_; lean_object* v___x_5113_; 
v_a_5106_ = lean_ctor_get(v___x_5105_, 0);
lean_inc(v_a_5106_);
lean_dec_ref_known(v___x_5105_, 1);
v___x_5107_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetElem___closed__8));
v___x_5108_ = 0;
v___x_5109_ = l_Lean_Expr_headBeta(v___x_5095_);
v___x_5110_ = l_Lean_mkLambda(v___x_5107_, v___x_5108_, v___x_5109_, v___x_5097_);
v___x_5111_ = l_Lean_mkApp3(v___x_5102_, v_a_5104_, v_a_5106_, v___x_5110_);
v___x_5112_ = 0;
v___x_5113_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_5018_, v_a_5091_, v___x_5111_, v___x_5112_, v_a_5019_, v_a_5021_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_);
return v___x_5113_;
}
else
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5121_; 
lean_dec(v_a_5104_);
lean_dec_ref(v___x_5102_);
lean_dec_ref(v___x_5097_);
lean_dec_ref(v___x_5095_);
lean_dec(v_a_5091_);
lean_dec_ref(v_e_5018_);
v_a_5114_ = lean_ctor_get(v___x_5105_, 0);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5105_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5116_ = v___x_5105_;
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5105_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v___x_5119_; 
if (v_isShared_5117_ == 0)
{
v___x_5119_ = v___x_5116_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5120_, 0, v_a_5114_);
v___x_5119_ = v_reuseFailAlloc_5120_;
goto v_reusejp_5118_;
}
v_reusejp_5118_:
{
return v___x_5119_;
}
}
}
}
else
{
lean_object* v_a_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5129_; 
lean_dec_ref(v___x_5102_);
lean_dec_ref(v___x_5097_);
lean_dec_ref(v___x_5095_);
lean_dec(v_a_5091_);
lean_dec(v_a_5066_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_e_5018_);
v_a_5122_ = lean_ctor_get(v___x_5103_, 0);
v_isSharedCheck_5129_ = !lean_is_exclusive(v___x_5103_);
if (v_isSharedCheck_5129_ == 0)
{
v___x_5124_ = v___x_5103_;
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_a_5122_);
lean_dec(v___x_5103_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5129_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v___x_5127_; 
if (v_isShared_5125_ == 0)
{
v___x_5127_ = v___x_5124_;
goto v_reusejp_5126_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v_a_5122_);
v___x_5127_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5126_;
}
v_reusejp_5126_:
{
return v___x_5127_;
}
}
}
}
else
{
lean_dec(v_a_5091_);
lean_dec(v_a_5075_);
lean_dec(v_a_5066_);
lean_dec_ref(v___x_5057_);
lean_dec_ref(v_arg_5056_);
lean_dec_ref(v_arg_5053_);
lean_dec_ref(v_arg_5050_);
lean_dec_ref(v_arg_5047_);
lean_dec_ref(v_arg_5044_);
lean_dec_ref(v_arg_5041_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
return v___x_5094_;
}
}
else
{
lean_object* v_a_5130_; lean_object* v___x_5132_; uint8_t v_isShared_5133_; uint8_t v_isSharedCheck_5137_; 
lean_dec(v_a_5075_);
lean_dec(v_a_5066_);
lean_dec_ref(v___x_5057_);
lean_dec_ref(v_arg_5056_);
lean_dec_ref(v_arg_5053_);
lean_dec_ref(v_arg_5050_);
lean_dec_ref(v_arg_5047_);
lean_dec_ref(v_arg_5044_);
lean_dec_ref(v_arg_5041_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
v_a_5130_ = lean_ctor_get(v___x_5090_, 0);
v_isSharedCheck_5137_ = !lean_is_exclusive(v___x_5090_);
if (v_isSharedCheck_5137_ == 0)
{
v___x_5132_ = v___x_5090_;
v_isShared_5133_ = v_isSharedCheck_5137_;
goto v_resetjp_5131_;
}
else
{
lean_inc(v_a_5130_);
lean_dec(v___x_5090_);
v___x_5132_ = lean_box(0);
v_isShared_5133_ = v_isSharedCheck_5137_;
goto v_resetjp_5131_;
}
v_resetjp_5131_:
{
lean_object* v___x_5135_; 
if (v_isShared_5133_ == 0)
{
v___x_5135_ = v___x_5132_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v_a_5130_);
v___x_5135_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
return v___x_5135_;
}
}
}
}
}
else
{
lean_object* v___x_5138_; lean_object* v___x_5140_; 
lean_dec(v_a_5077_);
lean_dec(v_a_5075_);
lean_dec(v_val_5072_);
lean_dec(v_a_5066_);
lean_dec_ref(v___x_5057_);
lean_dec_ref(v_arg_5056_);
lean_dec_ref(v_arg_5053_);
lean_dec_ref(v_arg_5050_);
lean_dec_ref(v_arg_5047_);
lean_dec_ref(v_arg_5044_);
lean_dec_ref(v_arg_5041_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
v___x_5138_ = lean_box(0);
if (v_isShared_5080_ == 0)
{
lean_ctor_set(v___x_5079_, 0, v___x_5138_);
v___x_5140_ = v___x_5079_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5141_; 
v_reuseFailAlloc_5141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5141_, 0, v___x_5138_);
v___x_5140_ = v_reuseFailAlloc_5141_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
return v___x_5140_;
}
}
}
}
else
{
lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5150_; 
lean_dec(v_a_5075_);
lean_dec(v_val_5072_);
lean_dec(v_a_5066_);
lean_dec_ref(v___x_5057_);
lean_dec_ref(v_arg_5056_);
lean_dec_ref(v_arg_5053_);
lean_dec_ref(v_arg_5050_);
lean_dec_ref(v_arg_5047_);
lean_dec_ref(v_arg_5044_);
lean_dec_ref(v_arg_5041_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
v_a_5143_ = lean_ctor_get(v___x_5076_, 0);
v_isSharedCheck_5150_ = !lean_is_exclusive(v___x_5076_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_5145_ = v___x_5076_;
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_dec(v___x_5076_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5150_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5148_; 
if (v_isShared_5146_ == 0)
{
v___x_5148_ = v___x_5145_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
v___x_5148_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
return v___x_5148_;
}
}
}
}
else
{
lean_object* v_a_5151_; lean_object* v___x_5153_; uint8_t v_isShared_5154_; uint8_t v_isSharedCheck_5158_; 
lean_dec(v_val_5072_);
lean_dec(v_a_5066_);
lean_dec_ref(v___x_5057_);
lean_dec_ref(v_arg_5056_);
lean_dec_ref(v_arg_5053_);
lean_dec_ref(v_arg_5050_);
lean_dec_ref(v_arg_5047_);
lean_dec_ref(v_arg_5044_);
lean_dec_ref(v_arg_5041_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
v_a_5151_ = lean_ctor_get(v___x_5074_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v___x_5074_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5153_ = v___x_5074_;
v_isShared_5154_ = v_isSharedCheck_5158_;
goto v_resetjp_5152_;
}
else
{
lean_inc(v_a_5151_);
lean_dec(v___x_5074_);
v___x_5153_ = lean_box(0);
v_isShared_5154_ = v_isSharedCheck_5158_;
goto v_resetjp_5152_;
}
v_resetjp_5152_:
{
lean_object* v___x_5156_; 
if (v_isShared_5154_ == 0)
{
v___x_5156_ = v___x_5153_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_a_5151_);
v___x_5156_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
return v___x_5156_;
}
}
}
}
else
{
lean_object* v___x_5159_; lean_object* v___x_5161_; 
lean_dec(v_a_5068_);
lean_dec(v_a_5066_);
lean_dec_ref(v___x_5057_);
lean_dec_ref(v_arg_5056_);
lean_dec_ref(v_arg_5053_);
lean_dec_ref(v_arg_5050_);
lean_dec_ref(v_arg_5047_);
lean_dec_ref(v_arg_5044_);
lean_dec_ref(v_arg_5041_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
v___x_5159_ = lean_box(0);
if (v_isShared_5071_ == 0)
{
lean_ctor_set(v___x_5070_, 0, v___x_5159_);
v___x_5161_ = v___x_5070_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v___x_5159_);
v___x_5161_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
return v___x_5161_;
}
}
}
}
else
{
lean_object* v_a_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5171_; 
lean_dec(v_a_5066_);
lean_dec_ref(v___x_5057_);
lean_dec_ref(v_arg_5056_);
lean_dec_ref(v_arg_5053_);
lean_dec_ref(v_arg_5050_);
lean_dec_ref(v_arg_5047_);
lean_dec_ref(v_arg_5044_);
lean_dec_ref(v_arg_5041_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
v_a_5164_ = lean_ctor_get(v___x_5067_, 0);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5067_);
if (v_isSharedCheck_5171_ == 0)
{
v___x_5166_ = v___x_5067_;
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_a_5164_);
lean_dec(v___x_5067_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v___x_5169_; 
if (v_isShared_5167_ == 0)
{
v___x_5169_ = v___x_5166_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_a_5164_);
v___x_5169_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
return v___x_5169_;
}
}
}
}
else
{
lean_object* v_a_5172_; lean_object* v___x_5174_; uint8_t v_isShared_5175_; uint8_t v_isSharedCheck_5179_; 
lean_dec_ref(v___x_5057_);
lean_dec_ref(v_arg_5056_);
lean_dec_ref(v_arg_5053_);
lean_dec_ref(v_arg_5050_);
lean_dec_ref(v_arg_5047_);
lean_dec_ref(v_arg_5044_);
lean_dec_ref(v_arg_5041_);
lean_dec_ref(v_arg_5038_);
lean_dec_ref(v_arg_5035_);
lean_dec_ref(v_e_5018_);
v_a_5172_ = lean_ctor_get(v___x_5065_, 0);
v_isSharedCheck_5179_ = !lean_is_exclusive(v___x_5065_);
if (v_isSharedCheck_5179_ == 0)
{
v___x_5174_ = v___x_5065_;
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
else
{
lean_inc(v_a_5172_);
lean_dec(v___x_5065_);
v___x_5174_ = lean_box(0);
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
v_resetjp_5173_:
{
lean_object* v___x_5177_; 
if (v_isShared_5175_ == 0)
{
v___x_5177_ = v___x_5174_;
goto v_reusejp_5176_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_a_5172_);
v___x_5177_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5176_;
}
v_reusejp_5176_:
{
return v___x_5177_;
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
v___jp_5030_:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; 
v___x_5031_ = lean_box(0);
v___x_5032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5032_, 0, v___x_5031_);
return v___x_5032_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateBVGetElem___boxed(lean_object* v_e_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l_Lean_Meta_Grind_propagateBVGetElem(v_e_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_);
lean_dec(v_a_5190_);
lean_dec_ref(v_a_5189_);
lean_dec(v_a_5188_);
lean_dec_ref(v_a_5187_);
lean_dec(v_a_5186_);
lean_dec_ref(v_a_5185_);
lean_dec(v_a_5184_);
lean_dec_ref(v_a_5183_);
lean_dec(v_a_5182_);
lean_dec(v_a_5181_);
return v_res_5192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetElem___regBuiltin_Lean_Meta_Grind_propagateBVGetElem_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2454187461____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; 
v___x_5194_ = ((lean_object*)(l_Lean_Meta_Grind_propagateBVGetElem___closed__2));
v___x_5195_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateBVGetElem___boxed), 12, 0);
v___x_5196_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_5194_, v___x_5195_);
return v___x_5196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetElem___regBuiltin_Lean_Meta_Grind_propagateBVGetElem_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2454187461____hygCtx___hyg_8____boxed(lean_object* v_a_5197_){
_start:
{
lean_object* v_res_5198_; 
v_res_5198_ = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetElem___regBuiltin_Lean_Meta_Grind_propagateBVGetElem_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2454187461____hygCtx___hyg_8_();
return v_res_5198_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_ToExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_BitVec(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVNot___regBuiltin_Lean_Meta_Grind_propagateBVNot_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_524020944____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVClz___regBuiltin_Lean_Meta_Grind_propagateBVClz_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3163129259____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVCpop___regBuiltin_Lean_Meta_Grind_propagateBVCpop_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4094280043____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVMsb___regBuiltin_Lean_Meta_Grind_propagateBVMsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1379739246____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToNat___regBuiltin_Lean_Meta_Grind_propagateBVToNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1265925494____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVToInt___regBuiltin_Lean_Meta_Grind_propagateBVToInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2998338308____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfNat___regBuiltin_Lean_Meta_Grind_propagateBVOfNat_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1693823724____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOfInt___regBuiltin_Lean_Meta_Grind_propagateBVOfInt_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_16048587____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSetWidth___regBuiltin_Lean_Meta_Grind_propagateBVSetWidth_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_860079827____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSignExtend___regBuiltin_Lean_Meta_Grind_propagateBVSignExtend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3709470554____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb_x27___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_x27_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4241407876____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVExtractLsb___regBuiltin_Lean_Meta_Grind_propagateBVExtractLsb_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3429100332____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVReplicate___regBuiltin_Lean_Meta_Grind_propagateBVReplicate_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3327375609____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAnd___regBuiltin_Lean_Meta_Grind_propagateBVAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_317501673____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVOr___regBuiltin_Lean_Meta_Grind_propagateBVOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4272827602____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVXor___regBuiltin_Lean_Meta_Grind_propagateBVXor_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1120302969____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVAppend___regBuiltin_Lean_Meta_Grind_propagateBVAppend_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_4057925374____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3262547096____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVUShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVUShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1878785357____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVSShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVSShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_3342532823____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateLeft___regBuiltin_Lean_Meta_Grind_propagateBVRotateLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1541346404____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVRotateRight___regBuiltin_Lean_Meta_Grind_propagateBVRotateRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2456321972____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftLeft___regBuiltin_Lean_Meta_Grind_propagateBVHShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2458924947____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVHShiftRight___regBuiltin_Lean_Meta_Grind_propagateBVHShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1131064821____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetLsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetLsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1075602488____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetMsbD___regBuiltin_Lean_Meta_Grind_propagateBVGetMsbD_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_1507361668____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_BitVec_0__Lean_Meta_Grind_propagateBVGetElem___regBuiltin_Lean_Meta_Grind_propagateBVGetElem_declare__1_00___x40_Lean_Meta_Tactic_Grind_BitVec_2454187461____hygCtx___hyg_8_();
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
