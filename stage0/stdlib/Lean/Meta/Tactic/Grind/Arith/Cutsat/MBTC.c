// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.MBTC
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util import Lean.Meta.Tactic.Grind.MBTC import Lean.Meta.Tactic.Grind.Arith.ModelUtil import Lean.Meta.Tactic.Grind.Arith.Cutsat.Model
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
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isInterpretedTerm(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_Meta_Grind_getParents___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ParentSet_elems(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_hasTermAtRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mbtc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int32"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int64"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Int8"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__4_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int16"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__7_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(256) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(65536) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__4;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__14_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f_spec__1(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__3_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__3_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastInt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__4_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(116, 224, 75, 57, 255, 108, 159, 197)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModelValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModelValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dvd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(233, 16, 181, 127, 123, 63, 3, 18)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__1_value),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__2_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType(lean_object* v_00_u03b1_13_){
_start:
{
uint8_t v___y_15_; lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_20_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__5));
v___x_21_ = l_Lean_Expr_isConstOf(v_00_u03b1_13_, v___x_20_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_22_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__7));
v___x_23_ = l_Lean_Expr_isConstOf(v_00_u03b1_13_, v___x_22_);
v___y_15_ = v___x_23_;
goto v___jp_14_;
}
else
{
v___y_15_ = v___x_21_;
goto v___jp_14_;
}
v___jp_14_:
{
if (v___y_15_ == 0)
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__1));
v___x_17_ = l_Lean_Expr_isConstOf(v_00_u03b1_13_, v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_18_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__3));
v___x_19_ = l_Lean_Expr_isConstOf(v_00_u03b1_13_, v___x_18_);
return v___x_19_;
}
else
{
return v___x_17_;
}
}
else
{
return v___y_15_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___boxed(lean_object* v_00_u03b1_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType(v_00_u03b1_24_);
lean_dec_ref(v_00_u03b1_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__2(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_cstr_to_nat("4294967296");
v___x_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__3(void){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_cstr_to_nat("18446744073709551616");
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__4(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__3);
v___x_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg(lean_object* v_00_u03b1_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_00_u03b1_54_, v_a_56_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_130_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_130_ == 0)
{
v___x_75_ = v___x_72_;
v_isShared_76_ = v_isSharedCheck_130_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_72_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_130_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_82_ = l_Lean_Expr_cleanupAnnotations(v_a_73_);
v___x_83_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__3));
v___x_84_ = l_Lean_Expr_isConstOf(v___x_82_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__1));
v___x_86_ = l_Lean_Expr_isConstOf(v___x_82_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__7));
v___x_88_ = l_Lean_Expr_isConstOf(v___x_82_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__5));
v___x_90_ = l_Lean_Expr_isConstOf(v___x_82_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_91_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__6));
v___x_92_ = l_Lean_Expr_isConstOf(v___x_82_, v___x_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; uint8_t v___x_94_; 
lean_del_object(v___x_75_);
v___x_93_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__8));
v___x_94_ = l_Lean_Expr_isConstOf(v___x_82_, v___x_93_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__10));
v___x_96_ = l_Lean_Expr_isConstOf(v___x_82_, v___x_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__12));
v___x_98_ = l_Lean_Expr_isConstOf(v___x_82_, v___x_97_);
if (v___x_98_ == 0)
{
uint8_t v___x_99_; 
v___x_99_ = l_Lean_Expr_isApp(v___x_82_);
if (v___x_99_ == 0)
{
lean_dec_ref(v___x_82_);
goto v___jp_60_;
}
else
{
lean_object* v_arg_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_arg_100_ = lean_ctor_get(v___x_82_, 1);
lean_inc_ref(v_arg_100_);
v___x_101_ = l_Lean_Expr_appFnCleanup___redArg(v___x_82_);
v___x_102_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__14));
v___x_103_ = l_Lean_Expr_isConstOf(v___x_101_, v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__16));
v___x_105_ = l_Lean_Expr_isConstOf(v___x_101_, v___x_104_);
lean_dec_ref(v___x_101_);
if (v___x_105_ == 0)
{
lean_dec_ref(v_arg_100_);
goto v___jp_60_;
}
else
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_getNatValue_x3f(v_arg_100_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
lean_dec_ref(v_arg_100_);
return v___x_106_;
}
}
else
{
lean_object* v___x_107_; 
lean_dec_ref(v___x_101_);
v___x_107_ = l_Lean_Meta_getNatValue_x3f(v_arg_100_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
lean_dec_ref(v_arg_100_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_129_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_129_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_129_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_129_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
if (lean_obj_tag(v_a_108_) == 1)
{
lean_object* v_val_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_124_; 
v_val_112_ = lean_ctor_get(v_a_108_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v_a_108_);
if (v_isSharedCheck_124_ == 0)
{
v___x_114_ = v_a_108_;
v_isShared_115_ = v_isSharedCheck_124_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_val_112_);
lean_dec(v_a_108_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_124_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_116_ = lean_unsigned_to_nat(2u);
v___x_117_ = lean_nat_pow(v___x_116_, v_val_112_);
lean_dec(v_val_112_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_117_);
v___x_119_ = v___x_114_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_117_);
v___x_119_ = v_reuseFailAlloc_123_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_121_; 
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_119_);
v___x_121_ = v___x_110_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
lean_object* v___x_125_; lean_object* v___x_127_; 
lean_dec(v_a_108_);
v___x_125_ = lean_box(0);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_125_);
v___x_127_ = v___x_110_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
else
{
return v___x_107_;
}
}
}
}
else
{
lean_dec_ref(v___x_82_);
goto v___jp_63_;
}
}
else
{
lean_dec_ref(v___x_82_);
goto v___jp_66_;
}
}
else
{
lean_dec_ref(v___x_82_);
goto v___jp_69_;
}
}
else
{
lean_dec_ref(v___x_82_);
goto v___jp_77_;
}
}
else
{
lean_dec_ref(v___x_82_);
lean_del_object(v___x_75_);
goto v___jp_63_;
}
}
else
{
lean_dec_ref(v___x_82_);
lean_del_object(v___x_75_);
goto v___jp_66_;
}
}
else
{
lean_dec_ref(v___x_82_);
lean_del_object(v___x_75_);
goto v___jp_69_;
}
}
else
{
lean_dec_ref(v___x_82_);
goto v___jp_77_;
}
v___jp_77_:
{
lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_78_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__4);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 0, v___x_78_);
v___x_80_ = v___x_75_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
v_a_131_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_72_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_72_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
v___jp_60_:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_box(0);
v___x_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
return v___x_62_;
}
v___jp_63_:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__0));
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
v___jp_66_:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__1));
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
v___jp_69_:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___closed__2);
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg___boxed(lean_object* v_00_u03b1_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg(v_00_u03b1_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f(lean_object* v_00_u03b1_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg(v_00_u03b1_146_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___boxed(lean_object* v_00_u03b1_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f(v_00_u03b1_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec(v_a_160_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f_spec__0(lean_object* v_a_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Rat_ofInt(v_a_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f_spec__1(lean_object* v_a_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_nat_to_int(v_a_174_);
return v___x_175_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(2u);
v___x_177_ = lean_nat_to_int(v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg(lean_object* v_e_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___y_195_; lean_object* v___y_200_; lean_object* v___y_201_; uint8_t v___y_202_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___x_216_; 
v___x_216_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_188_, v_a_190_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_299_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_299_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_299_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_299_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_226_ = l_Lean_Expr_cleanupAnnotations(v_a_217_);
v___x_227_ = l_Lean_Expr_isApp(v___x_226_);
if (v___x_227_ == 0)
{
lean_dec_ref(v___x_226_);
goto v___jp_221_;
}
else
{
lean_object* v_arg_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v_arg_228_ = lean_ctor_get(v___x_226_, 1);
lean_inc_ref(v_arg_228_);
v___x_229_ = l_Lean_Expr_appFnCleanup___redArg(v___x_226_);
v___x_230_ = l_Lean_Expr_isApp(v___x_229_);
if (v___x_230_ == 0)
{
lean_dec_ref(v___x_229_);
lean_dec_ref(v_arg_228_);
goto v___jp_221_;
}
else
{
lean_object* v_arg_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v_arg_231_ = lean_ctor_get(v___x_229_, 1);
lean_inc_ref(v_arg_231_);
v___x_232_ = l_Lean_Expr_appFnCleanup___redArg(v___x_229_);
v___x_233_ = l_Lean_Expr_isApp(v___x_232_);
if (v___x_233_ == 0)
{
lean_dec_ref(v___x_232_);
lean_dec_ref(v_arg_231_);
lean_dec_ref(v_arg_228_);
goto v___jp_221_;
}
else
{
lean_object* v_arg_234_; lean_object* v_k_236_; uint8_t v_neg_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v_arg_234_ = lean_ctor_get(v___x_232_, 1);
lean_inc_ref(v_arg_234_);
v___x_284_ = l_Lean_Expr_appFnCleanup___redArg(v___x_232_);
v___x_285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__3));
v___x_286_ = l_Lean_Expr_isConstOf(v___x_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; uint8_t v___x_288_; 
lean_dec_ref(v_arg_228_);
v___x_287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__6));
v___x_288_ = l_Lean_Expr_isConstOf(v___x_284_, v___x_287_);
lean_dec_ref(v___x_284_);
if (v___x_288_ == 0)
{
lean_dec_ref(v_arg_234_);
lean_dec_ref(v_arg_231_);
goto v___jp_221_;
}
else
{
lean_del_object(v___x_219_);
v_k_236_ = v_arg_231_;
v_neg_237_ = v___x_286_;
v___y_238_ = v_a_189_;
v___y_239_ = v_a_190_;
v___y_240_ = v_a_191_;
v___y_241_ = v_a_192_;
goto v___jp_235_;
}
}
else
{
lean_object* v___x_289_; uint8_t v___x_290_; 
lean_dec_ref(v___x_284_);
lean_dec_ref(v_arg_231_);
lean_del_object(v___x_219_);
v___x_289_ = l_Lean_Expr_cleanupAnnotations(v_arg_228_);
v___x_290_ = l_Lean_Expr_isApp(v___x_289_);
if (v___x_290_ == 0)
{
lean_dec_ref(v___x_289_);
lean_dec_ref(v_arg_234_);
goto v___jp_213_;
}
else
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = l_Lean_Expr_appFnCleanup___redArg(v___x_289_);
v___x_292_ = l_Lean_Expr_isApp(v___x_291_);
if (v___x_292_ == 0)
{
lean_dec_ref(v___x_291_);
lean_dec_ref(v_arg_234_);
goto v___jp_213_;
}
else
{
lean_object* v_arg_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v_arg_293_ = lean_ctor_get(v___x_291_, 1);
lean_inc_ref(v_arg_293_);
v___x_294_ = l_Lean_Expr_appFnCleanup___redArg(v___x_291_);
v___x_295_ = l_Lean_Expr_isApp(v___x_294_);
if (v___x_295_ == 0)
{
lean_dec_ref(v___x_294_);
lean_dec_ref(v_arg_293_);
lean_dec_ref(v_arg_234_);
goto v___jp_213_;
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_296_ = l_Lean_Expr_appFnCleanup___redArg(v___x_294_);
v___x_297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__6));
v___x_298_ = l_Lean_Expr_isConstOf(v___x_296_, v___x_297_);
lean_dec_ref(v___x_296_);
if (v___x_298_ == 0)
{
lean_dec_ref(v_arg_293_);
lean_dec_ref(v_arg_234_);
goto v___jp_213_;
}
else
{
v_k_236_ = v_arg_293_;
v_neg_237_ = v___x_298_;
v___y_238_ = v_a_189_;
v___y_239_ = v_a_190_;
v___y_240_ = v_a_191_;
v___y_241_ = v_a_192_;
goto v___jp_235_;
}
}
}
}
}
v___jp_235_:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Meta_getNatValue_x3f(v_k_236_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec_ref(v_k_236_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_275_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_275_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_275_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_275_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
if (lean_obj_tag(v_a_243_) == 1)
{
lean_object* v_val_247_; lean_object* v___x_248_; 
lean_del_object(v___x_245_);
v_val_247_ = lean_ctor_get(v_a_243_, 0);
lean_inc(v_val_247_);
lean_dec_ref_known(v_a_243_, 1);
lean_inc_ref(v_arg_234_);
v___x_248_ = l_Lean_Meta_Grind_Arith_Cutsat_modulus_x3f___redArg(v_arg_234_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_262_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_262_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_262_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_262_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
if (lean_obj_tag(v_a_249_) == 1)
{
lean_object* v_val_253_; lean_object* v___x_254_; 
lean_del_object(v___x_251_);
v_val_253_ = lean_ctor_get(v_a_249_, 0);
lean_inc(v_val_253_);
lean_dec_ref_known(v_a_249_, 1);
v___x_254_ = lean_nat_to_int(v_val_253_);
if (v_neg_237_ == 0)
{
lean_object* v___x_255_; 
v___x_255_ = lean_nat_to_int(v_val_247_);
v___y_205_ = v_arg_234_;
v___y_206_ = v___x_254_;
v___y_207_ = v___x_255_;
goto v___jp_204_;
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_nat_to_int(v_val_247_);
v___x_257_ = lean_int_neg(v___x_256_);
lean_dec(v___x_256_);
v___y_205_ = v_arg_234_;
v___y_206_ = v___x_254_;
v___y_207_ = v___x_257_;
goto v___jp_204_;
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_260_; 
lean_dec(v_a_249_);
lean_dec(v_val_247_);
lean_dec_ref(v_arg_234_);
v___x_258_ = lean_box(0);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v___x_258_);
v___x_260_ = v___x_251_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_dec(v_val_247_);
lean_dec_ref(v_arg_234_);
v_a_263_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_248_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_248_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_object* v___x_271_; lean_object* v___x_273_; 
lean_dec(v_a_243_);
lean_dec_ref(v_arg_234_);
v___x_271_ = lean_box(0);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_271_);
v___x_273_ = v___x_245_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref(v_arg_234_);
v_a_276_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_242_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_242_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
}
}
v___jp_221_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_222_ = lean_box(0);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_222_);
v___x_224_ = v___x_219_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_a_300_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_216_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_216_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
v___jp_194_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = l_Rat_ofInt(v___y_195_);
v___x_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
v___jp_199_:
{
if (v___y_202_ == 0)
{
lean_dec(v___y_200_);
v___y_195_ = v___y_201_;
goto v___jp_194_;
}
else
{
lean_object* v___x_203_; 
v___x_203_ = lean_int_sub(v___y_201_, v___y_200_);
lean_dec(v___y_200_);
lean_dec(v___y_201_);
v___y_195_ = v___x_203_;
goto v___jp_194_;
}
}
v___jp_204_:
{
lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = lean_int_emod(v___y_207_, v___y_206_);
lean_dec(v___y_207_);
v___x_209_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType(v___y_205_);
lean_dec_ref(v___y_205_);
if (v___x_209_ == 0)
{
v___y_200_ = v___y_206_;
v___y_201_ = v___x_208_;
v___y_202_ = v___x_209_;
goto v___jp_199_;
}
else
{
lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_210_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__0);
v___x_211_ = lean_int_ediv(v___y_206_, v___x_210_);
v___x_212_ = lean_int_dec_le(v___x_211_, v___x_208_);
lean_dec(v___x_211_);
v___y_200_ = v___y_206_;
v___y_201_ = v___x_208_;
v___y_202_ = v___x_212_;
goto v___jp_199_;
}
}
v___jp_213_:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_box(0);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___boxed(lean_object* v_e_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg(v_e_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f(lean_object* v_e_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg(v_e_315_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___boxed(lean_object* v_e_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f(v_e_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec(v_a_329_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg(lean_object* v_as_x27_352_, lean_object* v_b_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
if (lean_obj_tag(v_as_x27_352_) == 0)
{
lean_object* v___x_360_; 
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v_b_353_);
return v___x_360_;
}
else
{
lean_object* v_head_361_; lean_object* v_tail_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
lean_dec_ref(v_b_353_);
v_head_361_ = lean_ctor_get(v_as_x27_352_, 0);
v_tail_362_ = lean_ctor_get(v_as_x27_352_, 1);
v___x_363_ = lean_box(0);
v___x_364_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__0));
lean_inc(v_head_361_);
v___x_365_ = l_Lean_Expr_cleanupAnnotations(v_head_361_);
v___x_366_ = l_Lean_Expr_isApp(v___x_365_);
if (v___x_366_ == 0)
{
lean_dec_ref(v___x_365_);
v_as_x27_352_ = v_tail_362_;
v_b_353_ = v___x_364_;
goto _start;
}
else
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = l_Lean_Expr_appFnCleanup___redArg(v___x_365_);
v___x_369_ = l_Lean_Expr_isApp(v___x_368_);
if (v___x_369_ == 0)
{
lean_dec_ref(v___x_368_);
v_as_x27_352_ = v_tail_362_;
v_b_353_ = v___x_364_;
goto _start;
}
else
{
lean_object* v_arg_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v_arg_371_ = lean_ctor_get(v___x_368_, 1);
lean_inc_ref(v_arg_371_);
v___x_372_ = l_Lean_Expr_appFnCleanup___redArg(v___x_368_);
v___x_373_ = l_Lean_Expr_isApp(v___x_372_);
if (v___x_373_ == 0)
{
lean_dec_ref(v___x_372_);
lean_dec_ref(v_arg_371_);
v_as_x27_352_ = v_tail_362_;
v_b_353_ = v___x_364_;
goto _start;
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_375_ = l_Lean_Expr_appFnCleanup___redArg(v___x_372_);
v___x_376_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__3));
v___x_377_ = l_Lean_Expr_isConstOf(v___x_375_, v___x_376_);
lean_dec_ref(v___x_375_);
if (v___x_377_ == 0)
{
lean_dec_ref(v_arg_371_);
v_as_x27_352_ = v_tail_362_;
v_b_353_ = v___x_364_;
goto _start;
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_379_ = l_Lean_Expr_cleanupAnnotations(v_arg_371_);
v___x_380_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__5));
v___x_381_ = l_Lean_Expr_isConstOf(v___x_379_, v___x_380_);
lean_dec_ref(v___x_379_);
if (v___x_381_ == 0)
{
v_as_x27_352_ = v_tail_362_;
v_b_353_ = v___x_364_;
goto _start;
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_st_ref_get(v___y_354_);
lean_inc(v_head_361_);
v___x_384_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v___x_383_, v_head_361_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___x_383_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_394_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_394_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_394_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_394_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_389_, 0, v_a_385_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___x_363_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_390_);
v___x_392_ = v___x_387_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
v_a_395_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_384_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_384_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___boxed(lean_object* v_as_x27_403_, lean_object* v_b_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg(v_as_x27_403_, v_b_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec(v_as_x27_403_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(lean_object* v_e_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_val_425_; lean_object* v___x_431_; 
lean_inc_ref(v_e_412_);
v___x_431_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg(v_e_412_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_a_432_);
lean_dec_ref_known(v___x_431_, 1);
if (lean_obj_tag(v_a_432_) == 1)
{
lean_object* v_val_433_; 
lean_dec_ref(v_e_412_);
v_val_433_ = lean_ctor_get(v_a_432_, 0);
lean_inc(v_val_433_);
lean_dec_ref_known(v_a_432_, 1);
v_val_425_ = v_val_433_;
goto v___jp_424_;
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec(v_a_432_);
v___x_434_ = lean_st_ref_get(v_a_413_);
lean_inc_ref(v_e_412_);
v___x_435_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v___x_434_, v_e_412_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
lean_dec(v___x_434_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
if (lean_obj_tag(v_a_436_) == 1)
{
lean_object* v_val_437_; 
lean_dec_ref(v_e_412_);
v_val_437_ = lean_ctor_get(v_a_436_, 0);
lean_inc(v_val_437_);
lean_dec_ref_known(v_a_436_, 1);
v_val_425_ = v_val_437_;
goto v___jp_424_;
}
else
{
lean_object* v___x_438_; 
lean_dec(v_a_436_);
lean_inc(v_a_422_);
lean_inc_ref(v_a_421_);
lean_inc(v_a_420_);
lean_inc_ref(v_a_419_);
lean_inc_ref(v_e_412_);
v___x_438_ = lean_infer_type(v_e_412_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_524_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_524_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_524_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_524_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_443_ = l_Lean_Int_mkType;
v___x_444_ = lean_expr_eqv(v_a_439_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; uint8_t v___x_446_; 
lean_del_object(v___x_441_);
v___x_445_ = l_Lean_Nat_mkType;
v___x_446_ = lean_expr_eqv(v_a_439_, v___x_445_);
lean_dec(v_a_439_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_st_ref_get(v_a_413_);
lean_inc_ref(v_e_412_);
v___x_448_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_447_, v_e_412_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
lean_dec(v___x_447_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_450_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref_known(v___x_448_, 1);
v___x_450_ = l_Lean_Meta_Grind_getParents___redArg(v_a_449_, v_a_413_);
lean_dec(v_a_449_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_a_451_);
lean_dec_ref_known(v___x_450_, 1);
v___x_452_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_451_);
lean_dec(v_a_451_);
v___x_453_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__0));
v___x_454_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(v_e_412_, v___x_452_, v___x_453_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
lean_dec(v___x_452_);
lean_dec_ref(v_e_412_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_464_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_464_ == 0)
{
v___x_457_ = v___x_454_;
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v_fst_459_; 
v_fst_459_ = lean_ctor_get(v_a_455_, 0);
lean_inc(v_fst_459_);
lean_dec(v_a_455_);
if (lean_obj_tag(v_fst_459_) == 0)
{
lean_del_object(v___x_457_);
goto v___jp_428_;
}
else
{
lean_object* v_val_460_; lean_object* v___x_462_; 
v_val_460_ = lean_ctor_get(v_fst_459_, 0);
lean_inc(v_val_460_);
lean_dec_ref_known(v_fst_459_, 1);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v_val_460_);
v___x_462_ = v___x_457_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_val_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
v_a_465_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_454_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_454_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec_ref(v_e_412_);
v_a_473_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_450_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_450_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
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
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec_ref(v_e_412_);
v_a_481_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_448_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_448_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
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
lean_object* v___x_489_; 
v___x_489_ = l_Lean_Meta_Grind_getParents___redArg(v_e_412_, v_a_413_);
lean_dec_ref(v_e_412_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_489_, 1);
v___x_491_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_490_);
lean_dec(v_a_490_);
v___x_492_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__0));
v___x_493_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg(v___x_491_, v___x_492_, v_a_413_, v_a_419_, v_a_420_, v_a_421_, v_a_422_);
lean_dec(v___x_491_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_503_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_503_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_503_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_503_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v_fst_498_; 
v_fst_498_ = lean_ctor_get(v_a_494_, 0);
lean_inc(v_fst_498_);
lean_dec(v_a_494_);
if (lean_obj_tag(v_fst_498_) == 0)
{
lean_del_object(v___x_496_);
goto v___jp_428_;
}
else
{
lean_object* v_val_499_; lean_object* v___x_501_; 
v_val_499_ = lean_ctor_get(v_fst_498_, 0);
lean_inc(v_val_499_);
lean_dec_ref_known(v_fst_498_, 1);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v_val_499_);
v___x_501_ = v___x_496_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_val_499_);
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
v_a_504_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_493_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_493_);
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
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
v_a_512_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_489_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_489_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_522_; 
lean_dec(v_a_439_);
lean_dec_ref(v_e_412_);
v___x_520_ = lean_box(0);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_520_);
v___x_522_ = v___x_441_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec_ref(v_e_412_);
v_a_525_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_438_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_438_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_412_);
return v___x_435_;
}
}
}
else
{
lean_dec_ref(v_e_412_);
return v___x_431_;
}
v___jp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_426_, 0, v_val_425_);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
return v___x_427_;
}
v___jp_428_:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_box(0);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(lean_object* v_e_533_, lean_object* v_as_x27_534_, lean_object* v_b_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
if (lean_obj_tag(v_as_x27_534_) == 0)
{
lean_object* v___x_547_; 
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v_b_535_);
return v___x_547_;
}
else
{
lean_object* v_head_548_; lean_object* v_tail_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
lean_dec_ref(v_b_535_);
v_head_548_ = lean_ctor_get(v_as_x27_534_, 0);
v_tail_549_ = lean_ctor_get(v_as_x27_534_, 1);
v___x_550_ = lean_box(0);
v___x_551_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__0));
lean_inc(v_head_548_);
v___x_552_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_head_548_);
if (lean_obj_tag(v___x_552_) == 1)
{
lean_object* v_val_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_602_; 
v_val_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_602_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_602_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_val_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_602_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Meta_Grind_isEqv___redArg(v_val_553_, v_e_533_, v___y_536_);
lean_dec(v_val_553_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; uint8_t v___x_559_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_558_);
lean_dec_ref_known(v___x_557_, 1);
v___x_559_ = lean_unbox(v_a_558_);
lean_dec(v_a_558_);
if (v___x_559_ == 0)
{
lean_del_object(v___x_555_);
v_as_x27_534_ = v_tail_549_;
v_b_535_ = v___x_551_;
goto _start;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_st_ref_get(v___y_536_);
lean_inc(v_head_548_);
v___x_562_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_561_, v_head_548_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___x_561_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_564_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_562_, 1);
v___x_564_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(v_a_563_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_577_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_577_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_577_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_577_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
if (lean_obj_tag(v_a_565_) == 1)
{
lean_object* v___x_570_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v_a_565_);
v___x_570_ = v___x_555_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_575_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v___x_550_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_571_);
v___x_573_ = v___x_567_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
else
{
lean_del_object(v___x_567_);
lean_dec(v_a_565_);
lean_del_object(v___x_555_);
v_as_x27_534_ = v_tail_549_;
v_b_535_ = v___x_551_;
goto _start;
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_del_object(v___x_555_);
v_a_578_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_564_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_564_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_del_object(v___x_555_);
v_a_586_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_562_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_562_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_del_object(v___x_555_);
v_a_594_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_557_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_557_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
else
{
lean_dec(v___x_552_);
v_as_x27_534_ = v_tail_549_;
v_b_535_ = v___x_551_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg___boxed(lean_object* v_e_604_, lean_object* v_as_x27_605_, lean_object* v_b_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(v_e_604_, v_as_x27_605_, v_b_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec(v___y_607_);
lean_dec(v_as_x27_605_);
lean_dec_ref(v_e_604_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f___boxed(lean_object* v_e_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(v_e_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
lean_dec(v_a_629_);
lean_dec_ref(v_a_628_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec(v_a_620_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0(lean_object* v_e_632_, lean_object* v_as_633_, lean_object* v_as_x27_634_, lean_object* v_b_635_, lean_object* v_a_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(v_e_632_, v_as_x27_634_, v_b_635_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___boxed(lean_object* v_e_649_, lean_object* v_as_650_, lean_object* v_as_x27_651_, lean_object* v_b_652_, lean_object* v_a_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0(v_e_649_, v_as_650_, v_as_x27_651_, v_b_652_, v_a_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec(v___y_654_);
lean_dec(v_as_x27_651_);
lean_dec(v_as_650_);
lean_dec_ref(v_e_649_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1(lean_object* v_as_666_, lean_object* v_as_x27_667_, lean_object* v_b_668_, lean_object* v_a_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg(v_as_x27_667_, v_b_668_, v___y_670_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___boxed(lean_object* v_as_682_, lean_object* v_as_x27_683_, lean_object* v_b_684_, lean_object* v_a_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1(v_as_682_, v_as_x27_683_, v_b_684_, v_a_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec(v___y_686_);
lean_dec(v_as_x27_683_);
lean_dec(v_as_682_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModelValue_x3f(lean_object* v_e_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(v_e_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_738_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_738_ == 0)
{
v___x_713_ = v___x_710_;
v_isShared_714_ = v_isSharedCheck_738_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_710_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_738_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
if (lean_obj_tag(v_a_711_) == 1)
{
lean_object* v_val_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_733_; 
v_val_715_ = lean_ctor_get(v_a_711_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v_a_711_);
if (v_isSharedCheck_733_ == 0)
{
v___x_717_ = v_a_711_;
v_isShared_718_ = v_isSharedCheck_733_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_val_715_);
lean_dec(v_a_711_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_733_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v_num_719_; lean_object* v_den_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_num_719_ = lean_ctor_get(v_val_715_, 0);
lean_inc(v_num_719_);
v_den_720_ = lean_ctor_get(v_val_715_, 1);
lean_inc(v_den_720_);
lean_dec(v_val_715_);
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = lean_nat_dec_eq(v_den_720_, v___x_721_);
lean_dec(v_den_720_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_725_; 
lean_dec(v_num_719_);
lean_del_object(v___x_717_);
v___x_723_ = lean_box(0);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_723_);
v___x_725_ = v___x_713_;
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
else
{
lean_object* v___x_728_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v_num_719_);
v___x_728_ = v___x_717_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_num_719_);
v___x_728_ = v_reuseFailAlloc_732_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_730_; 
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_728_);
v___x_730_ = v___x_713_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
else
{
lean_object* v___x_734_; lean_object* v___x_736_; 
lean_dec(v_a_711_);
v___x_734_ = lean_box(0);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_734_);
v___x_736_ = v___x_713_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
v_a_739_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_710_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_710_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModelValue_x3f___boxed(lean_object* v_e_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Meta_Grind_Arith_Cutsat_getModelValue_x3f(v_e_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec(v_a_748_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg(lean_object* v_e_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_768_ = l_Lean_Meta_Grind_SolverExtension_hasTermAtRoot___redArg(v___x_767_, v_e_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg___boxed(lean_object* v_e_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg(v_e_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar(lean_object* v_e_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg(v_e_777_, v_a_778_, v_a_784_, v_a_785_, v_a_786_, v_a_787_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___boxed(lean_object* v_e_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar(v_e_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
lean_dec(v_a_792_);
lean_dec(v_a_791_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(lean_object* v_e_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = l_Lean_Expr_cleanupAnnotations(v_e_818_);
v___x_829_ = l_Lean_Expr_isApp(v___x_828_);
if (v___x_829_ == 0)
{
lean_dec_ref(v___x_828_);
goto v___jp_824_;
}
else
{
lean_object* v_arg_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v_arg_830_ = lean_ctor_get(v___x_828_, 1);
lean_inc_ref(v_arg_830_);
v___x_831_ = l_Lean_Expr_appFnCleanup___redArg(v___x_828_);
v___x_832_ = l_Lean_Expr_isApp(v___x_831_);
if (v___x_832_ == 0)
{
lean_dec_ref(v___x_831_);
lean_dec_ref(v_arg_830_);
goto v___jp_824_;
}
else
{
lean_object* v_arg_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_arg_833_ = lean_ctor_get(v___x_831_, 1);
lean_inc_ref(v_arg_833_);
v___x_834_ = l_Lean_Expr_appFnCleanup___redArg(v___x_831_);
v___x_835_ = l_Lean_Expr_isApp(v___x_834_);
if (v___x_835_ == 0)
{
lean_dec_ref(v___x_834_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_830_);
goto v___jp_824_;
}
else
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = l_Lean_Expr_appFnCleanup___redArg(v___x_834_);
v___x_837_ = l_Lean_Expr_isApp(v___x_836_);
if (v___x_837_ == 0)
{
lean_dec_ref(v___x_836_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_830_);
goto v___jp_824_;
}
else
{
lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = l_Lean_Expr_appFnCleanup___redArg(v___x_836_);
v___x_839_ = l_Lean_Expr_isApp(v___x_838_);
if (v___x_839_ == 0)
{
lean_dec_ref(v___x_838_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_830_);
goto v___jp_824_;
}
else
{
lean_object* v___x_840_; uint8_t v___x_841_; lean_object* v_b_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; 
v___x_840_ = l_Lean_Expr_appFnCleanup___redArg(v___x_838_);
v___x_841_ = l_Lean_Expr_isApp(v___x_840_);
if (v___x_841_ == 0)
{
lean_dec_ref(v___x_840_);
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_830_);
goto v___jp_824_;
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_871_ = l_Lean_Expr_appFnCleanup___redArg(v___x_840_);
v___x_872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2));
v___x_873_ = l_Lean_Expr_isConstOf(v___x_871_, v___x_872_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5));
v___x_875_ = l_Lean_Expr_isConstOf(v___x_871_, v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; uint8_t v___x_877_; lean_object* v___y_879_; 
v___x_876_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8));
v___x_877_ = l_Lean_Expr_isConstOf(v___x_871_, v___x_876_);
lean_dec_ref(v___x_871_);
if (v___x_877_ == 0)
{
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_830_);
goto v___jp_824_;
}
else
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_Meta_saveState___redArg(v_a_820_, v_a_822_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_903_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v___x_901_, 1);
v___x_903_ = l_Lean_Meta_getIntValue_x3f(v_arg_833_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_dec(v_a_902_);
lean_dec_ref(v_arg_830_);
v___y_879_ = v___x_903_;
goto v___jp_878_;
}
else
{
lean_object* v_a_904_; uint8_t v___y_906_; uint8_t v___x_917_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
v___x_917_ = l_Lean_Exception_isInterrupt(v_a_904_);
if (v___x_917_ == 0)
{
uint8_t v___x_918_; 
v___x_918_ = l_Lean_Exception_isRuntime(v_a_904_);
v___y_906_ = v___x_918_;
goto v___jp_905_;
}
else
{
lean_dec(v_a_904_);
v___y_906_ = v___x_917_;
goto v___jp_905_;
}
v___jp_905_:
{
if (v___y_906_ == 0)
{
lean_object* v___x_907_; 
lean_dec_ref_known(v___x_903_, 1);
v___x_907_ = l_Lean_Meta_SavedState_restore___redArg(v_a_902_, v_a_820_, v_a_822_);
lean_dec(v_a_902_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v___x_908_; 
lean_dec_ref_known(v___x_907_, 1);
v___x_908_ = l_Lean_Meta_getIntValue_x3f(v_arg_830_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
v___y_879_ = v___x_908_;
goto v___jp_878_;
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref(v_arg_830_);
v_a_909_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_907_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_907_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_dec(v_a_902_);
lean_dec_ref(v_arg_830_);
v___y_879_ = v___x_903_;
goto v___jp_878_;
}
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec_ref(v_arg_833_);
lean_dec_ref(v_arg_830_);
v_a_919_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_901_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_901_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
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
v___jp_878_:
{
if (lean_obj_tag(v___y_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_892_; 
v_a_880_ = lean_ctor_get(v___y_879_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___y_879_);
if (v_isSharedCheck_892_ == 0)
{
v___x_882_ = v___y_879_;
v_isShared_883_ = v_isSharedCheck_892_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___y_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_892_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
if (lean_obj_tag(v_a_880_) == 0)
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_box(v___x_877_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_884_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
else
{
lean_object* v___x_888_; lean_object* v___x_890_; 
lean_dec_ref_known(v_a_880_, 1);
v___x_888_ = lean_box(v___x_875_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_888_);
v___x_890_ = v___x_882_;
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
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
v_a_893_ = lean_ctor_get(v___y_879_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___y_879_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___y_879_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___y_879_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_871_);
lean_dec_ref(v_arg_833_);
v_b_843_ = v_arg_830_;
v___y_844_ = v_a_819_;
v___y_845_ = v_a_820_;
v___y_846_ = v_a_821_;
v___y_847_ = v_a_822_;
goto v___jp_842_;
}
}
else
{
lean_dec_ref(v___x_871_);
lean_dec_ref(v_arg_833_);
v_b_843_ = v_arg_830_;
v___y_844_ = v_a_819_;
v___y_845_ = v_a_820_;
v___y_846_ = v_a_821_;
v___y_847_ = v_a_822_;
goto v___jp_842_;
}
}
v___jp_842_:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_Meta_getIntValue_x3f(v_b_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_862_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_862_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_862_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_862_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
if (lean_obj_tag(v_a_849_) == 0)
{
lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_853_ = lean_box(v___x_841_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_853_);
v___x_855_ = v___x_851_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
else
{
uint8_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
lean_dec_ref_known(v_a_849_, 1);
v___x_857_ = 0;
v___x_858_ = lean_box(v___x_857_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_858_);
v___x_860_ = v___x_851_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
v_a_863_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_848_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_848_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
}
}
}
}
v___jp_824_:
{
uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = 0;
v___x_826_ = lean_box(v___x_825_);
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___boxed(lean_object* v_e_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(v_e_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(lean_object* v_e_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(v_e_934_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___boxed(lean_object* v_e_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_e_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec(v_a_948_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg(lean_object* v_e_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
uint8_t v___x_981_; 
lean_inc_ref(v_e_975_);
v___x_981_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_975_);
if (v___x_981_ == 0)
{
uint8_t v___x_982_; lean_object* v_f_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_982_ = 1;
v_f_983_ = l_Lean_Expr_getAppFn(v_e_975_);
lean_dec_ref(v_e_975_);
v___x_984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2));
v___x_985_ = l_Lean_Expr_isConstOf(v_f_983_, v___x_984_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5));
v___x_987_ = l_Lean_Expr_isConstOf(v_f_983_, v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; uint8_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_988_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8));
v___x_989_ = l_Lean_Expr_isConstOf(v_f_983_, v___x_988_);
lean_dec_ref(v_f_983_);
v___x_990_ = lean_box(v___x_989_);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; 
lean_dec_ref(v_f_983_);
v___x_992_ = lean_box(v___x_982_);
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
return v___x_993_;
}
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; 
lean_dec_ref(v_f_983_);
v___x_994_ = lean_box(v___x_982_);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
else
{
lean_object* v___x_996_; 
v___x_996_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(v_e_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1011_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1011_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1011_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
uint8_t v___x_1001_; 
v___x_1001_ = lean_unbox(v_a_997_);
lean_dec(v_a_997_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1002_ = lean_box(v___x_981_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1002_);
v___x_1004_ = v___x_999_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
else
{
uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1006_ = 0;
v___x_1007_ = lean_box(v___x_1006_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1007_);
v___x_1009_ = v___x_999_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
return v___x_996_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___boxed(lean_object* v_e_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg(v_e_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted(lean_object* v_e_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg(v_e_1019_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___boxed(lean_object* v_e_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted(v_e_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec(v_a_1033_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment(lean_object* v_a_1045_, lean_object* v_b_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(v_a_1045_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1094_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1094_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1094_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
if (lean_obj_tag(v_a_1059_) == 1)
{
lean_object* v_val_1063_; lean_object* v___x_1064_; 
lean_del_object(v___x_1061_);
v_val_1063_ = lean_ctor_get(v_a_1059_, 0);
lean_inc(v_val_1063_);
lean_dec_ref_known(v_a_1059_, 1);
v___x_1064_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(v_b_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1080_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1067_ = v___x_1064_;
v_isShared_1068_ = v_isSharedCheck_1080_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1080_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
if (lean_obj_tag(v_a_1065_) == 1)
{
lean_object* v_val_1069_; uint8_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v_val_1069_ = lean_ctor_get(v_a_1065_, 0);
lean_inc(v_val_1069_);
lean_dec_ref_known(v_a_1065_, 1);
v___x_1070_ = l_instDecidableEqRat_decEq(v_val_1063_, v_val_1069_);
lean_dec(v_val_1069_);
lean_dec(v_val_1063_);
v___x_1071_ = lean_box(v___x_1070_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1071_);
v___x_1073_ = v___x_1067_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
else
{
uint8_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; 
lean_dec(v_a_1065_);
lean_dec(v_val_1063_);
v___x_1075_ = 0;
v___x_1076_ = lean_box(v___x_1075_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1076_);
v___x_1078_ = v___x_1067_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
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
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_val_1063_);
v_a_1081_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1064_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1064_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
uint8_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
lean_dec(v_a_1059_);
lean_dec_ref(v_b_1046_);
v___x_1089_ = 0;
v___x_1090_ = lean_box(v___x_1089_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1090_);
v___x_1092_ = v___x_1061_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
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
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec_ref(v_b_1046_);
v_a_1095_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1058_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1058_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment___boxed(lean_object* v_a_1103_, lean_object* v_b_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment(v_a_1103_, v_b_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec(v_a_1105_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc(lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__3));
v___x_1136_ = l_Lean_Meta_Grind_mbtc(v___x_1135_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc___boxed(lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_Meta_Grind_Arith_Cutsat_mbtc(v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec(v_a_1137_);
return v_res_1148_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_MBTC(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(builtin);
}
#ifdef __cplusplus
}
#endif
