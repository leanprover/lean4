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
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLitValueModulus_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Int8"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int16"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int32"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__4_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int64"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__6_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__7_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___boxed(lean_object*);
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
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__1));
v___x_15_ = l_Lean_Expr_isConstOf(v_00_u03b1_13_, v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__3));
v___x_17_ = l_Lean_Expr_isConstOf(v_00_u03b1_13_, v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_18_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__5));
v___x_19_ = l_Lean_Expr_isConstOf(v_00_u03b1_13_, v___x_18_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_20_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___closed__7));
v___x_21_ = l_Lean_Expr_isConstOf(v_00_u03b1_13_, v___x_20_);
return v___x_21_;
}
else
{
return v___x_19_;
}
}
else
{
return v___x_17_;
}
}
else
{
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType___boxed(lean_object* v_00_u03b1_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType(v_00_u03b1_22_);
lean_dec_ref(v_00_u03b1_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f_spec__0(lean_object* v_a_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Rat_ofInt(v_a_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f_spec__1(lean_object* v_a_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_nat_to_int(v_a_27_);
return v___x_28_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_unsigned_to_nat(2u);
v___x_30_ = lean_nat_to_int(v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg(lean_object* v_e_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v___y_54_; lean_object* v___y_59_; lean_object* v___y_60_; lean_object* v___y_61_; lean_object* v_00_u03b1_69_; lean_object* v_k_70_; uint8_t v_neg_71_; lean_object* v___y_72_; lean_object* v___y_73_; lean_object* v___y_74_; lean_object* v___y_75_; lean_object* v___x_118_; 
v___x_118_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_41_, v_a_43_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_a_119_);
lean_dec_ref_known(v___x_118_, 1);
v___x_120_ = l_Lean_Expr_cleanupAnnotations(v_a_119_);
v___x_121_ = l_Lean_Expr_isApp(v___x_120_);
if (v___x_121_ == 0)
{
lean_dec_ref(v___x_120_);
goto v___jp_50_;
}
else
{
lean_object* v_arg_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_arg_122_ = lean_ctor_get(v___x_120_, 1);
lean_inc_ref(v_arg_122_);
v___x_123_ = l_Lean_Expr_appFnCleanup___redArg(v___x_120_);
v___x_124_ = l_Lean_Expr_isApp(v___x_123_);
if (v___x_124_ == 0)
{
lean_dec_ref(v___x_123_);
lean_dec_ref(v_arg_122_);
goto v___jp_50_;
}
else
{
lean_object* v_arg_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_arg_125_ = lean_ctor_get(v___x_123_, 1);
lean_inc_ref(v_arg_125_);
v___x_126_ = l_Lean_Expr_appFnCleanup___redArg(v___x_123_);
v___x_127_ = l_Lean_Expr_isApp(v___x_126_);
if (v___x_127_ == 0)
{
lean_dec_ref(v___x_126_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_arg_122_);
goto v___jp_50_;
}
else
{
lean_object* v_arg_128_; lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v_arg_128_ = lean_ctor_get(v___x_126_, 1);
lean_inc_ref(v_arg_128_);
v___x_129_ = l_Lean_Expr_appFnCleanup___redArg(v___x_126_);
v___x_130_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__3));
v___x_131_ = l_Lean_Expr_isConstOf(v___x_129_, v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; uint8_t v___x_133_; 
lean_dec_ref(v_arg_122_);
v___x_132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__6));
v___x_133_ = l_Lean_Expr_isConstOf(v___x_129_, v___x_132_);
lean_dec_ref(v___x_129_);
if (v___x_133_ == 0)
{
lean_dec_ref(v_arg_128_);
lean_dec_ref(v_arg_125_);
goto v___jp_50_;
}
else
{
v_00_u03b1_69_ = v_arg_128_;
v_k_70_ = v_arg_125_;
v_neg_71_ = v___x_131_;
v___y_72_ = v_a_42_;
v___y_73_ = v_a_43_;
v___y_74_ = v_a_44_;
v___y_75_ = v_a_45_;
goto v___jp_68_;
}
}
else
{
lean_object* v___x_134_; uint8_t v___x_135_; 
lean_dec_ref(v___x_129_);
lean_dec_ref(v_arg_125_);
v___x_134_ = l_Lean_Expr_cleanupAnnotations(v_arg_122_);
v___x_135_ = l_Lean_Expr_isApp(v___x_134_);
if (v___x_135_ == 0)
{
lean_dec_ref(v___x_134_);
lean_dec_ref(v_arg_128_);
goto v___jp_47_;
}
else
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = l_Lean_Expr_appFnCleanup___redArg(v___x_134_);
v___x_137_ = l_Lean_Expr_isApp(v___x_136_);
if (v___x_137_ == 0)
{
lean_dec_ref(v___x_136_);
lean_dec_ref(v_arg_128_);
goto v___jp_47_;
}
else
{
lean_object* v_arg_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v_arg_138_ = lean_ctor_get(v___x_136_, 1);
lean_inc_ref(v_arg_138_);
v___x_139_ = l_Lean_Expr_appFnCleanup___redArg(v___x_136_);
v___x_140_ = l_Lean_Expr_isApp(v___x_139_);
if (v___x_140_ == 0)
{
lean_dec_ref(v___x_139_);
lean_dec_ref(v_arg_138_);
lean_dec_ref(v_arg_128_);
goto v___jp_47_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_141_ = l_Lean_Expr_appFnCleanup___redArg(v___x_139_);
v___x_142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__6));
v___x_143_ = l_Lean_Expr_isConstOf(v___x_141_, v___x_142_);
lean_dec_ref(v___x_141_);
if (v___x_143_ == 0)
{
lean_dec_ref(v_arg_138_);
lean_dec_ref(v_arg_128_);
goto v___jp_47_;
}
else
{
v_00_u03b1_69_ = v_arg_128_;
v_k_70_ = v_arg_138_;
v_neg_71_ = v___x_143_;
v___y_72_ = v_a_42_;
v___y_73_ = v_a_43_;
v___y_74_ = v_a_44_;
v___y_75_ = v_a_45_;
goto v___jp_68_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
v_a_144_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_118_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_118_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
v___jp_47_:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_box(0);
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
v___jp_50_:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_box(0);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
v___jp_53_:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = l_Rat_ofInt(v___y_54_);
v___x_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
v___jp_58_:
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = lean_int_emod(v___y_61_, v___y_59_);
lean_dec(v___y_61_);
v___x_63_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isSignedType(v___y_60_);
lean_dec_ref(v___y_60_);
if (v___x_63_ == 0)
{
lean_dec(v___y_59_);
v___y_54_ = v___x_62_;
goto v___jp_53_;
}
else
{
lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_64_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___closed__0);
v___x_65_ = lean_int_ediv(v___y_59_, v___x_64_);
v___x_66_ = lean_int_dec_le(v___x_65_, v___x_62_);
lean_dec(v___x_65_);
if (v___x_66_ == 0)
{
lean_dec(v___y_59_);
v___y_54_ = v___x_62_;
goto v___jp_53_;
}
else
{
lean_object* v___x_67_; 
v___x_67_ = lean_int_sub(v___x_62_, v___y_59_);
lean_dec(v___y_59_);
lean_dec(v___x_62_);
v___y_54_ = v___x_67_;
goto v___jp_53_;
}
}
}
v___jp_68_:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Meta_getNatValue_x3f(v_k_70_, v___y_72_, v___y_73_, v___y_74_, v___y_75_);
lean_dec_ref(v_k_70_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_109_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_109_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_109_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_109_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
if (lean_obj_tag(v_a_77_) == 1)
{
lean_object* v_val_81_; lean_object* v___x_82_; 
lean_del_object(v___x_79_);
v_val_81_ = lean_ctor_get(v_a_77_, 0);
lean_inc(v_val_81_);
lean_dec_ref_known(v_a_77_, 1);
lean_inc_ref(v_00_u03b1_69_);
v___x_82_ = l_Lean_Meta_getLitValueModulus_x3f(v_00_u03b1_69_, v___y_72_, v___y_73_, v___y_74_, v___y_75_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_96_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_96_ == 0)
{
v___x_85_ = v___x_82_;
v_isShared_86_ = v_isSharedCheck_96_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_82_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_96_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
if (lean_obj_tag(v_a_83_) == 1)
{
lean_object* v_val_87_; lean_object* v___x_88_; 
lean_del_object(v___x_85_);
v_val_87_ = lean_ctor_get(v_a_83_, 0);
lean_inc(v_val_87_);
lean_dec_ref_known(v_a_83_, 1);
v___x_88_ = lean_nat_to_int(v_val_87_);
if (v_neg_71_ == 0)
{
lean_object* v___x_89_; 
v___x_89_ = lean_nat_to_int(v_val_81_);
v___y_59_ = v___x_88_;
v___y_60_ = v_00_u03b1_69_;
v___y_61_ = v___x_89_;
goto v___jp_58_;
}
else
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_nat_to_int(v_val_81_);
v___x_91_ = lean_int_neg(v___x_90_);
lean_dec(v___x_90_);
v___y_59_ = v___x_88_;
v___y_60_ = v_00_u03b1_69_;
v___y_61_ = v___x_91_;
goto v___jp_58_;
}
}
else
{
lean_object* v___x_92_; lean_object* v___x_94_; 
lean_dec(v_a_83_);
lean_dec(v_val_81_);
lean_dec_ref(v_00_u03b1_69_);
v___x_92_ = lean_box(0);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_92_);
v___x_94_ = v___x_85_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
else
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
lean_dec(v_val_81_);
lean_dec_ref(v_00_u03b1_69_);
v_a_97_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v___x_82_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_82_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_97_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
else
{
lean_object* v___x_105_; lean_object* v___x_107_; 
lean_dec(v_a_77_);
lean_dec_ref(v_00_u03b1_69_);
v___x_105_ = lean_box(0);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_105_);
v___x_107_ = v___x_79_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
lean_dec_ref(v_00_u03b1_69_);
v_a_110_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_76_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_76_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg___boxed(lean_object* v_e_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg(v_e_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f(lean_object* v_e_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg(v_e_159_, v_a_166_, v_a_167_, v_a_168_, v_a_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___boxed(lean_object* v_e_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f(v_e_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec(v_a_173_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg(lean_object* v_as_x27_196_, lean_object* v_b_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
if (lean_obj_tag(v_as_x27_196_) == 0)
{
lean_object* v___x_204_; 
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v_b_197_);
return v___x_204_;
}
else
{
lean_object* v_head_205_; lean_object* v_tail_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
lean_dec_ref(v_b_197_);
v_head_205_ = lean_ctor_get(v_as_x27_196_, 0);
v_tail_206_ = lean_ctor_get(v_as_x27_196_, 1);
v___x_207_ = lean_box(0);
v___x_208_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__0));
lean_inc(v_head_205_);
v___x_209_ = l_Lean_Expr_cleanupAnnotations(v_head_205_);
v___x_210_ = l_Lean_Expr_isApp(v___x_209_);
if (v___x_210_ == 0)
{
lean_dec_ref(v___x_209_);
v_as_x27_196_ = v_tail_206_;
v_b_197_ = v___x_208_;
goto _start;
}
else
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = l_Lean_Expr_appFnCleanup___redArg(v___x_209_);
v___x_213_ = l_Lean_Expr_isApp(v___x_212_);
if (v___x_213_ == 0)
{
lean_dec_ref(v___x_212_);
v_as_x27_196_ = v_tail_206_;
v_b_197_ = v___x_208_;
goto _start;
}
else
{
lean_object* v_arg_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_arg_215_ = lean_ctor_get(v___x_212_, 1);
lean_inc_ref(v_arg_215_);
v___x_216_ = l_Lean_Expr_appFnCleanup___redArg(v___x_212_);
v___x_217_ = l_Lean_Expr_isApp(v___x_216_);
if (v___x_217_ == 0)
{
lean_dec_ref(v___x_216_);
lean_dec_ref(v_arg_215_);
v_as_x27_196_ = v_tail_206_;
v_b_197_ = v___x_208_;
goto _start;
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_219_ = l_Lean_Expr_appFnCleanup___redArg(v___x_216_);
v___x_220_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__3));
v___x_221_ = l_Lean_Expr_isConstOf(v___x_219_, v___x_220_);
lean_dec_ref(v___x_219_);
if (v___x_221_ == 0)
{
lean_dec_ref(v_arg_215_);
v_as_x27_196_ = v_tail_206_;
v_b_197_ = v___x_208_;
goto _start;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_223_ = l_Lean_Expr_cleanupAnnotations(v_arg_215_);
v___x_224_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__5));
v___x_225_ = l_Lean_Expr_isConstOf(v___x_223_, v___x_224_);
lean_dec_ref(v___x_223_);
if (v___x_225_ == 0)
{
v_as_x27_196_ = v_tail_206_;
v_b_197_ = v___x_208_;
goto _start;
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_st_ref_get(v___y_198_);
lean_inc(v_head_205_);
v___x_228_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v___x_227_, v_head_205_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___x_227_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_238_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_238_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_238_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_238_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v_a_229_);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___x_207_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_234_);
v___x_236_ = v___x_231_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
v_a_239_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_228_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_228_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___boxed(lean_object* v_as_x27_247_, lean_object* v_b_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg(v_as_x27_247_, v_b_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec(v_as_x27_247_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(lean_object* v_e_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v_val_269_; lean_object* v___x_275_; 
lean_inc_ref(v_e_256_);
v___x_275_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getEmbeddedLitValue_x3f___redArg(v_e_256_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
if (lean_obj_tag(v_a_276_) == 1)
{
lean_object* v_val_277_; 
lean_dec_ref(v_e_256_);
v_val_277_ = lean_ctor_get(v_a_276_, 0);
lean_inc(v_val_277_);
lean_dec_ref_known(v_a_276_, 1);
v_val_269_ = v_val_277_;
goto v___jp_268_;
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec(v_a_276_);
v___x_278_ = lean_st_ref_get(v_a_257_);
lean_inc_ref(v_e_256_);
v___x_279_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(v___x_278_, v_e_256_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
lean_dec(v___x_278_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_a_280_);
lean_dec_ref_known(v___x_279_, 1);
if (lean_obj_tag(v_a_280_) == 1)
{
lean_object* v_val_281_; 
lean_dec_ref(v_e_256_);
v_val_281_ = lean_ctor_get(v_a_280_, 0);
lean_inc(v_val_281_);
lean_dec_ref_known(v_a_280_, 1);
v_val_269_ = v_val_281_;
goto v___jp_268_;
}
else
{
lean_object* v___x_282_; 
lean_dec(v_a_280_);
lean_inc(v_a_266_);
lean_inc_ref(v_a_265_);
lean_inc(v_a_264_);
lean_inc_ref(v_a_263_);
lean_inc_ref(v_e_256_);
v___x_282_ = lean_infer_type(v_e_256_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_368_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_368_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_368_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_368_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = l_Lean_Int_mkType;
v___x_288_ = lean_expr_eqv(v_a_283_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; uint8_t v___x_290_; 
lean_del_object(v___x_285_);
v___x_289_ = l_Lean_Nat_mkType;
v___x_290_ = lean_expr_eqv(v_a_283_, v___x_289_);
lean_dec(v_a_283_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_st_ref_get(v_a_257_);
lean_inc_ref(v_e_256_);
v___x_292_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_291_, v_e_256_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
lean_dec(v___x_291_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_294_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_293_);
lean_dec_ref_known(v___x_292_, 1);
v___x_294_ = l_Lean_Meta_Grind_getParents___redArg(v_a_293_, v_a_257_);
lean_dec(v_a_293_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref_known(v___x_294_, 1);
v___x_296_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_295_);
lean_dec(v_a_295_);
v___x_297_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__0));
v___x_298_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(v_e_256_, v___x_296_, v___x_297_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
lean_dec(v___x_296_);
lean_dec_ref(v_e_256_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_308_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_308_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_308_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_308_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v_fst_303_; 
v_fst_303_ = lean_ctor_get(v_a_299_, 0);
lean_inc(v_fst_303_);
lean_dec(v_a_299_);
if (lean_obj_tag(v_fst_303_) == 0)
{
lean_del_object(v___x_301_);
goto v___jp_272_;
}
else
{
lean_object* v_val_304_; lean_object* v___x_306_; 
v_val_304_ = lean_ctor_get(v_fst_303_, 0);
lean_inc(v_val_304_);
lean_dec_ref_known(v_fst_303_, 1);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v_val_304_);
v___x_306_ = v___x_301_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_val_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
v_a_309_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_298_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_298_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec_ref(v_e_256_);
v_a_317_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_294_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_294_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec_ref(v_e_256_);
v_a_325_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_292_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_292_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
else
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Meta_Grind_getParents___redArg(v_e_256_, v_a_257_);
lean_dec_ref(v_e_256_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v___x_335_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_334_);
lean_dec(v_a_334_);
v___x_336_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__0));
v___x_337_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg(v___x_335_, v___x_336_, v_a_257_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
lean_dec(v___x_335_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_347_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_347_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_347_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_347_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_fst_342_; 
v_fst_342_ = lean_ctor_get(v_a_338_, 0);
lean_inc(v_fst_342_);
lean_dec(v_a_338_);
if (lean_obj_tag(v_fst_342_) == 0)
{
lean_del_object(v___x_340_);
goto v___jp_272_;
}
else
{
lean_object* v_val_343_; lean_object* v___x_345_; 
v_val_343_ = lean_ctor_get(v_fst_342_, 0);
lean_inc(v_val_343_);
lean_dec_ref_known(v_fst_342_, 1);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v_val_343_);
v___x_345_ = v___x_340_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_val_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
v_a_348_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_337_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_337_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
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
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
v_a_356_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_333_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_333_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
}
else
{
lean_object* v___x_364_; lean_object* v___x_366_; 
lean_dec(v_a_283_);
lean_dec_ref(v_e_256_);
v___x_364_ = lean_box(0);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_364_);
v___x_366_ = v___x_285_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec_ref(v_e_256_);
v_a_369_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_282_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_282_);
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
}
else
{
lean_dec_ref(v_e_256_);
return v___x_279_;
}
}
}
else
{
lean_dec_ref(v_e_256_);
return v___x_275_;
}
v___jp_268_:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_270_, 0, v_val_269_);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
v___jp_272_:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_box(0);
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(lean_object* v_e_377_, lean_object* v_as_x27_378_, lean_object* v_b_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
if (lean_obj_tag(v_as_x27_378_) == 0)
{
lean_object* v___x_391_; 
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v_b_379_);
return v___x_391_;
}
else
{
lean_object* v_head_392_; lean_object* v_tail_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
lean_dec_ref(v_b_379_);
v_head_392_ = lean_ctor_get(v_as_x27_378_, 0);
v_tail_393_ = lean_ctor_get(v_as_x27_378_, 1);
v___x_394_ = lean_box(0);
v___x_395_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg___closed__0));
lean_inc(v_head_392_);
v___x_396_ = l_Lean_Meta_Grind_Arith_Cutsat_embeddingArg_x3f(v_head_392_);
if (lean_obj_tag(v___x_396_) == 1)
{
lean_object* v_val_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_446_; 
v_val_397_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_446_ == 0)
{
v___x_399_ = v___x_396_;
v_isShared_400_ = v_isSharedCheck_446_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_val_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_446_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Meta_Grind_isEqv___redArg(v_val_397_, v_e_377_, v___y_380_);
lean_dec(v_val_397_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; uint8_t v___x_403_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref_known(v___x_401_, 1);
v___x_403_ = lean_unbox(v_a_402_);
lean_dec(v_a_402_);
if (v___x_403_ == 0)
{
lean_del_object(v___x_399_);
v_as_x27_378_ = v_tail_393_;
v_b_379_ = v___x_395_;
goto _start;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_st_ref_get(v___y_380_);
lean_inc(v_head_392_);
v___x_406_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_405_, v_head_392_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___x_405_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_408_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
v___x_408_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(v_a_407_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_421_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_421_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_421_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_421_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
if (lean_obj_tag(v_a_409_) == 1)
{
lean_object* v___x_414_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v_a_409_);
v___x_414_ = v___x_399_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_419_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___x_394_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_415_);
v___x_417_ = v___x_411_;
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
else
{
lean_del_object(v___x_411_);
lean_dec(v_a_409_);
lean_del_object(v___x_399_);
v_as_x27_378_ = v_tail_393_;
v_b_379_ = v___x_395_;
goto _start;
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_del_object(v___x_399_);
v_a_422_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_408_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_408_);
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
lean_del_object(v___x_399_);
v_a_430_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_406_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_406_);
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
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_del_object(v___x_399_);
v_a_438_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_401_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_401_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
else
{
lean_dec(v___x_396_);
v_as_x27_378_ = v_tail_393_;
v_b_379_ = v___x_395_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg___boxed(lean_object* v_e_448_, lean_object* v_as_x27_449_, lean_object* v_b_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(v_e_448_, v_as_x27_449_, v_b_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec(v___y_451_);
lean_dec(v_as_x27_449_);
lean_dec_ref(v_e_448_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f___boxed(lean_object* v_e_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(v_e_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec(v_a_464_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0(lean_object* v_e_476_, lean_object* v_as_477_, lean_object* v_as_x27_478_, lean_object* v_b_479_, lean_object* v_a_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___redArg(v_e_476_, v_as_x27_478_, v_b_479_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0___boxed(lean_object* v_e_493_, lean_object* v_as_494_, lean_object* v_as_x27_495_, lean_object* v_b_496_, lean_object* v_a_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__0(v_e_493_, v_as_494_, v_as_x27_495_, v_b_496_, v_a_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec(v___y_498_);
lean_dec(v_as_x27_495_);
lean_dec(v_as_494_);
lean_dec_ref(v_e_493_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1(lean_object* v_as_510_, lean_object* v_as_x27_511_, lean_object* v_b_512_, lean_object* v_a_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___redArg(v_as_x27_511_, v_b_512_, v___y_514_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1___boxed(lean_object* v_as_526_, lean_object* v_as_x27_527_, lean_object* v_b_528_, lean_object* v_a_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f_spec__1(v_as_526_, v_as_x27_527_, v_b_528_, v_a_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec(v___y_530_);
lean_dec(v_as_x27_527_);
lean_dec(v_as_526_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModelValue_x3f(lean_object* v_e_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(v_e_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_582_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_582_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_582_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_582_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
if (lean_obj_tag(v_a_555_) == 1)
{
lean_object* v_val_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_577_; 
v_val_559_ = lean_ctor_get(v_a_555_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v_a_555_);
if (v_isSharedCheck_577_ == 0)
{
v___x_561_ = v_a_555_;
v_isShared_562_ = v_isSharedCheck_577_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_val_559_);
lean_dec(v_a_555_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_577_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v_num_563_; lean_object* v_den_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_num_563_ = lean_ctor_get(v_val_559_, 0);
lean_inc(v_num_563_);
v_den_564_ = lean_ctor_get(v_val_559_, 1);
lean_inc(v_den_564_);
lean_dec(v_val_559_);
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = lean_nat_dec_eq(v_den_564_, v___x_565_);
lean_dec(v_den_564_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_569_; 
lean_dec(v_num_563_);
lean_del_object(v___x_561_);
v___x_567_ = lean_box(0);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_567_);
v___x_569_ = v___x_557_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
else
{
lean_object* v___x_572_; 
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v_num_563_);
v___x_572_ = v___x_561_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_num_563_);
v___x_572_ = v_reuseFailAlloc_576_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_574_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_572_);
v___x_574_ = v___x_557_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_580_; 
lean_dec(v_a_555_);
v___x_578_ = lean_box(0);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_578_);
v___x_580_ = v___x_557_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
v_a_583_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_554_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_554_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getModelValue_x3f___boxed(lean_object* v_e_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_Meta_Grind_Arith_Cutsat_getModelValue_x3f(v_e_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec(v_a_592_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg(lean_object* v_e_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_612_ = l_Lean_Meta_Grind_SolverExtension_hasTermAtRoot___redArg(v___x_611_, v_e_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg___boxed(lean_object* v_e_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg(v_e_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar(lean_object* v_e_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___redArg(v_e_621_, v_a_622_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar___boxed(lean_object* v_e_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_hasTheoryVar(v_e_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
lean_dec(v_a_636_);
lean_dec(v_a_635_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(lean_object* v_e_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_672_ = l_Lean_Expr_cleanupAnnotations(v_e_662_);
v___x_673_ = l_Lean_Expr_isApp(v___x_672_);
if (v___x_673_ == 0)
{
lean_dec_ref(v___x_672_);
goto v___jp_668_;
}
else
{
lean_object* v_arg_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v_arg_674_ = lean_ctor_get(v___x_672_, 1);
lean_inc_ref(v_arg_674_);
v___x_675_ = l_Lean_Expr_appFnCleanup___redArg(v___x_672_);
v___x_676_ = l_Lean_Expr_isApp(v___x_675_);
if (v___x_676_ == 0)
{
lean_dec_ref(v___x_675_);
lean_dec_ref(v_arg_674_);
goto v___jp_668_;
}
else
{
lean_object* v_arg_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_arg_677_ = lean_ctor_get(v___x_675_, 1);
lean_inc_ref(v_arg_677_);
v___x_678_ = l_Lean_Expr_appFnCleanup___redArg(v___x_675_);
v___x_679_ = l_Lean_Expr_isApp(v___x_678_);
if (v___x_679_ == 0)
{
lean_dec_ref(v___x_678_);
lean_dec_ref(v_arg_677_);
lean_dec_ref(v_arg_674_);
goto v___jp_668_;
}
else
{
lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = l_Lean_Expr_appFnCleanup___redArg(v___x_678_);
v___x_681_ = l_Lean_Expr_isApp(v___x_680_);
if (v___x_681_ == 0)
{
lean_dec_ref(v___x_680_);
lean_dec_ref(v_arg_677_);
lean_dec_ref(v_arg_674_);
goto v___jp_668_;
}
else
{
lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = l_Lean_Expr_appFnCleanup___redArg(v___x_680_);
v___x_683_ = l_Lean_Expr_isApp(v___x_682_);
if (v___x_683_ == 0)
{
lean_dec_ref(v___x_682_);
lean_dec_ref(v_arg_677_);
lean_dec_ref(v_arg_674_);
goto v___jp_668_;
}
else
{
lean_object* v___x_684_; uint8_t v___x_685_; lean_object* v_b_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; 
v___x_684_ = l_Lean_Expr_appFnCleanup___redArg(v___x_682_);
v___x_685_ = l_Lean_Expr_isApp(v___x_684_);
if (v___x_685_ == 0)
{
lean_dec_ref(v___x_684_);
lean_dec_ref(v_arg_677_);
lean_dec_ref(v_arg_674_);
goto v___jp_668_;
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_715_ = l_Lean_Expr_appFnCleanup___redArg(v___x_684_);
v___x_716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__2));
v___x_717_ = l_Lean_Expr_isConstOf(v___x_715_, v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__5));
v___x_719_ = l_Lean_Expr_isConstOf(v___x_715_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; uint8_t v___x_721_; lean_object* v_a_723_; 
v___x_720_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___closed__8));
v___x_721_ = l_Lean_Expr_isConstOf(v___x_715_, v___x_720_);
lean_dec_ref(v___x_715_);
if (v___x_721_ == 0)
{
lean_dec_ref(v_arg_677_);
lean_dec_ref(v_arg_674_);
goto v___jp_668_;
}
else
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Meta_saveState___redArg(v_a_664_, v_a_666_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_737_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = l_Lean_Meta_getIntValue_x3f(v_arg_677_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; 
lean_dec(v_a_736_);
lean_dec_ref(v_arg_674_);
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_737_, 1);
v_a_723_ = v_a_738_;
goto v___jp_722_;
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_770_; 
v_a_739_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_770_ == 0)
{
v___x_741_ = v___x_737_;
v_isShared_742_ = v_isSharedCheck_770_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_737_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_770_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
uint8_t v___x_743_; 
v___x_743_ = l_Lean_Exception_isInterrupt(v_a_739_);
if (v___x_743_ == 0)
{
uint8_t v___x_744_; 
lean_inc(v_a_739_);
v___x_744_ = l_Lean_Exception_isRuntime(v_a_739_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; 
lean_del_object(v___x_741_);
lean_dec(v_a_739_);
v___x_745_ = l_Lean_Meta_SavedState_restore___redArg(v_a_736_, v_a_664_, v_a_666_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v___x_746_; 
lean_dec_ref_known(v___x_745_, 1);
v___x_746_ = l_Lean_Meta_getIntValue_x3f(v_arg_674_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v_a_723_ = v_a_747_;
goto v___jp_722_;
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
v_a_748_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_746_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_746_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref(v_arg_674_);
v_a_756_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_745_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_745_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_object* v___x_765_; 
lean_dec(v_a_736_);
lean_dec_ref(v_arg_674_);
if (v_isShared_742_ == 0)
{
v___x_765_ = v___x_741_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_739_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
else
{
lean_object* v___x_768_; 
lean_dec(v_a_736_);
lean_dec_ref(v_arg_674_);
if (v_isShared_742_ == 0)
{
v___x_768_ = v___x_741_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_739_);
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
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v_arg_677_);
lean_dec_ref(v_arg_674_);
v_a_771_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_735_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_735_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
v___jp_722_:
{
if (lean_obj_tag(v_a_723_) == 0)
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_box(v___x_721_);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
else
{
lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_733_; 
v_isSharedCheck_733_ = !lean_is_exclusive(v_a_723_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v_a_723_, 0);
lean_dec(v_unused_734_);
v___x_727_ = v_a_723_;
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
else
{
lean_dec(v_a_723_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = lean_box(v___x_719_);
if (v_isShared_728_ == 0)
{
lean_ctor_set_tag(v___x_727_, 0);
lean_ctor_set(v___x_727_, 0, v___x_729_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_715_);
lean_dec_ref(v_arg_677_);
v_b_687_ = v_arg_674_;
v___y_688_ = v_a_663_;
v___y_689_ = v_a_664_;
v___y_690_ = v_a_665_;
v___y_691_ = v_a_666_;
goto v___jp_686_;
}
}
else
{
lean_dec_ref(v___x_715_);
lean_dec_ref(v_arg_677_);
v_b_687_ = v_arg_674_;
v___y_688_ = v_a_663_;
v___y_689_ = v_a_664_;
v___y_690_ = v_a_665_;
v___y_691_ = v_a_666_;
goto v___jp_686_;
}
}
v___jp_686_:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_Meta_getIntValue_x3f(v_b_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_706_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_706_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_706_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_706_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
if (lean_obj_tag(v_a_693_) == 0)
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_box(v___x_685_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
else
{
uint8_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
lean_dec_ref_known(v_a_693_, 1);
v___x_701_ = 0;
v___x_702_ = lean_box(v___x_701_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_702_);
v___x_704_ = v___x_695_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
v_a_707_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_692_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_692_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
}
}
}
}
v___jp_668_:
{
uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = 0;
v___x_670_ = lean_box(v___x_669_);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg___boxed(lean_object* v_e_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(v_e_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(lean_object* v_e_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(v_e_786_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___boxed(lean_object* v_e_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_e_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec(v_a_800_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg(lean_object* v_e_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
uint8_t v___x_833_; 
lean_inc_ref(v_e_827_);
v___x_833_ = l_Lean_Meta_Grind_Arith_isInterpretedTerm(v_e_827_);
if (v___x_833_ == 0)
{
uint8_t v___x_834_; lean_object* v_f_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_834_ = 1;
v_f_835_ = l_Lean_Expr_getAppFn(v_e_827_);
lean_dec_ref(v_e_827_);
v___x_836_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__2));
v___x_837_ = l_Lean_Expr_isConstOf(v_f_835_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__5));
v___x_839_ = l_Lean_Expr_isConstOf(v_f_835_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; uint8_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_840_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___closed__8));
v___x_841_ = l_Lean_Expr_isConstOf(v_f_835_, v___x_840_);
lean_dec_ref(v_f_835_);
v___x_842_ = lean_box(v___x_841_);
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
return v___x_843_;
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec_ref(v_f_835_);
v___x_844_ = lean_box(v___x_834_);
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec_ref(v_f_835_);
v___x_846_ = lean_box(v___x_834_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
else
{
lean_object* v___x_848_; 
v___x_848_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___redArg(v_e_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_863_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_863_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_863_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_863_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
uint8_t v___x_853_; 
v___x_853_ = lean_unbox(v_a_849_);
lean_dec(v_a_849_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_854_ = lean_box(v___x_833_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_854_);
v___x_856_ = v___x_851_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
else
{
uint8_t v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_858_ = 0;
v___x_859_ = lean_box(v___x_858_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_859_);
v___x_861_ = v___x_851_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
else
{
return v___x_848_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg___boxed(lean_object* v_e_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg(v_e_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
lean_dec(v_a_868_);
lean_dec_ref(v_a_867_);
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted(lean_object* v_e_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___redArg(v_e_871_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted___boxed(lean_object* v_e_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_isInterpreted(v_e_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_a_886_);
lean_dec(v_a_885_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment(lean_object* v_a_897_, lean_object* v_b_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(v_a_897_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_946_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_946_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_946_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_946_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
if (lean_obj_tag(v_a_911_) == 1)
{
lean_object* v_val_915_; lean_object* v___x_916_; 
lean_del_object(v___x_913_);
v_val_915_ = lean_ctor_get(v_a_911_, 0);
lean_inc(v_val_915_);
lean_dec_ref_known(v_a_911_, 1);
v___x_916_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_getAssignmentExt_x3f(v_b_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_932_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_932_ == 0)
{
v___x_919_ = v___x_916_;
v_isShared_920_ = v_isSharedCheck_932_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_916_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_932_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
if (lean_obj_tag(v_a_917_) == 1)
{
lean_object* v_val_921_; uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
v_val_921_ = lean_ctor_get(v_a_917_, 0);
lean_inc(v_val_921_);
lean_dec_ref_known(v_a_917_, 1);
v___x_922_ = l_instDecidableEqRat_decEq(v_val_915_, v_val_921_);
lean_dec(v_val_921_);
lean_dec(v_val_915_);
v___x_923_ = lean_box(v___x_922_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_923_);
v___x_925_ = v___x_919_;
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
else
{
uint8_t v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
lean_dec(v_a_917_);
lean_dec(v_val_915_);
v___x_927_ = 0;
v___x_928_ = lean_box(v___x_927_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_928_);
v___x_930_ = v___x_919_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec(v_val_915_);
v_a_933_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_916_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_916_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
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
uint8_t v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
lean_dec(v_a_911_);
lean_dec_ref(v_b_898_);
v___x_941_ = 0;
v___x_942_ = lean_box(v___x_941_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_942_);
v___x_944_ = v___x_913_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec_ref(v_b_898_);
v_a_947_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_910_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_910_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment___boxed(lean_object* v_a_955_, lean_object* v_b_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC_0__Lean_Meta_Grind_Arith_Cutsat_eqAssignment(v_a_955_, v_b_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec(v_a_957_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc(lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mbtc___closed__3));
v___x_988_ = l_Lean_Meta_Grind_mbtc(v___x_987_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc___boxed(lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Meta_Grind_Arith_Cutsat_mbtc(v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec(v_a_989_);
return v_res_1000_;
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
