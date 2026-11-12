// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Lean.Meta.Tactic.Simp.Arith.Int.Simp
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_getGoalStackDepth___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_denoteExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_mkIntLE(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_mkIntDvd(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_shrink(lean_object*, lean_object*);
lean_object* l_Lean_mkIntEq(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isNatType(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isIntType(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
extern lean_object* l_instInhabitedRat;
lean_object* l_Rat_mul(lean_object*, lean_object*);
uint8_t l_Rat_instDecidableLe(lean_object*, lean_object*);
uint8_t l_Lean_Bool_toLBool(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isUnsatLe(lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Lean_Meta_isNatValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_getConst(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs_x27(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_leadCoeff(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Int_gcd(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Int_lcm(lean_object*, lean_object*);
static lean_once_cell_t l_Int_Internal_Linear_Poly_isZero___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Internal_Linear_Poly_isZero___closed__0;
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isZero(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isZero___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_isSorted_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_isSorted_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isSorted(lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isSorted___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modify_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ISize"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int64"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int32"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int16"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Int8"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__18_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__19_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__20_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__21_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__23_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isCutsatType___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isCutsatType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isCutsatType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isCutsatType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_mk_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_assert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " + "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ∣ "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "`grind` internal error, unexpected"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = " ≠ 0"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = " ≤ 0"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " = 0"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "`grind` internal error, unexpected constant polynomial"};
static const lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__0 = (const lean_object*)&l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__0_value;
static lean_once_cell_t l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1;
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(lean_object*);
static lean_once_cell_t l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0;
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Int_Internal_Linear_Poly_isZero___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isZero(lean_object* v_x_3_){
_start:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v_k_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v_k_4_ = lean_ctor_get(v_x_3_, 0);
v___x_5_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_6_ = lean_int_dec_eq(v_k_4_, v___x_5_);
return v___x_6_;
}
else
{
uint8_t v___x_7_; 
v___x_7_ = 0;
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isZero___boxed(lean_object* v_x_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l_Int_Internal_Linear_Poly_isZero(v_x_8_);
lean_dec_ref(v_x_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_isSorted_go(lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
if (lean_obj_tag(v_a_12_) == 0)
{
uint8_t v___x_13_; 
lean_dec(v_a_11_);
v___x_13_ = 1;
return v___x_13_;
}
else
{
if (lean_obj_tag(v_a_11_) == 0)
{
lean_object* v_v_14_; lean_object* v_p_15_; lean_object* v___x_16_; 
v_v_14_ = lean_ctor_get(v_a_12_, 1);
v_p_15_ = lean_ctor_get(v_a_12_, 2);
lean_inc(v_v_14_);
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v_v_14_);
v_a_11_ = v___x_16_;
v_a_12_ = v_p_15_;
goto _start;
}
else
{
lean_object* v_v_18_; lean_object* v_p_19_; lean_object* v_val_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_29_; 
v_v_18_ = lean_ctor_get(v_a_12_, 1);
v_p_19_ = lean_ctor_get(v_a_12_, 2);
v_val_20_ = lean_ctor_get(v_a_11_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v_a_11_);
if (v_isSharedCheck_29_ == 0)
{
v___x_22_ = v_a_11_;
v_isShared_23_ = v_isSharedCheck_29_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_val_20_);
lean_dec(v_a_11_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_29_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
uint8_t v___x_24_; 
v___x_24_ = lean_nat_dec_lt(v_v_18_, v_val_20_);
lean_dec(v_val_20_);
if (v___x_24_ == 0)
{
lean_del_object(v___x_22_);
return v___x_24_;
}
else
{
lean_object* v___x_26_; 
lean_inc(v_v_18_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v_v_18_);
v___x_26_ = v___x_22_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_v_18_);
v___x_26_ = v_reuseFailAlloc_28_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
v_a_11_ = v___x_26_;
v_a_12_ = v_p_19_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_isSorted_go___boxed(lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_isSorted_go(v_a_30_, v_a_31_);
lean_dec_ref(v_a_31_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isSorted(lean_object* v_p_34_){
_start:
{
lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_35_ = lean_box(0);
v___x_36_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_isSorted_go(v___x_35_, v_p_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isSorted___boxed(lean_object* v_p_37_){
_start:
{
uint8_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = l_Int_Internal_Linear_Poly_isSorted(v_p_37_);
lean_dec_ref(v_p_37_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_44_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_43_, v_a_40_, v_a_41_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg___boxed(lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_45_, v_a_46_);
lean_dec_ref(v_a_46_);
lean_dec(v_a_45_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27(lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_49_, v_a_57_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___boxed(lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec(v_a_61_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___redArg(lean_object* v_f_73_, lean_object* v_a_74_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_77_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_76_, v_f_73_, v_a_74_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___redArg___boxed(lean_object* v_f_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___redArg(v_f_78_, v_a_79_);
lean_dec(v_a_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modify_x27(lean_object* v_f_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_95_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_94_, v_f_82_, v_a_83_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___boxed(lean_object* v_f_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Meta_Grind_Arith_Cutsat_modify_x27(v_f_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
lean_dec(v_a_98_);
lean_dec(v_a_97_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg(lean_object* v_type_145_, lean_object* v_a_146_){
_start:
{
uint8_t v___x_152_; 
v___x_152_ = l_Lean_Meta_Grind_Arith_isNatType(v_type_145_);
if (v___x_152_ == 0)
{
uint8_t v___x_153_; 
v___x_153_ = l_Lean_Meta_Grind_Arith_isIntType(v_type_145_);
if (v___x_153_ == 0)
{
uint8_t v___x_154_; lean_object* v___x_155_; 
v___x_154_ = 1;
v___x_155_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_type_145_, v_a_146_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_243_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_243_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_243_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_243_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_160_ = l_Lean_Expr_cleanupAnnotations(v_a_156_);
lean_dec(v_a_156_);
v___x_161_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__1));
v___x_162_ = l_Lean_Expr_isConstOf(v___x_160_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__3));
v___x_164_ = l_Lean_Expr_isConstOf(v___x_160_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__5));
v___x_166_ = l_Lean_Expr_isConstOf(v___x_160_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__7));
v___x_168_ = l_Lean_Expr_isConstOf(v___x_160_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__9));
v___x_170_ = l_Lean_Expr_isConstOf(v___x_160_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__11));
v___x_172_ = l_Lean_Expr_isConstOf(v___x_160_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__13));
v___x_174_ = l_Lean_Expr_isConstOf(v___x_160_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__15));
v___x_176_ = l_Lean_Expr_isConstOf(v___x_160_, v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__17));
v___x_178_ = l_Lean_Expr_isConstOf(v___x_160_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__19));
v___x_180_ = l_Lean_Expr_isConstOf(v___x_160_, v___x_179_);
if (v___x_180_ == 0)
{
uint8_t v___x_181_; 
v___x_181_ = l_Lean_Expr_isApp(v___x_160_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_184_; 
lean_dec_ref(v___x_160_);
v___x_182_ = lean_box(v___x_153_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_182_);
v___x_184_ = v___x_158_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_186_ = l_Lean_Expr_appFnCleanup___redArg(v___x_160_);
lean_dec_ref(v___x_160_);
v___x_187_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__21));
v___x_188_ = l_Lean_Expr_isConstOf(v___x_186_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_189_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__23));
v___x_190_ = l_Lean_Expr_isConstOf(v___x_186_, v___x_189_);
lean_dec_ref(v___x_186_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_191_ = lean_box(v___x_153_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_191_);
v___x_193_ = v___x_158_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
else
{
lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_195_ = lean_box(v___x_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_195_);
v___x_197_ = v___x_158_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
else
{
lean_object* v___x_199_; lean_object* v___x_201_; 
lean_dec_ref(v___x_186_);
v___x_199_ = lean_box(v___x_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_199_);
v___x_201_ = v___x_158_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
else
{
lean_object* v___x_203_; lean_object* v___x_205_; 
lean_dec_ref(v___x_160_);
v___x_203_ = lean_box(v___x_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_203_);
v___x_205_ = v___x_158_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
else
{
lean_object* v___x_207_; lean_object* v___x_209_; 
lean_dec_ref(v___x_160_);
v___x_207_ = lean_box(v___x_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_207_);
v___x_209_ = v___x_158_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
else
{
lean_object* v___x_211_; lean_object* v___x_213_; 
lean_dec_ref(v___x_160_);
v___x_211_ = lean_box(v___x_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_211_);
v___x_213_ = v___x_158_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
else
{
lean_object* v___x_215_; lean_object* v___x_217_; 
lean_dec_ref(v___x_160_);
v___x_215_ = lean_box(v___x_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_215_);
v___x_217_ = v___x_158_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
else
{
lean_object* v___x_219_; lean_object* v___x_221_; 
lean_dec_ref(v___x_160_);
v___x_219_ = lean_box(v___x_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_219_);
v___x_221_ = v___x_158_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
else
{
lean_object* v___x_223_; lean_object* v___x_225_; 
lean_dec_ref(v___x_160_);
v___x_223_ = lean_box(v___x_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_223_);
v___x_225_ = v___x_158_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
else
{
lean_object* v___x_227_; lean_object* v___x_229_; 
lean_dec_ref(v___x_160_);
v___x_227_ = lean_box(v___x_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_227_);
v___x_229_ = v___x_158_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
else
{
lean_object* v___x_231_; lean_object* v___x_233_; 
lean_dec_ref(v___x_160_);
v___x_231_ = lean_box(v___x_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_231_);
v___x_233_ = v___x_158_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
else
{
lean_object* v___x_235_; lean_object* v___x_237_; 
lean_dec_ref(v___x_160_);
v___x_235_ = lean_box(v___x_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_235_);
v___x_237_ = v___x_158_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
else
{
lean_object* v___x_239_; lean_object* v___x_241_; 
lean_dec_ref(v___x_160_);
v___x_239_ = lean_box(v___x_154_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_239_);
v___x_241_ = v___x_158_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
v_a_244_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_155_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_155_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
else
{
lean_dec_ref(v_type_145_);
goto v___jp_148_;
}
}
else
{
lean_dec_ref(v_type_145_);
goto v___jp_148_;
}
v___jp_148_:
{
uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = 1;
v___x_150_ = lean_box(v___x_149_);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___boxed(lean_object* v_type_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg(v_type_252_, v_a_253_);
lean_dec(v_a_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType(lean_object* v_type_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg(v_type_256_, v_a_264_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___boxed(lean_object* v_type_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType(v_type_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_dec(v_a_270_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isCutsatType___redArg(lean_object* v_type_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_283_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_297_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_297_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_297_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_297_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
uint8_t v_lia_291_; 
v_lia_291_ = lean_ctor_get_uint8(v_a_287_, sizeof(void*)*18 + 24);
lean_dec(v_a_287_);
if (v_lia_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_294_; 
lean_dec_ref(v_type_282_);
v___x_292_ = lean_box(v_lia_291_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_292_);
v___x_294_ = v___x_289_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
else
{
lean_object* v___x_296_; 
lean_del_object(v___x_289_);
v___x_296_ = l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg(v_type_282_, v_a_284_);
return v___x_296_;
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec_ref(v_type_282_);
v_a_298_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_286_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_286_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isCutsatType___redArg___boxed(lean_object* v_type_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Meta_Grind_Arith_Cutsat_isCutsatType___redArg(v_type_306_, v_a_307_, v_a_308_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isCutsatType(lean_object* v_type_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Meta_Grind_Arith_Cutsat_isCutsatType___redArg(v_type_311_, v_a_314_, v_a_319_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isCutsatType___boxed(lean_object* v_type_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Meta_Grind_Arith_Cutsat_isCutsatType(v_type_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec(v_a_325_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg(lean_object* v_00_u03b1_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_347_ = l_Lean_Expr_cleanupAnnotations(v_00_u03b1_337_);
v___x_348_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__3));
v___x_349_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__5));
v___x_351_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__7));
v___x_353_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__9));
v___x_355_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__13));
v___x_357_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__15));
v___x_359_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__17));
v___x_361_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__19));
v___x_363_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_362_);
if (v___x_363_ == 0)
{
uint8_t v___x_364_; 
v___x_364_ = l_Lean_Expr_isApp(v___x_347_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_dec_ref(v___x_347_);
v___x_365_ = lean_box(v___x_363_);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
else
{
lean_object* v_arg_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_arg_367_ = lean_ctor_get(v___x_347_, 1);
lean_inc_ref(v_arg_367_);
v___x_368_ = l_Lean_Expr_appFnCleanup___redArg(v___x_347_);
lean_dec_ref(v___x_347_);
v___x_369_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__21));
v___x_370_ = l_Lean_Expr_isConstOf(v___x_368_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__23));
v___x_372_ = l_Lean_Expr_isConstOf(v___x_368_, v___x_371_);
lean_dec_ref(v___x_368_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_dec_ref(v_arg_367_);
v___x_373_ = lean_box(v___x_363_);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
else
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Meta_isNatValue(v_arg_367_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
lean_dec_ref(v_arg_367_);
return v___x_375_;
}
}
else
{
lean_object* v___x_376_; 
lean_dec_ref(v___x_368_);
v___x_376_ = l_Lean_Meta_isNatValue(v_arg_367_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
lean_dec_ref(v_arg_367_);
return v___x_376_;
}
}
}
else
{
lean_dec_ref(v___x_347_);
goto v___jp_343_;
}
}
else
{
lean_dec_ref(v___x_347_);
goto v___jp_343_;
}
}
else
{
lean_dec_ref(v___x_347_);
goto v___jp_343_;
}
}
else
{
lean_dec_ref(v___x_347_);
goto v___jp_343_;
}
}
else
{
lean_dec_ref(v___x_347_);
goto v___jp_343_;
}
}
else
{
lean_dec_ref(v___x_347_);
goto v___jp_343_;
}
}
else
{
lean_dec_ref(v___x_347_);
goto v___jp_343_;
}
}
else
{
lean_dec_ref(v___x_347_);
goto v___jp_343_;
}
v___jp_343_:
{
uint8_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = 1;
v___x_345_ = lean_box(v___x_344_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg___boxed(lean_object* v_00_u03b1_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg(v_00_u03b1_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec_ref(v_00_u03b1_377_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated(lean_object* v_00_u03b1_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg(v_00_u03b1_384_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___boxed(lean_object* v_00_u03b1_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated(v_00_u03b1_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
lean_dec(v_a_399_);
lean_dec(v_a_398_);
lean_dec_ref(v_00_u03b1_397_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_410_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; uint8_t v___x_415_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v___x_415_ = lean_unbox(v_a_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; 
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
v___x_416_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_410_, v_a_411_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_430_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_430_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_430_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_430_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v_conflict_x3f_421_; 
v_conflict_x3f_421_ = lean_ctor_get(v_a_417_, 18);
lean_inc(v_conflict_x3f_421_);
lean_dec(v_a_417_);
if (lean_obj_tag(v_conflict_x3f_421_) == 0)
{
lean_object* v___x_423_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v_a_414_);
v___x_423_ = v___x_419_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_414_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
else
{
uint8_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
lean_dec_ref_known(v_conflict_x3f_421_, 1);
lean_dec(v_a_414_);
v___x_425_ = 1;
v___x_426_ = lean_box(v___x_425_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_426_);
v___x_428_ = v___x_419_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
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
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
lean_dec(v_a_414_);
v_a_431_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_416_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_416_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
else
{
return v___x_413_;
}
}
else
{
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg___boxed(lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_439_, v_a_440_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_443_, v_a_451_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___boxed(lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec(v_a_455_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVar___boxed(lean_object* v_e_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_00___x40___internal___hyg_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = lean_grind_cutsat_mk_var(v_e_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_504_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_504_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v_vars_500_; lean_object* v___x_502_; 
v_vars_500_ = lean_ctor_get(v_a_496_, 0);
lean_inc_ref(v_vars_500_);
lean_dec(v_a_496_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v_vars_500_);
v___x_502_ = v___x_498_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_vars_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
v_a_505_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_495_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_495_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg___boxed(lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_513_, v_a_514_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars(lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_517_, v_a_525_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___boxed(lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars(v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec(v_a_529_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object* v_x_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = l_Lean_instInhabitedExpr;
v___x_546_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_542_, v_a_543_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_562_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_562_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_562_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_562_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v_vars_551_; lean_object* v_size_552_; uint8_t v___x_553_; 
v_vars_551_ = lean_ctor_get(v_a_547_, 0);
lean_inc_ref(v_vars_551_);
lean_dec(v_a_547_);
v_size_552_ = lean_ctor_get(v_vars_551_, 2);
v___x_553_ = lean_nat_dec_lt(v_x_541_, v_size_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_556_; 
lean_dec_ref(v_vars_551_);
v___x_554_ = l_outOfBounds___redArg(v___x_545_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_554_);
v___x_556_ = v___x_549_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
else
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = l_Lean_PersistentArray_get_x21___redArg(v___x_545_, v_vars_551_, v_x_541_);
lean_dec_ref(v_vars_551_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_558_);
v___x_560_ = v___x_549_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
v_a_563_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_546_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_546_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg___boxed(lean_object* v_x_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_571_, v_a_572_, v_a_573_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec(v_x_571_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar(lean_object* v_x_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_576_, v_a_577_, v_a_585_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___boxed(lean_object* v_x_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar(v_x_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec(v_a_590_);
lean_dec(v_x_589_);
return v_res_601_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_602_, lean_object* v_i_603_, lean_object* v_k_604_){
_start:
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = lean_array_get_size(v_keys_602_);
v___x_606_ = lean_nat_dec_lt(v_i_603_, v___x_605_);
if (v___x_606_ == 0)
{
lean_dec(v_i_603_);
return v___x_606_;
}
else
{
lean_object* v_k_x27_607_; size_t v___x_608_; size_t v___x_609_; uint8_t v___x_610_; 
v_k_x27_607_ = lean_array_fget_borrowed(v_keys_602_, v_i_603_);
v___x_608_ = lean_ptr_addr(v_k_604_);
v___x_609_ = lean_ptr_addr(v_k_x27_607_);
v___x_610_ = lean_usize_dec_eq(v___x_608_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_nat_add(v_i_603_, v___x_611_);
lean_dec(v_i_603_);
v_i_603_ = v___x_612_;
goto _start;
}
else
{
lean_dec(v_i_603_);
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_614_, lean_object* v_i_615_, lean_object* v_k_616_){
_start:
{
uint8_t v_res_617_; lean_object* v_r_618_; 
v_res_617_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_614_, v_i_615_, v_k_616_);
lean_dec_ref(v_k_616_);
lean_dec_ref(v_keys_614_);
v_r_618_ = lean_box(v_res_617_);
return v_r_618_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(lean_object* v_x_619_, size_t v_x_620_, lean_object* v_x_621_){
_start:
{
if (lean_obj_tag(v_x_619_) == 0)
{
lean_object* v_es_622_; lean_object* v___x_623_; size_t v___x_624_; size_t v___x_625_; lean_object* v_j_626_; lean_object* v___x_627_; 
v_es_622_ = lean_ctor_get(v_x_619_, 0);
v___x_623_ = lean_box(2);
v___x_624_ = ((size_t)31ULL);
v___x_625_ = lean_usize_land(v_x_620_, v___x_624_);
v_j_626_ = lean_usize_to_nat(v___x_625_);
v___x_627_ = lean_array_get_borrowed(v___x_623_, v_es_622_, v_j_626_);
lean_dec(v_j_626_);
switch(lean_obj_tag(v___x_627_))
{
case 0:
{
lean_object* v_key_628_; size_t v___x_629_; size_t v___x_630_; uint8_t v___x_631_; 
v_key_628_ = lean_ctor_get(v___x_627_, 0);
v___x_629_ = lean_ptr_addr(v_x_621_);
v___x_630_ = lean_ptr_addr(v_key_628_);
v___x_631_ = lean_usize_dec_eq(v___x_629_, v___x_630_);
return v___x_631_;
}
case 1:
{
lean_object* v_node_632_; size_t v___x_633_; size_t v___x_634_; 
v_node_632_ = lean_ctor_get(v___x_627_, 0);
v___x_633_ = ((size_t)5ULL);
v___x_634_ = lean_usize_shift_right(v_x_620_, v___x_633_);
v_x_619_ = v_node_632_;
v_x_620_ = v___x_634_;
goto _start;
}
default: 
{
uint8_t v___x_636_; 
v___x_636_ = 0;
return v___x_636_;
}
}
}
else
{
lean_object* v_ks_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_ks_637_ = lean_ctor_get(v_x_619_, 0);
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_ks_637_, v___x_638_, v_x_621_);
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___boxed(lean_object* v_x_640_, lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
size_t v_x_889__boxed_643_; uint8_t v_res_644_; lean_object* v_r_645_; 
v_x_889__boxed_643_ = lean_unbox_usize(v_x_641_);
lean_dec(v_x_641_);
v_res_644_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_640_, v_x_889__boxed_643_, v_x_642_);
lean_dec_ref(v_x_642_);
lean_dec_ref(v_x_640_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(lean_object* v_x_646_, lean_object* v_x_647_){
_start:
{
size_t v___x_648_; size_t v___x_649_; size_t v___x_650_; uint64_t v___x_651_; size_t v___x_652_; uint8_t v___x_653_; 
v___x_648_ = lean_ptr_addr(v_x_647_);
v___x_649_ = ((size_t)3ULL);
v___x_650_ = lean_usize_shift_right(v___x_648_, v___x_649_);
v___x_651_ = lean_usize_to_uint64(v___x_650_);
v___x_652_ = lean_uint64_to_usize(v___x_651_);
v___x_653_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_646_, v___x_652_, v_x_647_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg___boxed(lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
uint8_t v_res_656_; lean_object* v_r_657_; 
v_res_656_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_654_, v_x_655_);
lean_dec_ref(v_x_655_);
lean_dec_ref(v_x_654_);
v_r_657_ = lean_box(v_res_656_);
return v_r_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(lean_object* v_e_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_659_, v_a_660_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_673_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_673_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_673_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_673_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_varMap_667_; uint8_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v_varMap_667_ = lean_ctor_get(v_a_663_, 1);
lean_inc_ref(v_varMap_667_);
lean_dec(v_a_663_);
v___x_668_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_varMap_667_, v_e_658_);
lean_dec_ref(v_varMap_667_);
v___x_669_ = lean_box(v___x_668_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_669_);
v___x_671_ = v___x_665_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
v_a_674_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_662_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_662_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg___boxed(lean_object* v_e_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_682_, v_a_683_, v_a_684_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_e_682_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar(lean_object* v_e_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_687_, v_a_688_, v_a_696_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___boxed(lean_object* v_e_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar(v_e_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec(v_a_702_);
lean_dec(v_a_701_);
lean_dec_ref(v_e_700_);
return v_res_712_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(lean_object* v_00_u03b2_713_, lean_object* v_x_714_, lean_object* v_x_715_){
_start:
{
uint8_t v___x_716_; 
v___x_716_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_714_, v_x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___boxed(lean_object* v_00_u03b2_717_, lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
uint8_t v_res_720_; lean_object* v_r_721_; 
v_res_720_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(v_00_u03b2_717_, v_x_718_, v_x_719_);
lean_dec_ref(v_x_719_);
lean_dec_ref(v_x_718_);
v_r_721_ = lean_box(v_res_720_);
return v_r_721_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(lean_object* v_00_u03b2_722_, lean_object* v_x_723_, size_t v_x_724_, lean_object* v_x_725_){
_start:
{
uint8_t v___x_726_; 
v___x_726_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_723_, v_x_724_, v_x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_727_, lean_object* v_x_728_, lean_object* v_x_729_, lean_object* v_x_730_){
_start:
{
size_t v_x_1006__boxed_731_; uint8_t v_res_732_; lean_object* v_r_733_; 
v_x_1006__boxed_731_ = lean_unbox_usize(v_x_729_);
lean_dec(v_x_729_);
v_res_732_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(v_00_u03b2_727_, v_x_728_, v_x_1006__boxed_731_, v_x_730_);
lean_dec_ref(v_x_730_);
lean_dec_ref(v_x_728_);
v_r_733_ = lean_box(v_res_732_);
return v_r_733_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_734_, lean_object* v_keys_735_, lean_object* v_vals_736_, lean_object* v_heq_737_, lean_object* v_i_738_, lean_object* v_k_739_){
_start:
{
uint8_t v___x_740_; 
v___x_740_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_735_, v_i_738_, v_k_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_741_, lean_object* v_keys_742_, lean_object* v_vals_743_, lean_object* v_heq_744_, lean_object* v_i_745_, lean_object* v_k_746_){
_start:
{
uint8_t v_res_747_; lean_object* v_r_748_; 
v_res_747_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(v_00_u03b2_741_, v_keys_742_, v_vals_743_, v_heq_744_, v_i_745_, v_k_746_);
lean_dec_ref(v_k_746_);
lean_dec_ref(v_vals_743_);
lean_dec_ref(v_keys_742_);
v_r_748_ = lean_box(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(lean_object* v_e_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_749_, v_a_750_, v_a_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg___boxed(lean_object* v_e_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(v_e_754_, v_a_755_, v_a_756_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_e_754_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(lean_object* v_e_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_759_, v_a_760_, v_a_768_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___boxed(lean_object* v_e_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(v_e_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_e_772_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(lean_object* v_x_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_box(0);
v___x_790_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_786_, v_a_787_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_812_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_812_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_812_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_812_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___y_796_; lean_object* v_elimEqs_807_; lean_object* v_size_808_; uint8_t v___x_809_; 
v_elimEqs_807_ = lean_ctor_get(v_a_791_, 9);
lean_inc_ref(v_elimEqs_807_);
lean_dec(v_a_791_);
v_size_808_ = lean_ctor_get(v_elimEqs_807_, 2);
v___x_809_ = lean_nat_dec_lt(v_x_785_, v_size_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; 
lean_dec_ref(v_elimEqs_807_);
v___x_810_ = l_outOfBounds___redArg(v___x_789_);
v___y_796_ = v___x_810_;
goto v___jp_795_;
}
else
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_PersistentArray_get_x21___redArg(v___x_789_, v_elimEqs_807_, v_x_785_);
lean_dec_ref(v_elimEqs_807_);
v___y_796_ = v___x_811_;
goto v___jp_795_;
}
v___jp_795_:
{
if (lean_obj_tag(v___y_796_) == 0)
{
uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_797_ = 0;
v___x_798_ = lean_box(v___x_797_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_798_);
v___x_800_ = v___x_793_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
else
{
uint8_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
lean_dec_ref_known(v___y_796_, 1);
v___x_802_ = 1;
v___x_803_ = lean_box(v___x_802_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_803_);
v___x_805_ = v___x_793_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
v_a_813_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_790_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_790_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg___boxed(lean_object* v_x_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_821_, v_a_822_, v_a_823_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec(v_x_821_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated(lean_object* v_x_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_826_, v_a_827_, v_a_835_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___boxed(lean_object* v_x_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated(v_x_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec(v_a_840_);
lean_dec(v_x_839_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_assert___boxed(lean_object* v_c_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_00___x40___internal___hyg_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = lean_grind_cutsat_assert_eq(v_c_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(lean_object* v_x_877_, lean_object* v_s_878_){
_start:
{
lean_object* v_vars_879_; lean_object* v_varMap_880_; lean_object* v_varsHistory_881_; lean_object* v_natToIntMap_882_; lean_object* v_natDef_883_; lean_object* v_dvds_884_; lean_object* v_lowers_885_; lean_object* v_uppers_886_; lean_object* v_diseqs_887_; lean_object* v_elimEqs_888_; lean_object* v_active_889_; lean_object* v_elimStack_890_; lean_object* v_occurs_891_; lean_object* v_assignment_892_; lean_object* v_nextCnstrId_893_; uint8_t v_caseSplits_894_; lean_object* v_steps_895_; lean_object* v_penalties_896_; lean_object* v_numReorderRequests_897_; lean_object* v_conflict_x3f_898_; lean_object* v_diseqSplits_899_; lean_object* v_divMod_900_; uint8_t v_usedCommRing_901_; lean_object* v_nonlinearOccs_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_910_; 
v_vars_879_ = lean_ctor_get(v_s_878_, 0);
v_varMap_880_ = lean_ctor_get(v_s_878_, 1);
v_varsHistory_881_ = lean_ctor_get(v_s_878_, 2);
v_natToIntMap_882_ = lean_ctor_get(v_s_878_, 3);
v_natDef_883_ = lean_ctor_get(v_s_878_, 4);
v_dvds_884_ = lean_ctor_get(v_s_878_, 5);
v_lowers_885_ = lean_ctor_get(v_s_878_, 6);
v_uppers_886_ = lean_ctor_get(v_s_878_, 7);
v_diseqs_887_ = lean_ctor_get(v_s_878_, 8);
v_elimEqs_888_ = lean_ctor_get(v_s_878_, 9);
v_active_889_ = lean_ctor_get(v_s_878_, 10);
v_elimStack_890_ = lean_ctor_get(v_s_878_, 11);
v_occurs_891_ = lean_ctor_get(v_s_878_, 12);
v_assignment_892_ = lean_ctor_get(v_s_878_, 13);
v_nextCnstrId_893_ = lean_ctor_get(v_s_878_, 14);
v_caseSplits_894_ = lean_ctor_get_uint8(v_s_878_, sizeof(void*)*22);
v_steps_895_ = lean_ctor_get(v_s_878_, 15);
v_penalties_896_ = lean_ctor_get(v_s_878_, 16);
v_numReorderRequests_897_ = lean_ctor_get(v_s_878_, 17);
v_conflict_x3f_898_ = lean_ctor_get(v_s_878_, 18);
v_diseqSplits_899_ = lean_ctor_get(v_s_878_, 19);
v_divMod_900_ = lean_ctor_get(v_s_878_, 20);
v_usedCommRing_901_ = lean_ctor_get_uint8(v_s_878_, sizeof(void*)*22 + 1);
v_nonlinearOccs_902_ = lean_ctor_get(v_s_878_, 21);
v_isSharedCheck_910_ = !lean_is_exclusive(v_s_878_);
if (v_isSharedCheck_910_ == 0)
{
v___x_904_ = v_s_878_;
v_isShared_905_ = v_isSharedCheck_910_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_nonlinearOccs_902_);
lean_inc(v_divMod_900_);
lean_inc(v_diseqSplits_899_);
lean_inc(v_conflict_x3f_898_);
lean_inc(v_numReorderRequests_897_);
lean_inc(v_penalties_896_);
lean_inc(v_steps_895_);
lean_inc(v_nextCnstrId_893_);
lean_inc(v_assignment_892_);
lean_inc(v_occurs_891_);
lean_inc(v_elimStack_890_);
lean_inc(v_active_889_);
lean_inc(v_elimEqs_888_);
lean_inc(v_diseqs_887_);
lean_inc(v_uppers_886_);
lean_inc(v_lowers_885_);
lean_inc(v_dvds_884_);
lean_inc(v_natDef_883_);
lean_inc(v_natToIntMap_882_);
lean_inc(v_varsHistory_881_);
lean_inc(v_varMap_880_);
lean_inc(v_vars_879_);
lean_dec(v_s_878_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_910_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_906_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_892_, v_x_877_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 13, v___x_906_);
v___x_908_ = v___x_904_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_vars_879_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_varMap_880_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v_varsHistory_881_);
lean_ctor_set(v_reuseFailAlloc_909_, 3, v_natToIntMap_882_);
lean_ctor_set(v_reuseFailAlloc_909_, 4, v_natDef_883_);
lean_ctor_set(v_reuseFailAlloc_909_, 5, v_dvds_884_);
lean_ctor_set(v_reuseFailAlloc_909_, 6, v_lowers_885_);
lean_ctor_set(v_reuseFailAlloc_909_, 7, v_uppers_886_);
lean_ctor_set(v_reuseFailAlloc_909_, 8, v_diseqs_887_);
lean_ctor_set(v_reuseFailAlloc_909_, 9, v_elimEqs_888_);
lean_ctor_set(v_reuseFailAlloc_909_, 10, v_active_889_);
lean_ctor_set(v_reuseFailAlloc_909_, 11, v_elimStack_890_);
lean_ctor_set(v_reuseFailAlloc_909_, 12, v_occurs_891_);
lean_ctor_set(v_reuseFailAlloc_909_, 13, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_909_, 14, v_nextCnstrId_893_);
lean_ctor_set(v_reuseFailAlloc_909_, 15, v_steps_895_);
lean_ctor_set(v_reuseFailAlloc_909_, 16, v_penalties_896_);
lean_ctor_set(v_reuseFailAlloc_909_, 17, v_numReorderRequests_897_);
lean_ctor_set(v_reuseFailAlloc_909_, 18, v_conflict_x3f_898_);
lean_ctor_set(v_reuseFailAlloc_909_, 19, v_diseqSplits_899_);
lean_ctor_set(v_reuseFailAlloc_909_, 20, v_divMod_900_);
lean_ctor_set(v_reuseFailAlloc_909_, 21, v_nonlinearOccs_902_);
lean_ctor_set_uint8(v_reuseFailAlloc_909_, sizeof(void*)*22, v_caseSplits_894_);
lean_ctor_set_uint8(v_reuseFailAlloc_909_, sizeof(void*)*22 + 1, v_usedCommRing_901_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_x_911_, lean_object* v_s_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(v_x_911_, v_s_912_);
lean_dec(v_x_911_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object* v_x_914_, lean_object* v_a_915_){
_start:
{
lean_object* v___f_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___f_917_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_917_, 0, v_x_914_);
v___x_918_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_919_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_918_, v___f_917_, v_a_915_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___boxed(lean_object* v_x_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_920_, v_a_921_);
lean_dec(v_a_921_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(lean_object* v_x_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_924_, v_a_925_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___boxed(lean_object* v_x_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(v_x_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec(v_a_938_);
return v_res_949_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__0));
v___x_952_ = l_Lean_stringToMessageData(v___x_951_);
return v___x_952_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_unsigned_to_nat(1u);
v___x_954_ = lean_nat_to_int(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__3));
v___x_957_ = l_Lean_stringToMessageData(v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(lean_object* v_r_958_, lean_object* v_p_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
if (lean_obj_tag(v_p_959_) == 0)
{
lean_object* v_k_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_981_; 
v_k_963_ = lean_ctor_get(v_p_959_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v_p_959_);
if (v_isSharedCheck_981_ == 0)
{
v___x_965_ = v_p_959_;
v_isShared_966_ = v_isSharedCheck_981_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_k_963_);
lean_dec(v_p_959_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_981_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_967_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_968_ = lean_int_dec_eq(v_k_963_, v___x_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_969_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_970_, 0, v_r_958_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = l_Int_repr(v_k_963_);
lean_dec(v_k_963_);
if (v_isShared_966_ == 0)
{
lean_ctor_set_tag(v___x_965_, 3);
lean_ctor_set(v___x_965_, 0, v___x_971_);
v___x_973_ = v___x_965_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_971_);
v___x_973_ = v_reuseFailAlloc_977_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = l_Lean_MessageData_ofFormat(v___x_973_);
v___x_975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_970_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
}
else
{
lean_object* v___x_979_; 
lean_dec(v_k_963_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v_r_958_);
v___x_979_ = v___x_965_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_r_958_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v_k_982_; lean_object* v_v_983_; lean_object* v_p_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v_k_982_ = lean_ctor_get(v_p_959_, 0);
lean_inc(v_k_982_);
v_v_983_ = lean_ctor_get(v_p_959_, 1);
lean_inc(v_v_983_);
v_p_984_ = lean_ctor_get(v_p_959_, 2);
lean_inc_ref(v_p_984_);
lean_dec_ref_known(v_p_959_, 3);
v___x_985_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_986_ = lean_int_dec_eq(v_k_982_, v___x_985_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_983_, v_a_960_, v_a_961_);
lean_dec(v_v_983_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v_r_958_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l_Int_repr(v_k_982_);
lean_dec(v_k_982_);
v___x_992_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
v___x_993_ = l_Lean_MessageData_ofFormat(v___x_992_);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_990_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_988_);
v___x_998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v_r_958_ = v___x_998_;
v_p_959_ = v_p_984_;
goto _start;
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_dec_ref(v_p_984_);
lean_dec(v_k_982_);
lean_dec_ref(v_r_958_);
v_a_1000_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_987_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_987_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
else
{
lean_object* v___x_1008_; 
lean_dec(v_k_982_);
v___x_1008_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_983_, v_a_960_, v_a_961_);
lean_dec(v_v_983_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v_r_958_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_1009_);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v_r_958_ = v___x_1013_;
v_p_959_ = v_p_984_;
goto _start;
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref(v_p_984_);
lean_dec_ref(v_r_958_);
v_a_1015_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1008_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1008_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___boxed(lean_object* v_r_1023_, lean_object* v_p_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v_r_1023_, v_p_1024_, v_a_1025_, v_a_1026_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(lean_object* v_r_1029_, lean_object* v_p_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v_r_1029_, v_p_1030_, v_a_1031_, v_a_1039_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___boxed(lean_object* v_r_1043_, lean_object* v_p_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(v_r_1043_, v_p_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec(v_a_1045_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___redArg(lean_object* v_p_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
if (lean_obj_tag(v_p_1057_) == 0)
{
lean_object* v_k_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1071_; 
v_k_1061_ = lean_ctor_get(v_p_1057_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_p_1057_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1063_ = v_p_1057_;
v_isShared_1064_ = v_isSharedCheck_1071_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_k_1061_);
lean_dec(v_p_1057_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1071_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = l_Int_repr(v_k_1061_);
lean_dec(v_k_1061_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set_tag(v___x_1063_, 3);
lean_ctor_set(v___x_1063_, 0, v___x_1065_);
v___x_1067_ = v___x_1063_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = l_Lean_MessageData_ofFormat(v___x_1067_);
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
return v___x_1069_;
}
}
}
else
{
lean_object* v_k_1072_; lean_object* v_v_1073_; lean_object* v_p_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v_k_1072_ = lean_ctor_get(v_p_1057_, 0);
lean_inc(v_k_1072_);
v_v_1073_ = lean_ctor_get(v_p_1057_, 1);
lean_inc(v_v_1073_);
v_p_1074_ = lean_ctor_get(v_p_1057_, 2);
lean_inc_ref(v_p_1074_);
lean_dec_ref_known(v_p_1057_, 3);
v___x_1075_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_1076_ = lean_int_dec_eq(v_k_1072_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_1073_, v_a_1058_, v_a_1059_);
lean_dec(v_v_1073_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v___x_1079_ = l_Int_repr(v_k_1072_);
lean_dec(v_k_1072_);
v___x_1080_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
v___x_1081_ = l_Lean_MessageData_ofFormat(v___x_1080_);
v___x_1082_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_1078_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v___x_1085_, v_p_1074_, v_a_1058_, v_a_1059_);
return v___x_1086_;
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v_p_1074_);
lean_dec(v_k_1072_);
v_a_1087_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1077_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1077_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
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
lean_object* v___x_1095_; 
lean_dec(v_k_1072_);
v___x_1095_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_1073_, v_a_1058_, v_a_1059_);
lean_dec(v_v_1073_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v___x_1097_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_1096_);
v___x_1098_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v___x_1097_, v_p_1074_, v_a_1058_, v_a_1059_);
return v___x_1098_;
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec_ref(v_p_1074_);
v_a_1099_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1095_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1095_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___redArg___boxed(lean_object* v_p_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1107_, v_a_1108_, v_a_1109_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp(lean_object* v_p_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1112_, v_a_1113_, v_a_1121_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___boxed(lean_object* v_p_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Int_Internal_Linear_Poly_pp(v_p_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec(v_a_1126_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0(lean_object* v_a_1138_, lean_object* v___x_1139_, lean_object* v_x_1140_){
_start:
{
lean_object* v_size_1141_; uint8_t v___x_1142_; 
v_size_1141_ = lean_ctor_get(v_a_1138_, 2);
v___x_1142_ = lean_nat_dec_lt(v_x_1140_, v_size_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
v___x_1143_ = l_outOfBounds___redArg(v___x_1139_);
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1139_, v_a_1138_, v_x_1140_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed(lean_object* v_a_1145_, lean_object* v___x_1146_, lean_object* v_x_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0(v_a_1145_, v___x_1146_, v_x_1147_);
lean_dec(v_x_1147_);
lean_dec_ref(v___x_1146_);
lean_dec_ref(v_a_1145_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(lean_object* v_p_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = l_Lean_instInhabitedExpr;
v___x_1154_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_1150_, v_a_1151_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___f_1156_; lean_object* v___x_1157_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1154_, 1);
v___f_1156_ = lean_alloc_closure((void*)(l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1156_, 0, v_a_1155_);
lean_closure_set(v___f_1156_, 1, v___x_1153_);
v___x_1157_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_1156_, v_p_1149_);
return v___x_1157_;
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec_ref(v_p_1149_);
v_a_1158_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1154_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1154_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___boxed(lean_object* v_p_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1166_, v_a_1167_, v_a_1168_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27(lean_object* v_p_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1171_, v_a_1172_, v_a_1180_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___boxed(lean_object* v_p_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Int_Internal_Linear_Poly_denoteExpr_x27(v_p_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec(v_a_1185_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored___redArg(lean_object* v_c_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v_depth_x3f_1200_; 
v_depth_x3f_1200_ = lean_ctor_get(v_c_1197_, 2);
lean_inc(v_depth_x3f_1200_);
if (lean_obj_tag(v_depth_x3f_1200_) == 0)
{
lean_object* v_p_1201_; lean_object* v_h_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1227_; 
v_p_1201_ = lean_ctor_get(v_c_1197_, 0);
v_h_1202_ = lean_ctor_get(v_c_1197_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_c_1197_);
if (v_isSharedCheck_1227_ == 0)
{
lean_object* v_unused_1228_; 
v_unused_1228_ = lean_ctor_get(v_c_1197_, 2);
lean_dec(v_unused_1228_);
v___x_1204_ = v_c_1197_;
v_isShared_1205_ = v_isSharedCheck_1227_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_h_1202_);
lean_inc(v_p_1201_);
lean_dec(v_c_1197_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1227_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_Meta_Grind_getGoalStackDepth___redArg(v_a_1198_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1218_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1218_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1218_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_a_1207_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 2, v___x_1211_);
v___x_1213_ = v___x_1204_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_p_1201_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_h_1202_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1215_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v___x_1213_);
v___x_1215_ = v___x_1209_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_del_object(v___x_1204_);
lean_dec_ref(v_h_1202_);
lean_dec_ref(v_p_1201_);
v_a_1219_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1206_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1206_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
else
{
lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
v_isSharedCheck_1235_ = !lean_is_exclusive(v_depth_x3f_1200_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v_depth_x3f_1200_, 0);
lean_dec(v_unused_1236_);
v___x_1230_ = v_depth_x3f_1200_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_dec(v_depth_x3f_1200_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set_tag(v___x_1230_, 0);
lean_ctor_set(v___x_1230_, 0, v_c_1197_);
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_c_1197_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored___redArg___boxed(lean_object* v_c_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored___redArg(v_c_1237_, v_a_1238_);
lean_dec(v_a_1238_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored(lean_object* v_c_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored___redArg(v_c_1241_, v_a_1242_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored___boxed(lean_object* v_c_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored(v_c_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec(v_a_1255_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored___redArg(lean_object* v_c_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_depth_x3f_1270_; 
v_depth_x3f_1270_ = lean_ctor_get(v_c_1267_, 3);
lean_inc(v_depth_x3f_1270_);
if (lean_obj_tag(v_depth_x3f_1270_) == 0)
{
lean_object* v_d_1271_; lean_object* v_p_1272_; lean_object* v_h_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1298_; 
v_d_1271_ = lean_ctor_get(v_c_1267_, 0);
v_p_1272_ = lean_ctor_get(v_c_1267_, 1);
v_h_1273_ = lean_ctor_get(v_c_1267_, 2);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_c_1267_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; 
v_unused_1299_ = lean_ctor_get(v_c_1267_, 3);
lean_dec(v_unused_1299_);
v___x_1275_ = v_c_1267_;
v_isShared_1276_ = v_isSharedCheck_1298_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_h_1273_);
lean_inc(v_p_1272_);
lean_inc(v_d_1271_);
lean_dec(v_c_1267_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1298_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_Meta_Grind_getGoalStackDepth___redArg(v_a_1268_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1289_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1289_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1289_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_a_1278_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 3, v___x_1282_);
v___x_1284_ = v___x_1275_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_d_1271_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_p_1272_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v_h_1273_);
lean_ctor_set(v_reuseFailAlloc_1288_, 3, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1286_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1284_);
v___x_1286_ = v___x_1280_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_del_object(v___x_1275_);
lean_dec_ref(v_h_1273_);
lean_dec_ref(v_p_1272_);
lean_dec(v_d_1271_);
v_a_1290_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1277_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1277_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
else
{
lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
v_isSharedCheck_1306_ = !lean_is_exclusive(v_depth_x3f_1270_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; 
v_unused_1307_ = lean_ctor_get(v_depth_x3f_1270_, 0);
lean_dec(v_unused_1307_);
v___x_1301_ = v_depth_x3f_1270_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_dec(v_depth_x3f_1270_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
lean_ctor_set_tag(v___x_1301_, 0);
lean_ctor_set(v___x_1301_, 0, v_c_1267_);
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_c_1267_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored___redArg___boxed(lean_object* v_c_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored___redArg(v_c_1308_, v_a_1309_);
lean_dec(v_a_1309_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored(lean_object* v_c_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored___redArg(v_c_1312_, v_a_1313_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored___boxed(lean_object* v_c_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored(v_c_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec(v_a_1326_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored___redArg(lean_object* v_c_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_depth_x3f_1341_; 
v_depth_x3f_1341_ = lean_ctor_get(v_c_1338_, 2);
lean_inc(v_depth_x3f_1341_);
if (lean_obj_tag(v_depth_x3f_1341_) == 0)
{
lean_object* v_p_1342_; lean_object* v_h_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1368_; 
v_p_1342_ = lean_ctor_get(v_c_1338_, 0);
v_h_1343_ = lean_ctor_get(v_c_1338_, 1);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_c_1338_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; 
v_unused_1369_ = lean_ctor_get(v_c_1338_, 2);
lean_dec(v_unused_1369_);
v___x_1345_ = v_c_1338_;
v_isShared_1346_ = v_isSharedCheck_1368_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_h_1343_);
lean_inc(v_p_1342_);
lean_dec(v_c_1338_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1368_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_Meta_Grind_getGoalStackDepth___redArg(v_a_1339_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1359_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1359_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1359_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1352_, 0, v_a_1348_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 2, v___x_1352_);
v___x_1354_ = v___x_1345_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_p_1342_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_h_1343_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1356_; 
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1354_);
v___x_1356_ = v___x_1350_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_del_object(v___x_1345_);
lean_dec_ref(v_h_1343_);
lean_dec_ref(v_p_1342_);
v_a_1360_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1347_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1347_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
else
{
lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
v_isSharedCheck_1376_ = !lean_is_exclusive(v_depth_x3f_1341_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; 
v_unused_1377_ = lean_ctor_get(v_depth_x3f_1341_, 0);
lean_dec(v_unused_1377_);
v___x_1371_ = v_depth_x3f_1341_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_dec(v_depth_x3f_1341_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set_tag(v___x_1371_, 0);
lean_ctor_set(v___x_1371_, 0, v_c_1338_);
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_c_1338_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored___redArg___boxed(lean_object* v_c_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored___redArg(v_c_1378_, v_a_1379_);
lean_dec(v_a_1379_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored(lean_object* v_c_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored___redArg(v_c_1382_, v_a_1383_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored___boxed(lean_object* v_c_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored(v_c_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
lean_dec(v_a_1397_);
lean_dec(v_a_1396_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored___redArg(lean_object* v_c_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_depth_x3f_1411_; 
v_depth_x3f_1411_ = lean_ctor_get(v_c_1408_, 2);
lean_inc(v_depth_x3f_1411_);
if (lean_obj_tag(v_depth_x3f_1411_) == 0)
{
lean_object* v_p_1412_; lean_object* v_h_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1438_; 
v_p_1412_ = lean_ctor_get(v_c_1408_, 0);
v_h_1413_ = lean_ctor_get(v_c_1408_, 1);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_c_1408_);
if (v_isSharedCheck_1438_ == 0)
{
lean_object* v_unused_1439_; 
v_unused_1439_ = lean_ctor_get(v_c_1408_, 2);
lean_dec(v_unused_1439_);
v___x_1415_ = v_c_1408_;
v_isShared_1416_ = v_isSharedCheck_1438_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_h_1413_);
lean_inc(v_p_1412_);
lean_dec(v_c_1408_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1438_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_Meta_Grind_getGoalStackDepth___redArg(v_a_1409_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1429_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1420_ = v___x_1417_;
v_isShared_1421_ = v_isSharedCheck_1429_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1417_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1429_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v_a_1418_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 2, v___x_1422_);
v___x_1424_ = v___x_1415_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_p_1412_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_h_1413_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1426_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v___x_1424_);
v___x_1426_ = v___x_1420_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_del_object(v___x_1415_);
lean_dec_ref(v_h_1413_);
lean_dec_ref(v_p_1412_);
v_a_1430_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1417_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1417_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
else
{
lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_isSharedCheck_1446_ = !lean_is_exclusive(v_depth_x3f_1411_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; 
v_unused_1447_ = lean_ctor_get(v_depth_x3f_1411_, 0);
lean_dec(v_unused_1447_);
v___x_1441_ = v_depth_x3f_1411_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_dec(v_depth_x3f_1411_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set_tag(v___x_1441_, 0);
lean_ctor_set(v___x_1441_, 0, v_c_1408_);
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_c_1408_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored___redArg___boxed(lean_object* v_c_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored___redArg(v_c_1448_, v_a_1449_);
lean_dec(v_a_1449_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored(lean_object* v_c_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored___redArg(v_c_1452_, v_a_1453_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored___boxed(lean_object* v_c_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored(v_c_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec(v_a_1466_);
return v_res_1477_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object* v_c_1478_){
_start:
{
lean_object* v_p_1479_; 
v_p_1479_ = lean_ctor_get(v_c_1478_, 1);
if (lean_obj_tag(v_p_1479_) == 0)
{
lean_object* v_d_1480_; lean_object* v_k_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v_d_1480_ = lean_ctor_get(v_c_1478_, 0);
v_k_1481_ = lean_ctor_get(v_p_1479_, 0);
v___x_1482_ = lean_int_emod(v_k_1481_, v_d_1480_);
v___x_1483_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1484_ = lean_int_dec_eq(v___x_1482_, v___x_1483_);
lean_dec(v___x_1482_);
return v___x_1484_;
}
else
{
lean_object* v_d_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v_d_1485_ = lean_ctor_get(v_c_1478_, 0);
v___x_1486_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_1487_ = lean_int_dec_eq(v_d_1485_, v___x_1486_);
return v___x_1487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial___boxed(lean_object* v_c_1488_){
_start:
{
uint8_t v_res_1489_; lean_object* v_r_1490_; 
v_res_1489_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_c_1488_);
lean_dec_ref(v_c_1488_);
v_r_1490_ = lean_box(v_res_1489_);
return v_r_1490_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0));
v___x_1493_ = l_Lean_stringToMessageData(v___x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object* v_c_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v_d_1498_; lean_object* v_p_1499_; lean_object* v___x_1500_; 
v_d_1498_ = lean_ctor_get(v_c_1494_, 0);
lean_inc(v_d_1498_);
v_p_1499_ = lean_ctor_get(v_c_1494_, 1);
lean_inc_ref(v_p_1499_);
lean_dec_ref(v_c_1494_);
v___x_1500_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1499_, v_a_1495_, v_a_1496_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1514_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1503_ = v___x_1500_;
v_isShared_1504_ = v_isSharedCheck_1514_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1500_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1514_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1505_ = l_Int_repr(v_d_1498_);
lean_dec(v_d_1498_);
v___x_1506_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
v___x_1507_ = l_Lean_MessageData_ofFormat(v___x_1506_);
v___x_1508_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1);
v___x_1509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v_a_1501_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 0, v___x_1510_);
v___x_1512_ = v___x_1503_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
else
{
lean_dec(v_d_1498_);
return v___x_1500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___boxed(lean_object* v_c_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1515_, v_a_1516_, v_a_1517_);
lean_dec_ref(v_a_1517_);
lean_dec(v_a_1516_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(lean_object* v_c_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1520_, v_a_1521_, v_a_1529_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___boxed(lean_object* v_c_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(v_c_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec(v_a_1534_);
return v_res_1545_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = lean_unsigned_to_nat(0u);
v___x_1552_ = l_Lean_Level_ofNat(v___x_1551_);
return v___x_1552_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1553_ = lean_box(0);
v___x_1554_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3);
v___x_1555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v___x_1553_);
return v___x_1555_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4);
v___x_1557_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2));
v___x_1558_ = l_Lean_Expr_const___override(v___x_1557_, v___x_1556_);
return v___x_1558_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = lean_box(0);
v___x_1563_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7));
v___x_1564_ = l_Lean_Expr_const___override(v___x_1563_, v___x_1562_);
return v___x_1564_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = lean_box(0);
v___x_1570_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10));
v___x_1571_ = l_Lean_Expr_const___override(v___x_1570_, v___x_1569_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(lean_object* v_c_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_){
_start:
{
lean_object* v_d_1576_; lean_object* v_p_1577_; lean_object* v___x_1578_; 
v_d_1576_ = lean_ctor_get(v_c_1572_, 0);
lean_inc(v_d_1576_);
v_p_1577_ = lean_ctor_get(v_c_1572_, 1);
lean_inc_ref(v_p_1577_);
lean_dec_ref(v_c_1572_);
v___x_1578_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1577_, v_a_1573_, v_a_1574_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1600_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1581_ = v___x_1578_;
v_isShared_1582_ = v_isSharedCheck_1600_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1578_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1600_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___y_1584_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v___x_1589_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1590_ = lean_int_dec_le(v___x_1589_, v_d_1576_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1591_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5);
v___x_1592_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8);
v___x_1593_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11);
v___x_1594_ = lean_int_neg(v_d_1576_);
lean_dec(v_d_1576_);
v___x_1595_ = l_Int_toNat(v___x_1594_);
lean_dec(v___x_1594_);
v___x_1596_ = l_Lean_instToExprInt_mkNat(v___x_1595_);
v___x_1597_ = l_Lean_mkApp3(v___x_1591_, v___x_1592_, v___x_1593_, v___x_1596_);
v___y_1584_ = v___x_1597_;
goto v___jp_1583_;
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = l_Int_toNat(v_d_1576_);
lean_dec(v_d_1576_);
v___x_1599_ = l_Lean_instToExprInt_mkNat(v___x_1598_);
v___y_1584_ = v___x_1599_;
goto v___jp_1583_;
}
v___jp_1583_:
{
lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1585_ = l_Lean_mkIntDvd(v___y_1584_, v_a_1579_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1585_);
v___x_1587_ = v___x_1581_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
lean_dec(v_d_1576_);
return v___x_1578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1601_, v_a_1602_, v_a_1603_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(lean_object* v_c_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1606_, v_a_1607_, v_a_1615_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___boxed(lean_object* v_c_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(v_c_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec(v_a_1620_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(lean_object* v_msgData_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; lean_object* v_env_1639_; uint8_t v___x_1640_; lean_object* v_env_1641_; lean_object* v___x_1642_; lean_object* v_toCold_1643_; lean_object* v_mctx_1644_; lean_object* v_lctx_1645_; lean_object* v_options_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1638_ = lean_st_ref_get(v___y_1636_);
v_env_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc_ref(v_env_1639_);
lean_dec(v___x_1638_);
v___x_1640_ = 0;
v_env_1641_ = l_Lean_Environment_setRecordingDeps(v_env_1639_, v___x_1640_);
v___x_1642_ = lean_st_ref_get(v___y_1634_);
v_toCold_1643_ = lean_ctor_get(v___y_1635_, 0);
v_mctx_1644_ = lean_ctor_get(v___x_1642_, 0);
lean_inc_ref(v_mctx_1644_);
lean_dec(v___x_1642_);
v_lctx_1645_ = lean_ctor_get(v___y_1633_, 2);
v_options_1646_ = lean_ctor_get(v_toCold_1643_, 2);
lean_inc_ref(v_options_1646_);
lean_inc_ref(v_lctx_1645_);
v___x_1647_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1647_, 0, v_env_1641_);
lean_ctor_set(v___x_1647_, 1, v_mctx_1644_);
lean_ctor_set(v___x_1647_, 2, v_lctx_1645_);
lean_ctor_set(v___x_1647_, 3, v_options_1646_);
v___x_1648_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
lean_ctor_set(v___x_1648_, 1, v_msgData_1632_);
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object* v_msgData_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msgData_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(lean_object* v_msg_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_ref_1663_; lean_object* v___x_1664_; lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1673_; 
v_ref_1663_ = lean_ctor_get(v___y_1660_, 2);
v___x_1664_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msg_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
lean_inc(v_ref_1663_);
v___x_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1669_, 0, v_ref_1663_);
lean_ctor_set(v___x_1669_, 1, v_a_1665_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 1);
lean_ctor_set(v___x_1667_, 0, v___x_1669_);
v___x_1671_ = v___x_1667_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg___boxed(lean_object* v_msg_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
return v_res_1680_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0));
v___x_1683_ = l_Lean_stringToMessageData(v___x_1682_);
return v___x_1683_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2));
v___x_1686_ = l_Lean_stringToMessageData(v___x_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object* v_c_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1687_, v_a_1688_, v_a_1696_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1699_, 1);
v___x_1701_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1702_ = l_Lean_indentD(v_a_1700_);
v___x_1703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3);
v___x_1705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1705_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
return v___x_1706_;
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
v_a_1707_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1699_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1699_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(lean_object* v_00_u03b1_1728_, lean_object* v_c_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1742_, lean_object* v_c_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(v_00_u03b1_1742_, v_c_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
lean_dec(v_a_1749_);
lean_dec_ref(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec(v_a_1744_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(lean_object* v_00_u03b1_1756_, lean_object* v_msg_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1757_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___boxed(lean_object* v_00_u03b1_1770_, lean_object* v_msg_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(v_00_u03b1_1770_, v_msg_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec(v___y_1772_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial_spec__0(lean_object* v_a_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = lean_nat_to_int(v_a_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(lean_object* v_c_1786_){
_start:
{
lean_object* v_p_1787_; 
v_p_1787_ = lean_ctor_get(v_c_1786_, 0);
if (lean_obj_tag(v_p_1787_) == 0)
{
lean_object* v_k_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v_k_1788_ = lean_ctor_get(v_p_1787_, 0);
v___x_1789_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1790_ = lean_int_dec_eq(v_k_1788_, v___x_1789_);
if (v___x_1790_ == 0)
{
uint8_t v___x_1791_; 
v___x_1791_ = 1;
return v___x_1791_;
}
else
{
uint8_t v___x_1792_; 
v___x_1792_ = 0;
return v___x_1792_;
}
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1793_ = l_Int_Internal_Linear_Poly_getConst(v_p_1787_);
v___x_1794_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v_p_1787_);
v___x_1795_ = lean_nat_to_int(v___x_1794_);
v___x_1796_ = lean_int_emod(v___x_1793_, v___x_1795_);
lean_dec(v___x_1795_);
lean_dec(v___x_1793_);
v___x_1797_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1798_ = lean_int_dec_eq(v___x_1796_, v___x_1797_);
lean_dec(v___x_1796_);
if (v___x_1798_ == 0)
{
uint8_t v___x_1799_; 
v___x_1799_ = 1;
return v___x_1799_;
}
else
{
uint8_t v___x_1800_; 
v___x_1800_ = 0;
return v___x_1800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial___boxed(lean_object* v_c_1801_){
_start:
{
uint8_t v_res_1802_; lean_object* v_r_1803_; 
v_res_1802_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(v_c_1801_);
lean_dec_ref(v_c_1801_);
v_r_1803_ = lean_box(v_res_1802_);
return v_r_1803_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0));
v___x_1806_ = l_Lean_stringToMessageData(v___x_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(lean_object* v_c_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v_p_1811_; lean_object* v___x_1812_; 
v_p_1811_ = lean_ctor_get(v_c_1807_, 0);
lean_inc_ref(v_p_1811_);
lean_dec_ref(v_c_1807_);
v___x_1812_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1811_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1822_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1822_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1822_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1817_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v_a_1813_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1818_);
v___x_1820_ = v___x_1815_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
else
{
return v___x_1812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___boxed(lean_object* v_c_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1823_, v_a_1824_, v_a_1825_);
lean_dec_ref(v_a_1825_);
lean_dec(v_a_1824_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(lean_object* v_c_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1828_, v_a_1829_, v_a_1837_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___boxed(lean_object* v_c_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(v_c_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
lean_dec(v_a_1849_);
lean_dec_ref(v_a_1848_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
lean_dec(v_a_1843_);
lean_dec(v_a_1842_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(lean_object* v_c_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1854_, v_a_1855_, v_a_1858_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref_known(v___x_1861_, 1);
v___x_1863_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1864_ = l_Lean_indentD(v_a_1862_);
v___x_1865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1863_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1865_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
return v___x_1866_;
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
v_a_1867_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1861_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1861_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
lean_dec(v_a_1876_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(lean_object* v_00_u03b1_1883_, lean_object* v_c_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1884_, v_a_1885_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1897_, lean_object* v_c_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(v_00_u03b1_1897_, v_c_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
lean_dec(v_a_1908_);
lean_dec_ref(v_a_1907_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec(v_a_1899_);
return v_res_1910_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0(void){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1912_ = l_Lean_mkIntLit(v___x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(lean_object* v_c_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
lean_object* v_p_1917_; lean_object* v___x_1918_; 
v_p_1917_ = lean_ctor_get(v_c_1913_, 0);
lean_inc_ref(v_p_1917_);
lean_dec_ref(v_c_1913_);
v___x_1918_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1917_, v_a_1914_, v_a_1915_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1929_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1929_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1929_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1923_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1924_ = l_Lean_mkIntEq(v_a_1919_, v___x_1923_);
v___x_1925_ = l_Lean_mkNot(v___x_1924_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1925_);
v___x_1927_ = v___x_1921_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
else
{
return v___x_1918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1930_, v_a_1931_, v_a_1932_);
lean_dec_ref(v_a_1932_);
lean_dec(v_a_1931_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(lean_object* v_c_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1935_, v_a_1936_, v_a_1944_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___boxed(lean_object* v_c_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(v_c_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec(v_a_1949_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert___boxed(lean_object* v_c_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_00___x40___internal___hyg_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = lean_grind_cutsat_assert_le(v_c_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
return v_res_1985_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(lean_object* v_c_1986_){
_start:
{
lean_object* v_p_1987_; 
v_p_1987_ = lean_ctor_get(v_c_1986_, 0);
if (lean_obj_tag(v_p_1987_) == 0)
{
lean_object* v_k_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v_k_1988_ = lean_ctor_get(v_p_1987_, 0);
v___x_1989_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1990_ = lean_int_dec_le(v_k_1988_, v___x_1989_);
return v___x_1990_;
}
else
{
uint8_t v___x_1991_; 
v___x_1991_ = 0;
return v___x_1991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial___boxed(lean_object* v_c_1992_){
_start:
{
uint8_t v_res_1993_; lean_object* v_r_1994_; 
v_res_1993_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_c_1992_);
lean_dec_ref(v_c_1992_);
v_r_1994_ = lean_box(v_res_1993_);
return v_r_1994_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0));
v___x_1997_ = l_Lean_stringToMessageData(v___x_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(lean_object* v_c_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v_p_2002_; lean_object* v___x_2003_; 
v_p_2002_ = lean_ctor_get(v_c_1998_, 0);
lean_inc_ref(v_p_2002_);
lean_dec_ref(v_c_1998_);
v___x_2003_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_2002_, v_a_1999_, v_a_2000_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2013_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2006_ = v___x_2003_;
v_isShared_2007_ = v_isSharedCheck_2013_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_2003_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2013_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2008_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1);
v___x_2009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2009_, 0, v_a_2004_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v___x_2009_);
v___x_2011_ = v___x_2006_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
else
{
return v___x_2003_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___boxed(lean_object* v_c_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_2014_, v_a_2015_, v_a_2016_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(lean_object* v_c_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_2019_, v_a_2020_, v_a_2028_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___boxed(lean_object* v_c_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(v_c_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec(v_a_2038_);
lean_dec_ref(v_a_2037_);
lean_dec(v_a_2036_);
lean_dec_ref(v_a_2035_);
lean_dec(v_a_2034_);
lean_dec(v_a_2033_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(lean_object* v_c_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v_p_2049_; lean_object* v___x_2050_; 
v_p_2049_ = lean_ctor_get(v_c_2045_, 0);
lean_inc_ref(v_p_2049_);
lean_dec_ref(v_c_2045_);
v___x_2050_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_2049_, v_a_2046_, v_a_2047_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2060_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2060_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2060_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2055_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_2056_ = l_Lean_mkIntLE(v_a_2051_, v___x_2055_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2056_);
v___x_2058_ = v___x_2053_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
else
{
return v___x_2050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg___boxed(lean_object* v_c_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_2061_, v_a_2062_, v_a_2063_);
lean_dec_ref(v_a_2063_);
lean_dec(v_a_2062_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(lean_object* v_c_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_2066_, v_a_2067_, v_a_2075_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___boxed(lean_object* v_c_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(v_c_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
lean_dec(v_a_2089_);
lean_dec_ref(v_a_2088_);
lean_dec(v_a_2087_);
lean_dec_ref(v_a_2086_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec(v_a_2080_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(lean_object* v_c_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_2092_, v_a_2093_, v_a_2096_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v___x_2101_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_2102_ = l_Lean_indentD(v_a_2100_);
v___x_2103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2101_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
v___x_2104_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2103_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
return v___x_2104_;
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
v_a_2105_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2099_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2099_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(lean_object* v_00_u03b1_2121_, lean_object* v_c_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_2122_, v_a_2123_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_2135_, lean_object* v_c_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(v_00_u03b1_2135_, v_c_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec(v_a_2137_);
return v_res_2148_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(lean_object* v_c_2149_){
_start:
{
lean_object* v_p_2150_; 
v_p_2150_ = lean_ctor_get(v_c_2149_, 0);
if (lean_obj_tag(v_p_2150_) == 0)
{
lean_object* v_k_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; 
v_k_2151_ = lean_ctor_get(v_p_2150_, 0);
v___x_2152_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_2153_ = lean_int_dec_eq(v_k_2151_, v___x_2152_);
return v___x_2153_;
}
else
{
uint8_t v___x_2154_; 
v___x_2154_ = 0;
return v___x_2154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial___boxed(lean_object* v_c_2155_){
_start:
{
uint8_t v_res_2156_; lean_object* v_r_2157_; 
v_res_2156_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(v_c_2155_);
lean_dec_ref(v_c_2155_);
v_r_2157_ = lean_box(v_res_2156_);
return v_r_2157_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0));
v___x_2160_ = l_Lean_stringToMessageData(v___x_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object* v_c_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v_p_2165_; lean_object* v___x_2166_; 
v_p_2165_ = lean_ctor_get(v_c_2161_, 0);
lean_inc_ref(v_p_2165_);
lean_dec_ref(v_c_2161_);
v___x_2166_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_2165_, v_a_2162_, v_a_2163_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2176_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2176_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2176_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2171_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1);
v___x_2172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2172_, 0, v_a_2167_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v___x_2172_);
v___x_2174_ = v___x_2169_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
else
{
return v___x_2166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___boxed(lean_object* v_c_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_2177_, v_a_2178_, v_a_2179_);
lean_dec_ref(v_a_2179_);
lean_dec(v_a_2178_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(lean_object* v_c_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_2182_, v_a_2183_, v_a_2191_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___boxed(lean_object* v_c_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(v_c_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
lean_dec(v_a_2197_);
lean_dec(v_a_2196_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(lean_object* v_c_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v_p_2212_; lean_object* v___x_2213_; 
v_p_2212_ = lean_ctor_get(v_c_2208_, 0);
lean_inc_ref(v_p_2212_);
lean_dec_ref(v_c_2208_);
v___x_2213_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_2212_, v_a_2209_, v_a_2210_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2223_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2216_ = v___x_2213_;
v_isShared_2217_ = v_isSharedCheck_2223_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2213_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2223_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2218_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_2219_ = l_Lean_mkIntEq(v_a_2214_, v___x_2218_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v___x_2219_);
v___x_2221_ = v___x_2216_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
else
{
return v___x_2213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_2224_, v_a_2225_, v_a_2226_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(lean_object* v_c_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_2229_, v_a_2230_, v_a_2238_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___boxed(lean_object* v_c_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(v_c_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
lean_dec(v_a_2250_);
lean_dec_ref(v_a_2249_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec(v_a_2246_);
lean_dec_ref(v_a_2245_);
lean_dec(v_a_2244_);
lean_dec(v_a_2243_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(lean_object* v_c_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_2255_, v_a_2256_, v_a_2259_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v___x_2262_, 1);
v___x_2264_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_2265_ = l_Lean_indentD(v_a_2263_);
v___x_2266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2266_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_);
return v___x_2267_;
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
v_a_2268_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2262_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2262_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_);
lean_dec(v_a_2281_);
lean_dec_ref(v_a_2280_);
lean_dec(v_a_2279_);
lean_dec_ref(v_a_2278_);
lean_dec(v_a_2277_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(lean_object* v_00_u03b1_2284_, lean_object* v_c_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_2285_, v_a_2286_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_2298_, lean_object* v_c_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(v_00_u03b1_2298_, v_c_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec(v_a_2301_);
lean_dec(v_a_2300_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(lean_object* v_x_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2313_, v_a_2314_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2333_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2319_ = v___x_2316_;
v_isShared_2320_ = v_isSharedCheck_2333_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_2316_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2333_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v_occurs_2321_; lean_object* v_size_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
v_occurs_2321_ = lean_ctor_get(v_a_2317_, 12);
lean_inc_ref(v_occurs_2321_);
lean_dec(v_a_2317_);
v_size_2322_ = lean_ctor_get(v_occurs_2321_, 2);
v___x_2323_ = lean_box(1);
v___x_2324_ = lean_nat_dec_lt(v_x_2312_, v_size_2322_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2327_; 
lean_dec_ref(v_occurs_2321_);
v___x_2325_ = l_outOfBounds___redArg(v___x_2323_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2325_);
v___x_2327_ = v___x_2319_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2329_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2323_, v_occurs_2321_, v_x_2312_);
lean_dec_ref(v_occurs_2321_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2329_);
v___x_2331_ = v___x_2319_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
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
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
v_a_2334_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2316_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2316_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg___boxed(lean_object* v_x_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2342_, v_a_2343_, v_a_2344_);
lean_dec_ref(v_a_2344_);
lean_dec(v_a_2343_);
lean_dec(v_x_2342_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(lean_object* v_x_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2347_, v_a_2348_, v_a_2356_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___boxed(lean_object* v_x_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(v_x_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
lean_dec(v_a_2368_);
lean_dec_ref(v_a_2367_);
lean_dec(v_a_2366_);
lean_dec_ref(v_a_2365_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
lean_dec(v_a_2362_);
lean_dec(v_a_2361_);
lean_dec(v_x_2360_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(lean_object* v_k_2373_, lean_object* v_v_2374_, lean_object* v_t_2375_){
_start:
{
if (lean_obj_tag(v_t_2375_) == 0)
{
lean_object* v_size_2376_; lean_object* v_k_2377_; lean_object* v_v_2378_; lean_object* v_l_2379_; lean_object* v_r_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2661_; 
v_size_2376_ = lean_ctor_get(v_t_2375_, 0);
v_k_2377_ = lean_ctor_get(v_t_2375_, 1);
v_v_2378_ = lean_ctor_get(v_t_2375_, 2);
v_l_2379_ = lean_ctor_get(v_t_2375_, 3);
v_r_2380_ = lean_ctor_get(v_t_2375_, 4);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_t_2375_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2382_ = v_t_2375_;
v_isShared_2383_ = v_isSharedCheck_2661_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_r_2380_);
lean_inc(v_l_2379_);
lean_inc(v_v_2378_);
lean_inc(v_k_2377_);
lean_inc(v_size_2376_);
lean_dec(v_t_2375_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2661_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
uint8_t v___x_2384_; 
v___x_2384_ = lean_nat_dec_lt(v_k_2373_, v_k_2377_);
if (v___x_2384_ == 0)
{
uint8_t v___x_2385_; 
v___x_2385_ = lean_nat_dec_eq(v_k_2373_, v_k_2377_);
if (v___x_2385_ == 0)
{
lean_object* v_impl_2386_; lean_object* v___x_2387_; 
lean_dec(v_size_2376_);
v_impl_2386_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2373_, v_v_2374_, v_r_2380_);
v___x_2387_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2379_) == 0)
{
lean_object* v_size_2388_; lean_object* v_size_2389_; lean_object* v_k_2390_; lean_object* v_v_2391_; lean_object* v_l_2392_; lean_object* v_r_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; 
v_size_2388_ = lean_ctor_get(v_l_2379_, 0);
v_size_2389_ = lean_ctor_get(v_impl_2386_, 0);
v_k_2390_ = lean_ctor_get(v_impl_2386_, 1);
v_v_2391_ = lean_ctor_get(v_impl_2386_, 2);
v_l_2392_ = lean_ctor_get(v_impl_2386_, 3);
lean_inc(v_l_2392_);
v_r_2393_ = lean_ctor_get(v_impl_2386_, 4);
v___x_2394_ = lean_unsigned_to_nat(3u);
v___x_2395_ = lean_nat_mul(v___x_2394_, v_size_2388_);
v___x_2396_ = lean_nat_dec_lt(v___x_2395_, v_size_2389_);
lean_dec(v___x_2395_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
lean_dec(v_l_2392_);
v___x_2397_ = lean_nat_add(v___x_2387_, v_size_2388_);
v___x_2398_ = lean_nat_add(v___x_2397_, v_size_2389_);
lean_dec(v___x_2397_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 4, v_impl_2386_);
lean_ctor_set(v___x_2382_, 0, v___x_2398_);
v___x_2400_ = v___x_2382_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v_k_2377_);
lean_ctor_set(v_reuseFailAlloc_2401_, 2, v_v_2378_);
lean_ctor_set(v_reuseFailAlloc_2401_, 3, v_l_2379_);
lean_ctor_set(v_reuseFailAlloc_2401_, 4, v_impl_2386_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
else
{
lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2465_; 
lean_inc(v_r_2393_);
lean_inc(v_v_2391_);
lean_inc(v_k_2390_);
lean_inc(v_size_2389_);
v_isSharedCheck_2465_ = !lean_is_exclusive(v_impl_2386_);
if (v_isSharedCheck_2465_ == 0)
{
lean_object* v_unused_2466_; lean_object* v_unused_2467_; lean_object* v_unused_2468_; lean_object* v_unused_2469_; lean_object* v_unused_2470_; 
v_unused_2466_ = lean_ctor_get(v_impl_2386_, 4);
lean_dec(v_unused_2466_);
v_unused_2467_ = lean_ctor_get(v_impl_2386_, 3);
lean_dec(v_unused_2467_);
v_unused_2468_ = lean_ctor_get(v_impl_2386_, 2);
lean_dec(v_unused_2468_);
v_unused_2469_ = lean_ctor_get(v_impl_2386_, 1);
lean_dec(v_unused_2469_);
v_unused_2470_ = lean_ctor_get(v_impl_2386_, 0);
lean_dec(v_unused_2470_);
v___x_2403_ = v_impl_2386_;
v_isShared_2404_ = v_isSharedCheck_2465_;
goto v_resetjp_2402_;
}
else
{
lean_dec(v_impl_2386_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2465_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v_size_2405_; lean_object* v_k_2406_; lean_object* v_v_2407_; lean_object* v_l_2408_; lean_object* v_r_2409_; lean_object* v_size_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; 
v_size_2405_ = lean_ctor_get(v_l_2392_, 0);
v_k_2406_ = lean_ctor_get(v_l_2392_, 1);
v_v_2407_ = lean_ctor_get(v_l_2392_, 2);
v_l_2408_ = lean_ctor_get(v_l_2392_, 3);
v_r_2409_ = lean_ctor_get(v_l_2392_, 4);
v_size_2410_ = lean_ctor_get(v_r_2393_, 0);
v___x_2411_ = lean_unsigned_to_nat(2u);
v___x_2412_ = lean_nat_mul(v___x_2411_, v_size_2410_);
v___x_2413_ = lean_nat_dec_lt(v_size_2405_, v___x_2412_);
lean_dec(v___x_2412_);
if (v___x_2413_ == 0)
{
lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2441_; 
lean_inc(v_r_2409_);
lean_inc(v_l_2408_);
lean_inc(v_v_2407_);
lean_inc(v_k_2406_);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_l_2392_);
if (v_isSharedCheck_2441_ == 0)
{
lean_object* v_unused_2442_; lean_object* v_unused_2443_; lean_object* v_unused_2444_; lean_object* v_unused_2445_; lean_object* v_unused_2446_; 
v_unused_2442_ = lean_ctor_get(v_l_2392_, 4);
lean_dec(v_unused_2442_);
v_unused_2443_ = lean_ctor_get(v_l_2392_, 3);
lean_dec(v_unused_2443_);
v_unused_2444_ = lean_ctor_get(v_l_2392_, 2);
lean_dec(v_unused_2444_);
v_unused_2445_ = lean_ctor_get(v_l_2392_, 1);
lean_dec(v_unused_2445_);
v_unused_2446_ = lean_ctor_get(v_l_2392_, 0);
lean_dec(v_unused_2446_);
v___x_2415_ = v_l_2392_;
v_isShared_2416_ = v_isSharedCheck_2441_;
goto v_resetjp_2414_;
}
else
{
lean_dec(v_l_2392_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2441_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2431_; 
v___x_2417_ = lean_nat_add(v___x_2387_, v_size_2388_);
v___x_2418_ = lean_nat_add(v___x_2417_, v_size_2389_);
lean_dec(v_size_2389_);
if (lean_obj_tag(v_l_2408_) == 0)
{
lean_object* v_size_2439_; 
v_size_2439_ = lean_ctor_get(v_l_2408_, 0);
lean_inc(v_size_2439_);
v___y_2431_ = v_size_2439_;
goto v___jp_2430_;
}
else
{
lean_object* v___x_2440_; 
v___x_2440_ = lean_unsigned_to_nat(0u);
v___y_2431_ = v___x_2440_;
goto v___jp_2430_;
}
v___jp_2419_:
{
lean_object* v___x_2423_; lean_object* v___x_2425_; 
v___x_2423_ = lean_nat_add(v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec(v___y_2421_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 4, v_r_2393_);
lean_ctor_set(v___x_2415_, 3, v_r_2409_);
lean_ctor_set(v___x_2415_, 2, v_v_2391_);
lean_ctor_set(v___x_2415_, 1, v_k_2390_);
lean_ctor_set(v___x_2415_, 0, v___x_2423_);
v___x_2425_ = v___x_2415_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2423_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v_k_2390_);
lean_ctor_set(v_reuseFailAlloc_2429_, 2, v_v_2391_);
lean_ctor_set(v_reuseFailAlloc_2429_, 3, v_r_2409_);
lean_ctor_set(v_reuseFailAlloc_2429_, 4, v_r_2393_);
v___x_2425_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
lean_object* v___x_2427_; 
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 4, v___x_2425_);
lean_ctor_set(v___x_2403_, 3, v___y_2420_);
lean_ctor_set(v___x_2403_, 2, v_v_2407_);
lean_ctor_set(v___x_2403_, 1, v_k_2406_);
lean_ctor_set(v___x_2403_, 0, v___x_2418_);
v___x_2427_ = v___x_2403_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2418_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_k_2406_);
lean_ctor_set(v_reuseFailAlloc_2428_, 2, v_v_2407_);
lean_ctor_set(v_reuseFailAlloc_2428_, 3, v___y_2420_);
lean_ctor_set(v_reuseFailAlloc_2428_, 4, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
v___jp_2430_:
{
lean_object* v___x_2432_; lean_object* v___x_2434_; 
v___x_2432_ = lean_nat_add(v___x_2417_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec(v___x_2417_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 4, v_l_2408_);
lean_ctor_set(v___x_2382_, 0, v___x_2432_);
v___x_2434_ = v___x_2382_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2432_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_k_2377_);
lean_ctor_set(v_reuseFailAlloc_2438_, 2, v_v_2378_);
lean_ctor_set(v_reuseFailAlloc_2438_, 3, v_l_2379_);
lean_ctor_set(v_reuseFailAlloc_2438_, 4, v_l_2408_);
v___x_2434_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_nat_add(v___x_2387_, v_size_2410_);
if (lean_obj_tag(v_r_2409_) == 0)
{
lean_object* v_size_2436_; 
v_size_2436_ = lean_ctor_get(v_r_2409_, 0);
lean_inc(v_size_2436_);
v___y_2420_ = v___x_2434_;
v___y_2421_ = v___x_2435_;
v___y_2422_ = v_size_2436_;
goto v___jp_2419_;
}
else
{
lean_object* v___x_2437_; 
v___x_2437_ = lean_unsigned_to_nat(0u);
v___y_2420_ = v___x_2434_;
v___y_2421_ = v___x_2435_;
v___y_2422_ = v___x_2437_;
goto v___jp_2419_;
}
}
}
}
}
else
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2451_; 
lean_del_object(v___x_2382_);
v___x_2447_ = lean_nat_add(v___x_2387_, v_size_2388_);
v___x_2448_ = lean_nat_add(v___x_2447_, v_size_2389_);
lean_dec(v_size_2389_);
v___x_2449_ = lean_nat_add(v___x_2447_, v_size_2405_);
lean_dec(v___x_2447_);
lean_inc_ref(v_l_2379_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 4, v_l_2392_);
lean_ctor_set(v___x_2403_, 3, v_l_2379_);
lean_ctor_set(v___x_2403_, 2, v_v_2378_);
lean_ctor_set(v___x_2403_, 1, v_k_2377_);
lean_ctor_set(v___x_2403_, 0, v___x_2449_);
v___x_2451_ = v___x_2403_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v_k_2377_);
lean_ctor_set(v_reuseFailAlloc_2464_, 2, v_v_2378_);
lean_ctor_set(v_reuseFailAlloc_2464_, 3, v_l_2379_);
lean_ctor_set(v_reuseFailAlloc_2464_, 4, v_l_2392_);
v___x_2451_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
v_isSharedCheck_2458_ = !lean_is_exclusive(v_l_2379_);
if (v_isSharedCheck_2458_ == 0)
{
lean_object* v_unused_2459_; lean_object* v_unused_2460_; lean_object* v_unused_2461_; lean_object* v_unused_2462_; lean_object* v_unused_2463_; 
v_unused_2459_ = lean_ctor_get(v_l_2379_, 4);
lean_dec(v_unused_2459_);
v_unused_2460_ = lean_ctor_get(v_l_2379_, 3);
lean_dec(v_unused_2460_);
v_unused_2461_ = lean_ctor_get(v_l_2379_, 2);
lean_dec(v_unused_2461_);
v_unused_2462_ = lean_ctor_get(v_l_2379_, 1);
lean_dec(v_unused_2462_);
v_unused_2463_ = lean_ctor_get(v_l_2379_, 0);
lean_dec(v_unused_2463_);
v___x_2453_ = v_l_2379_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_dec(v_l_2379_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 4, v_r_2393_);
lean_ctor_set(v___x_2453_, 3, v___x_2451_);
lean_ctor_set(v___x_2453_, 2, v_v_2391_);
lean_ctor_set(v___x_2453_, 1, v_k_2390_);
lean_ctor_set(v___x_2453_, 0, v___x_2448_);
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2448_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_k_2390_);
lean_ctor_set(v_reuseFailAlloc_2457_, 2, v_v_2391_);
lean_ctor_set(v_reuseFailAlloc_2457_, 3, v___x_2451_);
lean_ctor_set(v_reuseFailAlloc_2457_, 4, v_r_2393_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2471_; 
v_l_2471_ = lean_ctor_get(v_impl_2386_, 3);
lean_inc(v_l_2471_);
if (lean_obj_tag(v_l_2471_) == 0)
{
lean_object* v_r_2472_; lean_object* v_k_2473_; lean_object* v_v_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2497_; 
v_r_2472_ = lean_ctor_get(v_impl_2386_, 4);
v_k_2473_ = lean_ctor_get(v_impl_2386_, 1);
v_v_2474_ = lean_ctor_get(v_impl_2386_, 2);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_impl_2386_);
if (v_isSharedCheck_2497_ == 0)
{
lean_object* v_unused_2498_; lean_object* v_unused_2499_; 
v_unused_2498_ = lean_ctor_get(v_impl_2386_, 3);
lean_dec(v_unused_2498_);
v_unused_2499_ = lean_ctor_get(v_impl_2386_, 0);
lean_dec(v_unused_2499_);
v___x_2476_ = v_impl_2386_;
v_isShared_2477_ = v_isSharedCheck_2497_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_r_2472_);
lean_inc(v_v_2474_);
lean_inc(v_k_2473_);
lean_dec(v_impl_2386_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2497_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v_k_2478_; lean_object* v_v_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2493_; 
v_k_2478_ = lean_ctor_get(v_l_2471_, 1);
v_v_2479_ = lean_ctor_get(v_l_2471_, 2);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_l_2471_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; lean_object* v_unused_2495_; lean_object* v_unused_2496_; 
v_unused_2494_ = lean_ctor_get(v_l_2471_, 4);
lean_dec(v_unused_2494_);
v_unused_2495_ = lean_ctor_get(v_l_2471_, 3);
lean_dec(v_unused_2495_);
v_unused_2496_ = lean_ctor_get(v_l_2471_, 0);
lean_dec(v_unused_2496_);
v___x_2481_ = v_l_2471_;
v_isShared_2482_ = v_isSharedCheck_2493_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_v_2479_);
lean_inc(v_k_2478_);
lean_dec(v_l_2471_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2493_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; lean_object* v___x_2485_; 
v___x_2483_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2472_, 2);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 4, v_r_2472_);
lean_ctor_set(v___x_2481_, 3, v_r_2472_);
lean_ctor_set(v___x_2481_, 2, v_v_2378_);
lean_ctor_set(v___x_2481_, 1, v_k_2377_);
lean_ctor_set(v___x_2481_, 0, v___x_2387_);
v___x_2485_ = v___x_2481_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2387_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_k_2377_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_v_2378_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v_r_2472_);
lean_ctor_set(v_reuseFailAlloc_2492_, 4, v_r_2472_);
v___x_2485_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2487_; 
lean_inc(v_r_2472_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 3, v_r_2472_);
lean_ctor_set(v___x_2476_, 0, v___x_2387_);
v___x_2487_ = v___x_2476_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2387_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_k_2473_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_v_2474_);
lean_ctor_set(v_reuseFailAlloc_2491_, 3, v_r_2472_);
lean_ctor_set(v_reuseFailAlloc_2491_, 4, v_r_2472_);
v___x_2487_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
lean_object* v___x_2489_; 
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 4, v___x_2487_);
lean_ctor_set(v___x_2382_, 3, v___x_2485_);
lean_ctor_set(v___x_2382_, 2, v_v_2479_);
lean_ctor_set(v___x_2382_, 1, v_k_2478_);
lean_ctor_set(v___x_2382_, 0, v___x_2483_);
v___x_2489_ = v___x_2382_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_k_2478_);
lean_ctor_set(v_reuseFailAlloc_2490_, 2, v_v_2479_);
lean_ctor_set(v_reuseFailAlloc_2490_, 3, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2490_, 4, v___x_2487_);
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
}
else
{
lean_object* v_r_2500_; 
v_r_2500_ = lean_ctor_get(v_impl_2386_, 4);
lean_inc(v_r_2500_);
if (lean_obj_tag(v_r_2500_) == 0)
{
lean_object* v_k_2501_; lean_object* v_v_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2513_; 
v_k_2501_ = lean_ctor_get(v_impl_2386_, 1);
v_v_2502_ = lean_ctor_get(v_impl_2386_, 2);
v_isSharedCheck_2513_ = !lean_is_exclusive(v_impl_2386_);
if (v_isSharedCheck_2513_ == 0)
{
lean_object* v_unused_2514_; lean_object* v_unused_2515_; lean_object* v_unused_2516_; 
v_unused_2514_ = lean_ctor_get(v_impl_2386_, 4);
lean_dec(v_unused_2514_);
v_unused_2515_ = lean_ctor_get(v_impl_2386_, 3);
lean_dec(v_unused_2515_);
v_unused_2516_ = lean_ctor_get(v_impl_2386_, 0);
lean_dec(v_unused_2516_);
v___x_2504_ = v_impl_2386_;
v_isShared_2505_ = v_isSharedCheck_2513_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_v_2502_);
lean_inc(v_k_2501_);
lean_dec(v_impl_2386_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2513_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2506_ = lean_unsigned_to_nat(3u);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 4, v_l_2471_);
lean_ctor_set(v___x_2504_, 2, v_v_2378_);
lean_ctor_set(v___x_2504_, 1, v_k_2377_);
lean_ctor_set(v___x_2504_, 0, v___x_2387_);
v___x_2508_ = v___x_2504_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2387_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_k_2377_);
lean_ctor_set(v_reuseFailAlloc_2512_, 2, v_v_2378_);
lean_ctor_set(v_reuseFailAlloc_2512_, 3, v_l_2471_);
lean_ctor_set(v_reuseFailAlloc_2512_, 4, v_l_2471_);
v___x_2508_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2510_; 
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 4, v_r_2500_);
lean_ctor_set(v___x_2382_, 3, v___x_2508_);
lean_ctor_set(v___x_2382_, 2, v_v_2502_);
lean_ctor_set(v___x_2382_, 1, v_k_2501_);
lean_ctor_set(v___x_2382_, 0, v___x_2506_);
v___x_2510_ = v___x_2382_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_k_2501_);
lean_ctor_set(v_reuseFailAlloc_2511_, 2, v_v_2502_);
lean_ctor_set(v_reuseFailAlloc_2511_, 3, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2511_, 4, v_r_2500_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2517_ = lean_unsigned_to_nat(2u);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 4, v_impl_2386_);
lean_ctor_set(v___x_2382_, 3, v_r_2500_);
lean_ctor_set(v___x_2382_, 0, v___x_2517_);
v___x_2519_ = v___x_2382_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_k_2377_);
lean_ctor_set(v_reuseFailAlloc_2520_, 2, v_v_2378_);
lean_ctor_set(v_reuseFailAlloc_2520_, 3, v_r_2500_);
lean_ctor_set(v_reuseFailAlloc_2520_, 4, v_impl_2386_);
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
}
else
{
lean_object* v___x_2522_; 
lean_dec(v_v_2378_);
lean_dec(v_k_2377_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 2, v_v_2374_);
lean_ctor_set(v___x_2382_, 1, v_k_2373_);
v___x_2522_ = v___x_2382_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_size_2376_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_k_2373_);
lean_ctor_set(v_reuseFailAlloc_2523_, 2, v_v_2374_);
lean_ctor_set(v_reuseFailAlloc_2523_, 3, v_l_2379_);
lean_ctor_set(v_reuseFailAlloc_2523_, 4, v_r_2380_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
else
{
lean_object* v_impl_2524_; lean_object* v___x_2525_; 
lean_dec(v_size_2376_);
v_impl_2524_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2373_, v_v_2374_, v_l_2379_);
v___x_2525_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2380_) == 0)
{
lean_object* v_size_2526_; lean_object* v_size_2527_; lean_object* v_k_2528_; lean_object* v_v_2529_; lean_object* v_l_2530_; lean_object* v_r_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v_size_2526_ = lean_ctor_get(v_r_2380_, 0);
v_size_2527_ = lean_ctor_get(v_impl_2524_, 0);
v_k_2528_ = lean_ctor_get(v_impl_2524_, 1);
v_v_2529_ = lean_ctor_get(v_impl_2524_, 2);
v_l_2530_ = lean_ctor_get(v_impl_2524_, 3);
v_r_2531_ = lean_ctor_get(v_impl_2524_, 4);
lean_inc(v_r_2531_);
v___x_2532_ = lean_unsigned_to_nat(3u);
v___x_2533_ = lean_nat_mul(v___x_2532_, v_size_2526_);
v___x_2534_ = lean_nat_dec_lt(v___x_2533_, v_size_2527_);
lean_dec(v___x_2533_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2538_; 
lean_dec(v_r_2531_);
v___x_2535_ = lean_nat_add(v___x_2525_, v_size_2527_);
v___x_2536_ = lean_nat_add(v___x_2535_, v_size_2526_);
lean_dec(v___x_2535_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 3, v_impl_2524_);
lean_ctor_set(v___x_2382_, 0, v___x_2536_);
v___x_2538_ = v___x_2382_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2536_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_k_2377_);
lean_ctor_set(v_reuseFailAlloc_2539_, 2, v_v_2378_);
lean_ctor_set(v_reuseFailAlloc_2539_, 3, v_impl_2524_);
lean_ctor_set(v_reuseFailAlloc_2539_, 4, v_r_2380_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
else
{
lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2605_; 
lean_inc(v_l_2530_);
lean_inc(v_v_2529_);
lean_inc(v_k_2528_);
lean_inc(v_size_2527_);
v_isSharedCheck_2605_ = !lean_is_exclusive(v_impl_2524_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; lean_object* v_unused_2607_; lean_object* v_unused_2608_; lean_object* v_unused_2609_; lean_object* v_unused_2610_; 
v_unused_2606_ = lean_ctor_get(v_impl_2524_, 4);
lean_dec(v_unused_2606_);
v_unused_2607_ = lean_ctor_get(v_impl_2524_, 3);
lean_dec(v_unused_2607_);
v_unused_2608_ = lean_ctor_get(v_impl_2524_, 2);
lean_dec(v_unused_2608_);
v_unused_2609_ = lean_ctor_get(v_impl_2524_, 1);
lean_dec(v_unused_2609_);
v_unused_2610_ = lean_ctor_get(v_impl_2524_, 0);
lean_dec(v_unused_2610_);
v___x_2541_ = v_impl_2524_;
v_isShared_2542_ = v_isSharedCheck_2605_;
goto v_resetjp_2540_;
}
else
{
lean_dec(v_impl_2524_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2605_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v_size_2543_; lean_object* v_size_2544_; lean_object* v_k_2545_; lean_object* v_v_2546_; lean_object* v_l_2547_; lean_object* v_r_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; 
v_size_2543_ = lean_ctor_get(v_l_2530_, 0);
v_size_2544_ = lean_ctor_get(v_r_2531_, 0);
v_k_2545_ = lean_ctor_get(v_r_2531_, 1);
v_v_2546_ = lean_ctor_get(v_r_2531_, 2);
v_l_2547_ = lean_ctor_get(v_r_2531_, 3);
v_r_2548_ = lean_ctor_get(v_r_2531_, 4);
v___x_2549_ = lean_unsigned_to_nat(2u);
v___x_2550_ = lean_nat_mul(v___x_2549_, v_size_2543_);
v___x_2551_ = lean_nat_dec_lt(v_size_2544_, v___x_2550_);
lean_dec(v___x_2550_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2580_; 
lean_inc(v_r_2548_);
lean_inc(v_l_2547_);
lean_inc(v_v_2546_);
lean_inc(v_k_2545_);
v_isSharedCheck_2580_ = !lean_is_exclusive(v_r_2531_);
if (v_isSharedCheck_2580_ == 0)
{
lean_object* v_unused_2581_; lean_object* v_unused_2582_; lean_object* v_unused_2583_; lean_object* v_unused_2584_; lean_object* v_unused_2585_; 
v_unused_2581_ = lean_ctor_get(v_r_2531_, 4);
lean_dec(v_unused_2581_);
v_unused_2582_ = lean_ctor_get(v_r_2531_, 3);
lean_dec(v_unused_2582_);
v_unused_2583_ = lean_ctor_get(v_r_2531_, 2);
lean_dec(v_unused_2583_);
v_unused_2584_ = lean_ctor_get(v_r_2531_, 1);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v_r_2531_, 0);
lean_dec(v_unused_2585_);
v___x_2553_ = v_r_2531_;
v_isShared_2554_ = v_isSharedCheck_2580_;
goto v_resetjp_2552_;
}
else
{
lean_dec(v_r_2531_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2580_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___x_2568_; lean_object* v___y_2570_; 
v___x_2555_ = lean_nat_add(v___x_2525_, v_size_2527_);
lean_dec(v_size_2527_);
v___x_2556_ = lean_nat_add(v___x_2555_, v_size_2526_);
lean_dec(v___x_2555_);
v___x_2568_ = lean_nat_add(v___x_2525_, v_size_2543_);
if (lean_obj_tag(v_l_2547_) == 0)
{
lean_object* v_size_2578_; 
v_size_2578_ = lean_ctor_get(v_l_2547_, 0);
lean_inc(v_size_2578_);
v___y_2570_ = v_size_2578_;
goto v___jp_2569_;
}
else
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_unsigned_to_nat(0u);
v___y_2570_ = v___x_2579_;
goto v___jp_2569_;
}
v___jp_2557_:
{
lean_object* v___x_2561_; lean_object* v___x_2563_; 
v___x_2561_ = lean_nat_add(v___y_2558_, v___y_2560_);
lean_dec(v___y_2560_);
lean_dec(v___y_2558_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 4, v_r_2380_);
lean_ctor_set(v___x_2553_, 3, v_r_2548_);
lean_ctor_set(v___x_2553_, 2, v_v_2378_);
lean_ctor_set(v___x_2553_, 1, v_k_2377_);
lean_ctor_set(v___x_2553_, 0, v___x_2561_);
v___x_2563_ = v___x_2553_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2561_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v_k_2377_);
lean_ctor_set(v_reuseFailAlloc_2567_, 2, v_v_2378_);
lean_ctor_set(v_reuseFailAlloc_2567_, 3, v_r_2548_);
lean_ctor_set(v_reuseFailAlloc_2567_, 4, v_r_2380_);
v___x_2563_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
lean_object* v___x_2565_; 
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 4, v___x_2563_);
lean_ctor_set(v___x_2541_, 3, v___y_2559_);
lean_ctor_set(v___x_2541_, 2, v_v_2546_);
lean_ctor_set(v___x_2541_, 1, v_k_2545_);
lean_ctor_set(v___x_2541_, 0, v___x_2556_);
v___x_2565_ = v___x_2541_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2556_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v_k_2545_);
lean_ctor_set(v_reuseFailAlloc_2566_, 2, v_v_2546_);
lean_ctor_set(v_reuseFailAlloc_2566_, 3, v___y_2559_);
lean_ctor_set(v_reuseFailAlloc_2566_, 4, v___x_2563_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
v___jp_2569_:
{
lean_object* v___x_2571_; lean_object* v___x_2573_; 
v___x_2571_ = lean_nat_add(v___x_2568_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec(v___x_2568_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 4, v_l_2547_);
lean_ctor_set(v___x_2382_, 3, v_l_2530_);
lean_ctor_set(v___x_2382_, 2, v_v_2529_);
lean_ctor_set(v___x_2382_, 1, v_k_2528_);
lean_ctor_set(v___x_2382_, 0, v___x_2571_);
v___x_2573_ = v___x_2382_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2571_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_k_2528_);
lean_ctor_set(v_reuseFailAlloc_2577_, 2, v_v_2529_);
lean_ctor_set(v_reuseFailAlloc_2577_, 3, v_l_2530_);
lean_ctor_set(v_reuseFailAlloc_2577_, 4, v_l_2547_);
v___x_2573_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
lean_object* v___x_2574_; 
v___x_2574_ = lean_nat_add(v___x_2525_, v_size_2526_);
if (lean_obj_tag(v_r_2548_) == 0)
{
lean_object* v_size_2575_; 
v_size_2575_ = lean_ctor_get(v_r_2548_, 0);
lean_inc(v_size_2575_);
v___y_2558_ = v___x_2574_;
v___y_2559_ = v___x_2573_;
v___y_2560_ = v_size_2575_;
goto v___jp_2557_;
}
else
{
lean_object* v___x_2576_; 
v___x_2576_ = lean_unsigned_to_nat(0u);
v___y_2558_ = v___x_2574_;
v___y_2559_ = v___x_2573_;
v___y_2560_ = v___x_2576_;
goto v___jp_2557_;
}
}
}
}
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2591_; 
lean_del_object(v___x_2382_);
v___x_2586_ = lean_nat_add(v___x_2525_, v_size_2527_);
lean_dec(v_size_2527_);
v___x_2587_ = lean_nat_add(v___x_2586_, v_size_2526_);
lean_dec(v___x_2586_);
v___x_2588_ = lean_nat_add(v___x_2525_, v_size_2526_);
v___x_2589_ = lean_nat_add(v___x_2588_, v_size_2544_);
lean_dec(v___x_2588_);
lean_inc_ref(v_r_2380_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 4, v_r_2380_);
lean_ctor_set(v___x_2541_, 3, v_r_2531_);
lean_ctor_set(v___x_2541_, 2, v_v_2378_);
lean_ctor_set(v___x_2541_, 1, v_k_2377_);
lean_ctor_set(v___x_2541_, 0, v___x_2589_);
v___x_2591_ = v___x_2541_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2589_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_k_2377_);
lean_ctor_set(v_reuseFailAlloc_2604_, 2, v_v_2378_);
lean_ctor_set(v_reuseFailAlloc_2604_, 3, v_r_2531_);
lean_ctor_set(v_reuseFailAlloc_2604_, 4, v_r_2380_);
v___x_2591_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
v_isSharedCheck_2598_ = !lean_is_exclusive(v_r_2380_);
if (v_isSharedCheck_2598_ == 0)
{
lean_object* v_unused_2599_; lean_object* v_unused_2600_; lean_object* v_unused_2601_; lean_object* v_unused_2602_; lean_object* v_unused_2603_; 
v_unused_2599_ = lean_ctor_get(v_r_2380_, 4);
lean_dec(v_unused_2599_);
v_unused_2600_ = lean_ctor_get(v_r_2380_, 3);
lean_dec(v_unused_2600_);
v_unused_2601_ = lean_ctor_get(v_r_2380_, 2);
lean_dec(v_unused_2601_);
v_unused_2602_ = lean_ctor_get(v_r_2380_, 1);
lean_dec(v_unused_2602_);
v_unused_2603_ = lean_ctor_get(v_r_2380_, 0);
lean_dec(v_unused_2603_);
v___x_2593_ = v_r_2380_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_dec(v_r_2380_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 4, v___x_2591_);
lean_ctor_set(v___x_2593_, 3, v_l_2530_);
lean_ctor_set(v___x_2593_, 2, v_v_2529_);
lean_ctor_set(v___x_2593_, 1, v_k_2528_);
lean_ctor_set(v___x_2593_, 0, v___x_2587_);
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_k_2528_);
lean_ctor_set(v_reuseFailAlloc_2597_, 2, v_v_2529_);
lean_ctor_set(v_reuseFailAlloc_2597_, 3, v_l_2530_);
lean_ctor_set(v_reuseFailAlloc_2597_, 4, v___x_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2611_; 
v_l_2611_ = lean_ctor_get(v_impl_2524_, 3);
if (lean_obj_tag(v_l_2611_) == 0)
{
lean_object* v_r_2612_; lean_object* v_k_2613_; lean_object* v_v_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2625_; 
lean_inc_ref(v_l_2611_);
v_r_2612_ = lean_ctor_get(v_impl_2524_, 4);
v_k_2613_ = lean_ctor_get(v_impl_2524_, 1);
v_v_2614_ = lean_ctor_get(v_impl_2524_, 2);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_impl_2524_);
if (v_isSharedCheck_2625_ == 0)
{
lean_object* v_unused_2626_; lean_object* v_unused_2627_; 
v_unused_2626_ = lean_ctor_get(v_impl_2524_, 3);
lean_dec(v_unused_2626_);
v_unused_2627_ = lean_ctor_get(v_impl_2524_, 0);
lean_dec(v_unused_2627_);
v___x_2616_ = v_impl_2524_;
v_isShared_2617_ = v_isSharedCheck_2625_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_r_2612_);
lean_inc(v_v_2614_);
lean_inc(v_k_2613_);
lean_dec(v_impl_2524_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2625_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; lean_object* v___x_2620_; 
v___x_2618_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2612_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 3, v_r_2612_);
lean_ctor_set(v___x_2616_, 2, v_v_2378_);
lean_ctor_set(v___x_2616_, 1, v_k_2377_);
lean_ctor_set(v___x_2616_, 0, v___x_2525_);
v___x_2620_ = v___x_2616_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2525_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_k_2377_);
lean_ctor_set(v_reuseFailAlloc_2624_, 2, v_v_2378_);
lean_ctor_set(v_reuseFailAlloc_2624_, 3, v_r_2612_);
lean_ctor_set(v_reuseFailAlloc_2624_, 4, v_r_2612_);
v___x_2620_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
lean_object* v___x_2622_; 
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 4, v___x_2620_);
lean_ctor_set(v___x_2382_, 3, v_l_2611_);
lean_ctor_set(v___x_2382_, 2, v_v_2614_);
lean_ctor_set(v___x_2382_, 1, v_k_2613_);
lean_ctor_set(v___x_2382_, 0, v___x_2618_);
v___x_2622_ = v___x_2382_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_k_2613_);
lean_ctor_set(v_reuseFailAlloc_2623_, 2, v_v_2614_);
lean_ctor_set(v_reuseFailAlloc_2623_, 3, v_l_2611_);
lean_ctor_set(v_reuseFailAlloc_2623_, 4, v___x_2620_);
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
else
{
lean_object* v_r_2628_; 
v_r_2628_ = lean_ctor_get(v_impl_2524_, 4);
lean_inc(v_r_2628_);
if (lean_obj_tag(v_r_2628_) == 0)
{
lean_object* v_k_2629_; lean_object* v_v_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2653_; 
lean_inc(v_l_2611_);
v_k_2629_ = lean_ctor_get(v_impl_2524_, 1);
v_v_2630_ = lean_ctor_get(v_impl_2524_, 2);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_impl_2524_);
if (v_isSharedCheck_2653_ == 0)
{
lean_object* v_unused_2654_; lean_object* v_unused_2655_; lean_object* v_unused_2656_; 
v_unused_2654_ = lean_ctor_get(v_impl_2524_, 4);
lean_dec(v_unused_2654_);
v_unused_2655_ = lean_ctor_get(v_impl_2524_, 3);
lean_dec(v_unused_2655_);
v_unused_2656_ = lean_ctor_get(v_impl_2524_, 0);
lean_dec(v_unused_2656_);
v___x_2632_ = v_impl_2524_;
v_isShared_2633_ = v_isSharedCheck_2653_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_v_2630_);
lean_inc(v_k_2629_);
lean_dec(v_impl_2524_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2653_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v_k_2634_; lean_object* v_v_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2649_; 
v_k_2634_ = lean_ctor_get(v_r_2628_, 1);
v_v_2635_ = lean_ctor_get(v_r_2628_, 2);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_r_2628_);
if (v_isSharedCheck_2649_ == 0)
{
lean_object* v_unused_2650_; lean_object* v_unused_2651_; lean_object* v_unused_2652_; 
v_unused_2650_ = lean_ctor_get(v_r_2628_, 4);
lean_dec(v_unused_2650_);
v_unused_2651_ = lean_ctor_get(v_r_2628_, 3);
lean_dec(v_unused_2651_);
v_unused_2652_ = lean_ctor_get(v_r_2628_, 0);
lean_dec(v_unused_2652_);
v___x_2637_ = v_r_2628_;
v_isShared_2638_ = v_isSharedCheck_2649_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_v_2635_);
lean_inc(v_k_2634_);
lean_dec(v_r_2628_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2649_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2639_ = lean_unsigned_to_nat(3u);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 4, v_l_2611_);
lean_ctor_set(v___x_2637_, 3, v_l_2611_);
lean_ctor_set(v___x_2637_, 2, v_v_2630_);
lean_ctor_set(v___x_2637_, 1, v_k_2629_);
lean_ctor_set(v___x_2637_, 0, v___x_2525_);
v___x_2641_ = v___x_2637_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2525_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_k_2629_);
lean_ctor_set(v_reuseFailAlloc_2648_, 2, v_v_2630_);
lean_ctor_set(v_reuseFailAlloc_2648_, 3, v_l_2611_);
lean_ctor_set(v_reuseFailAlloc_2648_, 4, v_l_2611_);
v___x_2641_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2643_; 
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 4, v_l_2611_);
lean_ctor_set(v___x_2632_, 2, v_v_2378_);
lean_ctor_set(v___x_2632_, 1, v_k_2377_);
lean_ctor_set(v___x_2632_, 0, v___x_2525_);
v___x_2643_ = v___x_2632_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2525_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v_k_2377_);
lean_ctor_set(v_reuseFailAlloc_2647_, 2, v_v_2378_);
lean_ctor_set(v_reuseFailAlloc_2647_, 3, v_l_2611_);
lean_ctor_set(v_reuseFailAlloc_2647_, 4, v_l_2611_);
v___x_2643_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
lean_object* v___x_2645_; 
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 4, v___x_2643_);
lean_ctor_set(v___x_2382_, 3, v___x_2641_);
lean_ctor_set(v___x_2382_, 2, v_v_2635_);
lean_ctor_set(v___x_2382_, 1, v_k_2634_);
lean_ctor_set(v___x_2382_, 0, v___x_2639_);
v___x_2645_ = v___x_2382_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_k_2634_);
lean_ctor_set(v_reuseFailAlloc_2646_, 2, v_v_2635_);
lean_ctor_set(v_reuseFailAlloc_2646_, 3, v___x_2641_);
lean_ctor_set(v_reuseFailAlloc_2646_, 4, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2659_; 
v___x_2657_ = lean_unsigned_to_nat(2u);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 4, v_r_2628_);
lean_ctor_set(v___x_2382_, 3, v_impl_2524_);
lean_ctor_set(v___x_2382_, 0, v___x_2657_);
v___x_2659_ = v___x_2382_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v_k_2377_);
lean_ctor_set(v_reuseFailAlloc_2660_, 2, v_v_2378_);
lean_ctor_set(v_reuseFailAlloc_2660_, 3, v_impl_2524_);
lean_ctor_set(v_reuseFailAlloc_2660_, 4, v_r_2628_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = lean_unsigned_to_nat(1u);
v___x_2663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2662_);
lean_ctor_set(v___x_2663_, 1, v_k_2373_);
lean_ctor_set(v___x_2663_, 2, v_v_2374_);
lean_ctor_set(v___x_2663_, 3, v_t_2375_);
lean_ctor_set(v___x_2663_, 4, v_t_2375_);
return v___x_2663_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(lean_object* v_k_2664_, lean_object* v_t_2665_){
_start:
{
if (lean_obj_tag(v_t_2665_) == 0)
{
lean_object* v_k_2666_; lean_object* v_l_2667_; lean_object* v_r_2668_; uint8_t v___x_2669_; 
v_k_2666_ = lean_ctor_get(v_t_2665_, 1);
v_l_2667_ = lean_ctor_get(v_t_2665_, 3);
v_r_2668_ = lean_ctor_get(v_t_2665_, 4);
v___x_2669_ = lean_nat_dec_lt(v_k_2664_, v_k_2666_);
if (v___x_2669_ == 0)
{
uint8_t v___x_2670_; 
v___x_2670_ = lean_nat_dec_eq(v_k_2664_, v_k_2666_);
if (v___x_2670_ == 0)
{
v_t_2665_ = v_r_2668_;
goto _start;
}
else
{
return v___x_2670_;
}
}
else
{
v_t_2665_ = v_l_2667_;
goto _start;
}
}
else
{
uint8_t v___x_2673_; 
v___x_2673_ = 0;
return v___x_2673_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg___boxed(lean_object* v_k_2674_, lean_object* v_t_2675_){
_start:
{
uint8_t v_res_2676_; lean_object* v_r_2677_; 
v_res_2676_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2674_, v_t_2675_);
lean_dec(v_t_2675_);
lean_dec(v_k_2674_);
v_r_2677_ = lean_box(v_res_2676_);
return v_r_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(lean_object* v_y_2678_, lean_object* v_x_2679_, size_t v_x_2680_, size_t v_x_2681_){
_start:
{
if (lean_obj_tag(v_x_2679_) == 0)
{
lean_object* v_cs_2682_; size_t v_j_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; uint8_t v___x_2686_; 
v_cs_2682_ = lean_ctor_get(v_x_2679_, 0);
v_j_2683_ = lean_usize_shift_right(v_x_2680_, v_x_2681_);
v___x_2684_ = lean_usize_to_nat(v_j_2683_);
v___x_2685_ = lean_array_get_size(v_cs_2682_);
v___x_2686_ = lean_nat_dec_lt(v___x_2684_, v___x_2685_);
if (v___x_2686_ == 0)
{
lean_dec(v___x_2684_);
lean_dec(v_y_2678_);
return v_x_2679_;
}
else
{
lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2704_; 
lean_inc_ref(v_cs_2682_);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_x_2679_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; 
v_unused_2705_ = lean_ctor_get(v_x_2679_, 0);
lean_dec(v_unused_2705_);
v___x_2688_ = v_x_2679_;
v_isShared_2689_ = v_isSharedCheck_2704_;
goto v_resetjp_2687_;
}
else
{
lean_dec(v_x_2679_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2704_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
size_t v___x_2690_; size_t v___x_2691_; size_t v___x_2692_; size_t v_i_2693_; size_t v___x_2694_; size_t v_shift_2695_; lean_object* v_v_2696_; lean_object* v___x_2697_; lean_object* v_xs_x27_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2690_ = ((size_t)1ULL);
v___x_2691_ = lean_usize_shift_left(v___x_2690_, v_x_2681_);
v___x_2692_ = lean_usize_sub(v___x_2691_, v___x_2690_);
v_i_2693_ = lean_usize_land(v_x_2680_, v___x_2692_);
v___x_2694_ = ((size_t)5ULL);
v_shift_2695_ = lean_usize_sub(v_x_2681_, v___x_2694_);
v_v_2696_ = lean_array_fget(v_cs_2682_, v___x_2684_);
v___x_2697_ = lean_box(0);
v_xs_x27_2698_ = lean_array_fset(v_cs_2682_, v___x_2684_, v___x_2697_);
v___x_2699_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2678_, v_v_2696_, v_i_2693_, v_shift_2695_);
v___x_2700_ = lean_array_fset(v_xs_x27_2698_, v___x_2684_, v___x_2699_);
lean_dec(v___x_2684_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2700_);
v___x_2702_ = v___x_2688_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
else
{
lean_object* v_vs_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; 
v_vs_2706_ = lean_ctor_get(v_x_2679_, 0);
v___x_2707_ = lean_usize_to_nat(v_x_2680_);
v___x_2708_ = lean_array_get_size(v_vs_2706_);
v___x_2709_ = lean_nat_dec_lt(v___x_2707_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_dec(v___x_2707_);
lean_dec(v_y_2678_);
return v_x_2679_;
}
else
{
lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2724_; 
lean_inc_ref(v_vs_2706_);
v_isSharedCheck_2724_ = !lean_is_exclusive(v_x_2679_);
if (v_isSharedCheck_2724_ == 0)
{
lean_object* v_unused_2725_; 
v_unused_2725_ = lean_ctor_get(v_x_2679_, 0);
lean_dec(v_unused_2725_);
v___x_2711_ = v_x_2679_;
v_isShared_2712_ = v_isSharedCheck_2724_;
goto v_resetjp_2710_;
}
else
{
lean_dec(v_x_2679_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2724_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v_v_2713_; lean_object* v___x_2714_; lean_object* v_xs_x27_2715_; lean_object* v___y_2717_; uint8_t v___x_2722_; 
v_v_2713_ = lean_array_fget(v_vs_2706_, v___x_2707_);
v___x_2714_ = lean_box(0);
v_xs_x27_2715_ = lean_array_fset(v_vs_2706_, v___x_2707_, v___x_2714_);
v___x_2722_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2678_, v_v_2713_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; 
v___x_2723_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2678_, v___x_2714_, v_v_2713_);
v___y_2717_ = v___x_2723_;
goto v___jp_2716_;
}
else
{
lean_dec(v_y_2678_);
v___y_2717_ = v_v_2713_;
goto v___jp_2716_;
}
v___jp_2716_:
{
lean_object* v___x_2718_; lean_object* v___x_2720_; 
v___x_2718_ = lean_array_fset(v_xs_x27_2715_, v___x_2707_, v___y_2717_);
lean_dec(v___x_2707_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2718_);
v___x_2720_ = v___x_2711_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2718_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2726_, lean_object* v_x_2727_, lean_object* v_x_2728_, lean_object* v_x_2729_){
_start:
{
size_t v_x_3956__boxed_2730_; size_t v_x_3957__boxed_2731_; lean_object* v_res_2732_; 
v_x_3956__boxed_2730_ = lean_unbox_usize(v_x_2728_);
lean_dec(v_x_2728_);
v_x_3957__boxed_2731_ = lean_unbox_usize(v_x_2729_);
lean_dec(v_x_2729_);
v_res_2732_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2726_, v_x_2727_, v_x_3956__boxed_2730_, v_x_3957__boxed_2731_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(lean_object* v_y_2733_, lean_object* v_t_2734_, lean_object* v_i_2735_){
_start:
{
lean_object* v_root_2736_; lean_object* v_tail_2737_; lean_object* v_size_2738_; size_t v_shift_2739_; lean_object* v_tailOff_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2767_; 
v_root_2736_ = lean_ctor_get(v_t_2734_, 0);
v_tail_2737_ = lean_ctor_get(v_t_2734_, 1);
v_size_2738_ = lean_ctor_get(v_t_2734_, 2);
v_shift_2739_ = lean_ctor_get_usize(v_t_2734_, 4);
v_tailOff_2740_ = lean_ctor_get(v_t_2734_, 3);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_t_2734_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2742_ = v_t_2734_;
v_isShared_2743_ = v_isSharedCheck_2767_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_tailOff_2740_);
lean_inc(v_size_2738_);
lean_inc(v_tail_2737_);
lean_inc(v_root_2736_);
lean_dec(v_t_2734_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2767_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
uint8_t v___x_2744_; 
v___x_2744_ = lean_nat_dec_le(v_tailOff_2740_, v_i_2735_);
if (v___x_2744_ == 0)
{
size_t v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2748_; 
v___x_2745_ = lean_usize_of_nat(v_i_2735_);
v___x_2746_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2733_, v_root_2736_, v___x_2745_, v_shift_2739_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 0, v___x_2746_);
v___x_2748_ = v___x_2742_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2746_);
lean_ctor_set(v_reuseFailAlloc_2749_, 1, v_tail_2737_);
lean_ctor_set(v_reuseFailAlloc_2749_, 2, v_size_2738_);
lean_ctor_set(v_reuseFailAlloc_2749_, 3, v_tailOff_2740_);
lean_ctor_set_usize(v_reuseFailAlloc_2749_, 4, v_shift_2739_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
else
{
lean_object* v___x_2750_; lean_object* v___x_2751_; uint8_t v___x_2752_; 
v___x_2750_ = lean_nat_sub(v_i_2735_, v_tailOff_2740_);
v___x_2751_ = lean_array_get_size(v_tail_2737_);
v___x_2752_ = lean_nat_dec_lt(v___x_2750_, v___x_2751_);
if (v___x_2752_ == 0)
{
lean_object* v___x_2754_; 
lean_dec(v___x_2750_);
lean_dec(v_y_2733_);
if (v_isShared_2743_ == 0)
{
v___x_2754_ = v___x_2742_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_root_2736_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v_tail_2737_);
lean_ctor_set(v_reuseFailAlloc_2755_, 2, v_size_2738_);
lean_ctor_set(v_reuseFailAlloc_2755_, 3, v_tailOff_2740_);
lean_ctor_set_usize(v_reuseFailAlloc_2755_, 4, v_shift_2739_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
else
{
lean_object* v_v_2756_; lean_object* v___x_2757_; lean_object* v_xs_x27_2758_; lean_object* v___y_2760_; uint8_t v___x_2765_; 
v_v_2756_ = lean_array_fget(v_tail_2737_, v___x_2750_);
v___x_2757_ = lean_box(0);
v_xs_x27_2758_ = lean_array_fset(v_tail_2737_, v___x_2750_, v___x_2757_);
v___x_2765_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2733_, v_v_2756_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2733_, v___x_2757_, v_v_2756_);
v___y_2760_ = v___x_2766_;
goto v___jp_2759_;
}
else
{
lean_dec(v_y_2733_);
v___y_2760_ = v_v_2756_;
goto v___jp_2759_;
}
v___jp_2759_:
{
lean_object* v___x_2761_; lean_object* v___x_2763_; 
v___x_2761_ = lean_array_fset(v_xs_x27_2758_, v___x_2750_, v___y_2760_);
lean_dec(v___x_2750_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 1, v___x_2761_);
v___x_2763_ = v___x_2742_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_root_2736_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v___x_2761_);
lean_ctor_set(v_reuseFailAlloc_2764_, 2, v_size_2738_);
lean_ctor_set(v_reuseFailAlloc_2764_, 3, v_tailOff_2740_);
lean_ctor_set_usize(v_reuseFailAlloc_2764_, 4, v_shift_2739_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2___boxed(lean_object* v_y_2768_, lean_object* v_t_2769_, lean_object* v_i_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2768_, v_t_2769_, v_i_2770_);
lean_dec(v_i_2770_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(lean_object* v_y_2772_, lean_object* v_x_2773_, lean_object* v_s_2774_){
_start:
{
lean_object* v_vars_2775_; lean_object* v_varMap_2776_; lean_object* v_varsHistory_2777_; lean_object* v_natToIntMap_2778_; lean_object* v_natDef_2779_; lean_object* v_dvds_2780_; lean_object* v_lowers_2781_; lean_object* v_uppers_2782_; lean_object* v_diseqs_2783_; lean_object* v_elimEqs_2784_; lean_object* v_active_2785_; lean_object* v_elimStack_2786_; lean_object* v_occurs_2787_; lean_object* v_assignment_2788_; lean_object* v_nextCnstrId_2789_; uint8_t v_caseSplits_2790_; lean_object* v_steps_2791_; lean_object* v_penalties_2792_; lean_object* v_numReorderRequests_2793_; lean_object* v_conflict_x3f_2794_; lean_object* v_diseqSplits_2795_; lean_object* v_divMod_2796_; uint8_t v_usedCommRing_2797_; lean_object* v_nonlinearOccs_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2806_; 
v_vars_2775_ = lean_ctor_get(v_s_2774_, 0);
v_varMap_2776_ = lean_ctor_get(v_s_2774_, 1);
v_varsHistory_2777_ = lean_ctor_get(v_s_2774_, 2);
v_natToIntMap_2778_ = lean_ctor_get(v_s_2774_, 3);
v_natDef_2779_ = lean_ctor_get(v_s_2774_, 4);
v_dvds_2780_ = lean_ctor_get(v_s_2774_, 5);
v_lowers_2781_ = lean_ctor_get(v_s_2774_, 6);
v_uppers_2782_ = lean_ctor_get(v_s_2774_, 7);
v_diseqs_2783_ = lean_ctor_get(v_s_2774_, 8);
v_elimEqs_2784_ = lean_ctor_get(v_s_2774_, 9);
v_active_2785_ = lean_ctor_get(v_s_2774_, 10);
v_elimStack_2786_ = lean_ctor_get(v_s_2774_, 11);
v_occurs_2787_ = lean_ctor_get(v_s_2774_, 12);
v_assignment_2788_ = lean_ctor_get(v_s_2774_, 13);
v_nextCnstrId_2789_ = lean_ctor_get(v_s_2774_, 14);
v_caseSplits_2790_ = lean_ctor_get_uint8(v_s_2774_, sizeof(void*)*22);
v_steps_2791_ = lean_ctor_get(v_s_2774_, 15);
v_penalties_2792_ = lean_ctor_get(v_s_2774_, 16);
v_numReorderRequests_2793_ = lean_ctor_get(v_s_2774_, 17);
v_conflict_x3f_2794_ = lean_ctor_get(v_s_2774_, 18);
v_diseqSplits_2795_ = lean_ctor_get(v_s_2774_, 19);
v_divMod_2796_ = lean_ctor_get(v_s_2774_, 20);
v_usedCommRing_2797_ = lean_ctor_get_uint8(v_s_2774_, sizeof(void*)*22 + 1);
v_nonlinearOccs_2798_ = lean_ctor_get(v_s_2774_, 21);
v_isSharedCheck_2806_ = !lean_is_exclusive(v_s_2774_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2800_ = v_s_2774_;
v_isShared_2801_ = v_isSharedCheck_2806_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_nonlinearOccs_2798_);
lean_inc(v_divMod_2796_);
lean_inc(v_diseqSplits_2795_);
lean_inc(v_conflict_x3f_2794_);
lean_inc(v_numReorderRequests_2793_);
lean_inc(v_penalties_2792_);
lean_inc(v_steps_2791_);
lean_inc(v_nextCnstrId_2789_);
lean_inc(v_assignment_2788_);
lean_inc(v_occurs_2787_);
lean_inc(v_elimStack_2786_);
lean_inc(v_active_2785_);
lean_inc(v_elimEqs_2784_);
lean_inc(v_diseqs_2783_);
lean_inc(v_uppers_2782_);
lean_inc(v_lowers_2781_);
lean_inc(v_dvds_2780_);
lean_inc(v_natDef_2779_);
lean_inc(v_natToIntMap_2778_);
lean_inc(v_varsHistory_2777_);
lean_inc(v_varMap_2776_);
lean_inc(v_vars_2775_);
lean_dec(v_s_2774_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2806_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2802_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2772_, v_occurs_2787_, v_x_2773_);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 12, v___x_2802_);
v___x_2804_ = v___x_2800_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_vars_2775_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_varMap_2776_);
lean_ctor_set(v_reuseFailAlloc_2805_, 2, v_varsHistory_2777_);
lean_ctor_set(v_reuseFailAlloc_2805_, 3, v_natToIntMap_2778_);
lean_ctor_set(v_reuseFailAlloc_2805_, 4, v_natDef_2779_);
lean_ctor_set(v_reuseFailAlloc_2805_, 5, v_dvds_2780_);
lean_ctor_set(v_reuseFailAlloc_2805_, 6, v_lowers_2781_);
lean_ctor_set(v_reuseFailAlloc_2805_, 7, v_uppers_2782_);
lean_ctor_set(v_reuseFailAlloc_2805_, 8, v_diseqs_2783_);
lean_ctor_set(v_reuseFailAlloc_2805_, 9, v_elimEqs_2784_);
lean_ctor_set(v_reuseFailAlloc_2805_, 10, v_active_2785_);
lean_ctor_set(v_reuseFailAlloc_2805_, 11, v_elimStack_2786_);
lean_ctor_set(v_reuseFailAlloc_2805_, 12, v___x_2802_);
lean_ctor_set(v_reuseFailAlloc_2805_, 13, v_assignment_2788_);
lean_ctor_set(v_reuseFailAlloc_2805_, 14, v_nextCnstrId_2789_);
lean_ctor_set(v_reuseFailAlloc_2805_, 15, v_steps_2791_);
lean_ctor_set(v_reuseFailAlloc_2805_, 16, v_penalties_2792_);
lean_ctor_set(v_reuseFailAlloc_2805_, 17, v_numReorderRequests_2793_);
lean_ctor_set(v_reuseFailAlloc_2805_, 18, v_conflict_x3f_2794_);
lean_ctor_set(v_reuseFailAlloc_2805_, 19, v_diseqSplits_2795_);
lean_ctor_set(v_reuseFailAlloc_2805_, 20, v_divMod_2796_);
lean_ctor_set(v_reuseFailAlloc_2805_, 21, v_nonlinearOccs_2798_);
lean_ctor_set_uint8(v_reuseFailAlloc_2805_, sizeof(void*)*22, v_caseSplits_2790_);
lean_ctor_set_uint8(v_reuseFailAlloc_2805_, sizeof(void*)*22 + 1, v_usedCommRing_2797_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed(lean_object* v_y_2807_, lean_object* v_x_2808_, lean_object* v_s_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(v_y_2807_, v_x_2808_, v_s_2809_);
lean_dec(v_x_2808_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(lean_object* v_x_2811_, lean_object* v_y_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_){
_start:
{
lean_object* v___f_2816_; lean_object* v___x_2817_; 
lean_inc(v_x_2811_);
lean_inc(v_y_2812_);
v___f_2816_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2816_, 0, v_y_2812_);
lean_closure_set(v___f_2816_, 1, v_x_2811_);
v___x_2817_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2811_, v_a_2813_, v_a_2814_);
lean_dec(v_x_2811_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2829_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2820_ = v___x_2817_;
v_isShared_2821_ = v_isSharedCheck_2829_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2817_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2829_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
uint8_t v___x_2822_; 
v___x_2822_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2812_, v_a_2818_);
lean_dec(v_a_2818_);
lean_dec(v_y_2812_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
lean_del_object(v___x_2820_);
v___x_2823_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2824_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2823_, v___f_2816_, v_a_2813_);
return v___x_2824_;
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2827_; 
lean_dec_ref(v___f_2816_);
v___x_2825_ = lean_box(0);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v___x_2825_);
v___x_2827_ = v___x_2820_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec_ref(v___f_2816_);
lean_dec(v_y_2812_);
v_a_2830_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2817_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2817_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___boxed(lean_object* v_x_2838_, lean_object* v_y_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2838_, v_y_2839_, v_a_2840_, v_a_2841_);
lean_dec_ref(v_a_2841_);
lean_dec(v_a_2840_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc(lean_object* v_x_2844_, lean_object* v_y_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2844_, v_y_2845_, v_a_2846_, v_a_2854_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___boxed(lean_object* v_x_2858_, lean_object* v_y_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc(v_x_2858_, v_y_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
lean_dec(v_a_2869_);
lean_dec_ref(v_a_2868_);
lean_dec(v_a_2867_);
lean_dec_ref(v_a_2866_);
lean_dec(v_a_2865_);
lean_dec_ref(v_a_2864_);
lean_dec(v_a_2863_);
lean_dec_ref(v_a_2862_);
lean_dec(v_a_2861_);
lean_dec(v_a_2860_);
return v_res_2871_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(lean_object* v_00_u03b2_2872_, lean_object* v_k_2873_, lean_object* v_t_2874_){
_start:
{
uint8_t v___x_2875_; 
v___x_2875_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2873_, v_t_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2876_, lean_object* v_k_2877_, lean_object* v_t_2878_){
_start:
{
uint8_t v_res_2879_; lean_object* v_r_2880_; 
v_res_2879_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(v_00_u03b2_2876_, v_k_2877_, v_t_2878_);
lean_dec(v_t_2878_);
lean_dec(v_k_2877_);
v_r_2880_ = lean_box(v_res_2879_);
return v_r_2880_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1(lean_object* v_00_u03b2_2881_, lean_object* v_k_2882_, lean_object* v_v_2883_, lean_object* v_t_2884_, lean_object* v_hl_2885_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2882_, v_v_2883_, v_t_2884_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(lean_object* v_y_2887_, lean_object* v_p_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_){
_start:
{
if (lean_obj_tag(v_p_2888_) == 1)
{
lean_object* v_v_2892_; lean_object* v_p_2893_; lean_object* v___x_2894_; 
v_v_2892_ = lean_ctor_get(v_p_2888_, 1);
lean_inc(v_v_2892_);
v_p_2893_ = lean_ctor_get(v_p_2888_, 2);
lean_inc_ref(v_p_2893_);
lean_dec_ref_known(v_p_2888_, 3);
lean_inc(v_y_2887_);
v___x_2894_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_v_2892_, v_y_2887_, v_a_2889_, v_a_2890_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_dec_ref_known(v___x_2894_, 1);
v_p_2888_ = v_p_2893_;
goto _start;
}
else
{
lean_dec_ref(v_p_2893_);
lean_dec(v_y_2887_);
return v___x_2894_;
}
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
lean_dec_ref(v_p_2888_);
lean_dec(v_y_2887_);
v___x_2896_ = lean_box(0);
v___x_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
return v___x_2897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg___boxed(lean_object* v_y_2898_, lean_object* v_p_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2898_, v_p_2899_, v_a_2900_, v_a_2901_);
lean_dec_ref(v_a_2901_);
lean_dec(v_a_2900_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(lean_object* v_y_2904_, lean_object* v_p_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2904_, v_p_2905_, v_a_2906_, v_a_2914_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___boxed(lean_object* v_y_2918_, lean_object* v_p_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(v_y_2918_, v_p_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
lean_dec(v_a_2927_);
lean_dec_ref(v_a_2926_);
lean_dec(v_a_2925_);
lean_dec_ref(v_a_2924_);
lean_dec(v_a_2923_);
lean_dec_ref(v_a_2922_);
lean_dec(v_a_2921_);
lean_dec(v_a_2920_);
return v_res_2931_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = ((lean_object*)(l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__0));
v___x_2934_ = l_Lean_stringToMessageData(v___x_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg(lean_object* v_p_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
if (lean_obj_tag(v_p_2935_) == 1)
{
lean_object* v_v_2942_; lean_object* v_p_2943_; lean_object* v___x_2944_; 
v_v_2942_ = lean_ctor_get(v_p_2935_, 1);
lean_inc(v_v_2942_);
v_p_2943_ = lean_ctor_get(v_p_2935_, 2);
lean_inc_ref(v_p_2943_);
lean_dec_ref_known(v_p_2935_, 3);
v___x_2944_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_v_2942_, v_p_2943_, v_a_2936_, v_a_2939_);
return v___x_2944_;
}
else
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
lean_dec_ref(v_p_2935_);
v___x_2945_ = lean_obj_once(&l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1, &l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1_once, _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1);
v___x_2946_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2945_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
return v___x_2946_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg___boxed(lean_object* v_p_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs(lean_object* v_p_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2955_, v_a_2956_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___boxed(lean_object* v_p_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Int_Internal_Linear_Poly_updateOccs(v_p_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_);
lean_dec(v_a_2978_);
lean_dec_ref(v_a_2977_);
lean_dec(v_a_2976_);
lean_dec_ref(v_a_2975_);
lean_dec(v_a_2974_);
lean_dec_ref(v_a_2973_);
lean_dec(v_a_2972_);
lean_dec_ref(v_a_2971_);
lean_dec(v_a_2970_);
lean_dec(v_a_2969_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go_spec__0(lean_object* v_a_2981_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Rat_ofInt(v_a_2981_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(lean_object* v_a_2983_, lean_object* v_v_2984_, lean_object* v_a_2985_){
_start:
{
if (lean_obj_tag(v_a_2985_) == 0)
{
lean_object* v_k_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2995_; 
v_k_2986_ = lean_ctor_get(v_a_2985_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_a_2985_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2988_ = v_a_2985_;
v_isShared_2989_ = v_isSharedCheck_2995_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_k_2986_);
lean_dec(v_a_2985_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2995_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2990_ = l_Rat_ofInt(v_k_2986_);
v___x_2991_ = l_Rat_add(v_v_2984_, v___x_2990_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set_tag(v___x_2988_, 1);
lean_ctor_set(v___x_2988_, 0, v___x_2991_);
v___x_2993_ = v___x_2988_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
else
{
lean_object* v_k_2996_; lean_object* v_v_2997_; lean_object* v_p_2998_; lean_object* v_size_2999_; uint8_t v___x_3000_; 
v_k_2996_ = lean_ctor_get(v_a_2985_, 0);
lean_inc(v_k_2996_);
v_v_2997_ = lean_ctor_get(v_a_2985_, 1);
lean_inc(v_v_2997_);
v_p_2998_ = lean_ctor_get(v_a_2985_, 2);
lean_inc_ref(v_p_2998_);
lean_dec_ref_known(v_a_2985_, 3);
v_size_2999_ = lean_ctor_get(v_a_2983_, 2);
v___x_3000_ = lean_nat_dec_lt(v_v_2997_, v_size_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
lean_dec_ref(v_p_2998_);
lean_dec(v_v_2997_);
lean_dec(v_k_2996_);
lean_dec_ref(v_v_2984_);
v___x_3001_ = lean_box(0);
return v___x_3001_;
}
else
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3002_ = l_instInhabitedRat;
v___x_3003_ = l_Rat_ofInt(v_k_2996_);
v___x_3004_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3002_, v_a_2983_, v_v_2997_);
lean_dec(v_v_2997_);
v___x_3005_ = l_Rat_mul(v___x_3003_, v___x_3004_);
lean_dec_ref(v___x_3003_);
v___x_3006_ = l_Rat_add(v_v_2984_, v___x_3005_);
v_v_2984_ = v___x_3006_;
v_a_2985_ = v_p_2998_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go___boxed(lean_object* v_a_3008_, lean_object* v_v_3009_, lean_object* v_a_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_a_3008_, v_v_3009_, v_a_3010_);
lean_dec_ref(v_a_3008_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(lean_object* v_a_3012_){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = lean_nat_to_int(v_a_3012_);
v___x_3014_ = l_Rat_ofInt(v___x_3013_);
return v___x_3014_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = lean_unsigned_to_nat(0u);
v___x_3016_ = l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(v___x_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg(lean_object* v_p_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3018_, v_a_3019_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3032_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3024_ = v___x_3021_;
v_isShared_3025_ = v_isSharedCheck_3032_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3032_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v_assignment_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3030_; 
v_assignment_3026_ = lean_ctor_get(v_a_3022_, 13);
lean_inc_ref(v_assignment_3026_);
lean_dec(v_a_3022_);
v___x_3027_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_3028_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_assignment_3026_, v___x_3027_, v_p_3017_);
lean_dec_ref(v_assignment_3026_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3028_);
v___x_3030_ = v___x_3024_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec_ref(v_p_3017_);
v_a_3033_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3021_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3021_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg___boxed(lean_object* v_p_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3041_, v_a_3042_, v_a_3043_);
lean_dec_ref(v_a_3043_);
lean_dec(v_a_3042_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f(lean_object* v_p_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3046_, v_a_3047_, v_a_3055_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___boxed(lean_object* v_p_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Int_Internal_Linear_Poly_eval_x3f(v_p_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec(v_a_3060_);
return v_res_3071_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(lean_object* v_c_3072_){
_start:
{
lean_object* v_p_3073_; uint8_t v___x_3074_; 
v_p_3073_ = lean_ctor_get(v_c_3072_, 0);
v___x_3074_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_3073_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat___boxed(lean_object* v_c_3075_){
_start:
{
uint8_t v_res_3076_; lean_object* v_r_3077_; 
v_res_3076_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(v_c_3075_);
lean_dec_ref(v_c_3075_);
v_r_3077_ = lean_box(v_res_3076_);
return v_r_3077_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(lean_object* v_c_3078_){
_start:
{
lean_object* v_d_3079_; lean_object* v_p_3080_; uint8_t v___x_3081_; 
v_d_3079_ = lean_ctor_get(v_c_3078_, 0);
lean_inc(v_d_3079_);
v_p_3080_ = lean_ctor_get(v_c_3078_, 1);
lean_inc_ref(v_p_3080_);
lean_dec_ref(v_c_3078_);
v___x_3081_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_3079_, v_p_3080_);
lean_dec_ref(v_p_3080_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat___boxed(lean_object* v_c_3082_){
_start:
{
uint8_t v_res_3083_; lean_object* v_r_3084_; 
v_res_3083_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(v_c_3082_);
v_r_3084_ = lean_box(v_res_3083_);
return v_r_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object* v_c_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_){
_start:
{
lean_object* v_d_3089_; lean_object* v_p_3090_; lean_object* v___x_3091_; 
v_d_3089_ = lean_ctor_get(v_c_3085_, 0);
lean_inc(v_d_3089_);
v_p_3090_ = lean_ctor_get(v_c_3085_, 1);
lean_inc_ref(v_p_3090_);
lean_dec_ref(v_c_3085_);
v___x_3091_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3090_, v_a_3086_, v_a_3087_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3119_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3094_ = v___x_3091_;
v_isShared_3095_ = v_isSharedCheck_3119_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3091_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3119_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
if (lean_obj_tag(v_a_3092_) == 1)
{
lean_object* v_val_3096_; lean_object* v_num_3097_; lean_object* v_den_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v_val_3096_ = lean_ctor_get(v_a_3092_, 0);
lean_inc(v_val_3096_);
lean_dec_ref_known(v_a_3092_, 1);
v_num_3097_ = lean_ctor_get(v_val_3096_, 0);
lean_inc(v_num_3097_);
v_den_3098_ = lean_ctor_get(v_val_3096_, 1);
lean_inc(v_den_3098_);
lean_dec(v_val_3096_);
v___x_3099_ = lean_unsigned_to_nat(1u);
v___x_3100_ = lean_nat_dec_eq(v_den_3098_, v___x_3099_);
lean_dec(v_den_3098_);
if (v___x_3100_ == 0)
{
uint8_t v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3104_; 
lean_dec(v_num_3097_);
lean_dec(v_d_3089_);
v___x_3101_ = 0;
v___x_3102_ = lean_box(v___x_3101_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3102_);
v___x_3104_ = v___x_3094_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; uint8_t v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3112_; 
v___x_3106_ = lean_int_emod(v_num_3097_, v_d_3089_);
lean_dec(v_d_3089_);
lean_dec(v_num_3097_);
v___x_3107_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_3108_ = lean_int_dec_eq(v___x_3106_, v___x_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = l_Lean_Bool_toLBool(v___x_3108_);
v___x_3110_ = lean_box(v___x_3109_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3110_);
v___x_3112_ = v___x_3094_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3110_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
else
{
uint8_t v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3117_; 
lean_dec(v_a_3092_);
lean_dec(v_d_3089_);
v___x_3114_ = 2;
v___x_3115_ = lean_box(v___x_3114_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3115_);
v___x_3117_ = v___x_3094_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3115_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec(v_d_3089_);
v_a_3120_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3091_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3091_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg___boxed(lean_object* v_c_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_3128_, v_a_3129_, v_a_3130_);
lean_dec_ref(v_a_3130_);
lean_dec(v_a_3129_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(lean_object* v_c_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_3133_, v_a_3134_, v_a_3142_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___boxed(lean_object* v_c_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(v_c_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_);
lean_dec(v_a_3156_);
lean_dec_ref(v_a_3155_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
lean_dec_ref(v_a_3151_);
lean_dec(v_a_3150_);
lean_dec_ref(v_a_3149_);
lean_dec(v_a_3148_);
lean_dec(v_a_3147_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg(lean_object* v_p_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v___x_3163_; 
v___x_3163_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3159_, v_a_3160_, v_a_3161_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3181_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3166_ = v___x_3163_;
v_isShared_3167_ = v_isSharedCheck_3181_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3163_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3181_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
if (lean_obj_tag(v_a_3164_) == 1)
{
lean_object* v_val_3168_; lean_object* v___x_3169_; uint8_t v___x_3170_; uint8_t v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3174_; 
v_val_3168_ = lean_ctor_get(v_a_3164_, 0);
lean_inc(v_val_3168_);
lean_dec_ref_known(v_a_3164_, 1);
v___x_3169_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_3170_ = l_Rat_instDecidableLe(v_val_3168_, v___x_3169_);
v___x_3171_ = l_Lean_Bool_toLBool(v___x_3170_);
v___x_3172_ = lean_box(v___x_3171_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 0, v___x_3172_);
v___x_3174_ = v___x_3166_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3172_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
else
{
uint8_t v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3179_; 
lean_dec(v_a_3164_);
v___x_3176_ = 2;
v___x_3177_ = lean_box(v___x_3176_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 0, v___x_3177_);
v___x_3179_ = v___x_3166_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v___x_3177_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
v_a_3182_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3163_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3163_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg___boxed(lean_object* v_p_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_3190_, v_a_3191_, v_a_3192_);
lean_dec_ref(v_a_3192_);
lean_dec(v_a_3191_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe(lean_object* v_p_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_3195_, v_a_3196_, v_a_3204_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___boxed(lean_object* v_p_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Int_Internal_Linear_Poly_satisfiedLe(v_p_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_);
lean_dec(v_a_3218_);
lean_dec_ref(v_a_3217_);
lean_dec(v_a_3216_);
lean_dec_ref(v_a_3215_);
lean_dec(v_a_3214_);
lean_dec_ref(v_a_3213_);
lean_dec(v_a_3212_);
lean_dec_ref(v_a_3211_);
lean_dec(v_a_3210_);
lean_dec(v_a_3209_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(lean_object* v_c_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_){
_start:
{
lean_object* v_p_3225_; lean_object* v___x_3226_; 
v_p_3225_ = lean_ctor_get(v_c_3221_, 0);
lean_inc_ref(v_p_3225_);
lean_dec_ref(v_c_3221_);
v___x_3226_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_3225_, v_a_3222_, v_a_3223_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg___boxed(lean_object* v_c_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_3227_, v_a_3228_, v_a_3229_);
lean_dec_ref(v_a_3229_);
lean_dec(v_a_3228_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(lean_object* v_c_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_){
_start:
{
lean_object* v___x_3244_; 
v___x_3244_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_3232_, v_a_3233_, v_a_3241_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___boxed(lean_object* v_c_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(v_c_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_);
lean_dec(v_a_3255_);
lean_dec_ref(v_a_3254_);
lean_dec(v_a_3253_);
lean_dec_ref(v_a_3252_);
lean_dec(v_a_3251_);
lean_dec_ref(v_a_3250_);
lean_dec(v_a_3249_);
lean_dec_ref(v_a_3248_);
lean_dec(v_a_3247_);
lean_dec(v_a_3246_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(lean_object* v_c_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_){
_start:
{
lean_object* v_p_3262_; lean_object* v___x_3263_; 
v_p_3262_ = lean_ctor_get(v_c_3258_, 0);
lean_inc_ref(v_p_3262_);
lean_dec_ref(v_c_3258_);
v___x_3263_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3262_, v_a_3259_, v_a_3260_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3283_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3266_ = v___x_3263_;
v_isShared_3267_ = v_isSharedCheck_3283_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3263_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3283_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
uint8_t v___y_3269_; 
if (lean_obj_tag(v_a_3264_) == 1)
{
lean_object* v_val_3275_; lean_object* v___x_3276_; uint8_t v___x_3277_; 
v_val_3275_ = lean_ctor_get(v_a_3264_, 0);
lean_inc(v_val_3275_);
lean_dec_ref_known(v_a_3264_, 1);
v___x_3276_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_3277_ = l_instDecidableEqRat_decEq(v_val_3275_, v___x_3276_);
lean_dec(v_val_3275_);
if (v___x_3277_ == 0)
{
uint8_t v___x_3278_; 
v___x_3278_ = 1;
v___y_3269_ = v___x_3278_;
goto v___jp_3268_;
}
else
{
uint8_t v___x_3279_; 
v___x_3279_ = 0;
v___y_3269_ = v___x_3279_;
goto v___jp_3268_;
}
}
else
{
uint8_t v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
lean_del_object(v___x_3266_);
lean_dec(v_a_3264_);
v___x_3280_ = 2;
v___x_3281_ = lean_box(v___x_3280_);
v___x_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
return v___x_3282_;
}
v___jp_3268_:
{
uint8_t v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3273_; 
v___x_3270_ = l_Lean_Bool_toLBool(v___y_3269_);
v___x_3271_ = lean_box(v___x_3270_);
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 0, v___x_3271_);
v___x_3273_ = v___x_3266_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3271_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
v_a_3284_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3263_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3263_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg___boxed(lean_object* v_c_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_3292_, v_a_3293_, v_a_3294_);
lean_dec_ref(v_a_3294_);
lean_dec(v_a_3293_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(lean_object* v_c_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_3297_, v_a_3298_, v_a_3306_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___boxed(lean_object* v_c_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(v_c_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
lean_dec(v_a_3318_);
lean_dec_ref(v_a_3317_);
lean_dec(v_a_3316_);
lean_dec_ref(v_a_3315_);
lean_dec(v_a_3314_);
lean_dec_ref(v_a_3313_);
lean_dec(v_a_3312_);
lean_dec(v_a_3311_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(lean_object* v_c_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v_p_3327_; lean_object* v___x_3328_; 
v_p_3327_ = lean_ctor_get(v_c_3323_, 0);
lean_inc_ref(v_p_3327_);
lean_dec_ref(v_c_3323_);
v___x_3328_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3327_, v_a_3324_, v_a_3325_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3346_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3331_ = v___x_3328_;
v_isShared_3332_ = v_isSharedCheck_3346_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3328_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3346_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
if (lean_obj_tag(v_a_3329_) == 1)
{
lean_object* v_val_3333_; lean_object* v___x_3334_; uint8_t v___x_3335_; uint8_t v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3339_; 
v_val_3333_ = lean_ctor_get(v_a_3329_, 0);
lean_inc(v_val_3333_);
lean_dec_ref_known(v_a_3329_, 1);
v___x_3334_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_3335_ = l_instDecidableEqRat_decEq(v_val_3333_, v___x_3334_);
lean_dec(v_val_3333_);
v___x_3336_ = l_Lean_Bool_toLBool(v___x_3335_);
v___x_3337_ = lean_box(v___x_3336_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3337_);
v___x_3339_ = v___x_3331_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
else
{
uint8_t v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
lean_dec(v_a_3329_);
v___x_3341_ = 2;
v___x_3342_ = lean_box(v___x_3341_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3342_);
v___x_3344_ = v___x_3331_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
v_a_3347_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3328_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3328_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg___boxed(lean_object* v_c_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_3355_, v_a_3356_, v_a_3357_);
lean_dec_ref(v_a_3357_);
lean_dec(v_a_3356_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(lean_object* v_c_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v___x_3372_; 
v___x_3372_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_3360_, v_a_3361_, v_a_3369_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___boxed(lean_object* v_c_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(v_c_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
lean_dec(v_a_3383_);
lean_dec_ref(v_a_3382_);
lean_dec(v_a_3381_);
lean_dec_ref(v_a_3380_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
lean_dec(v_a_3377_);
lean_dec_ref(v_a_3376_);
lean_dec(v_a_3375_);
lean_dec(v_a_3374_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg(lean_object* v_p_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_){
_start:
{
if (lean_obj_tag(v_p_3386_) == 0)
{
lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3397_; 
v_isSharedCheck_3397_ = !lean_is_exclusive(v_p_3386_);
if (v_isSharedCheck_3397_ == 0)
{
lean_object* v_unused_3398_; 
v_unused_3398_ = lean_ctor_get(v_p_3386_, 0);
lean_dec(v_unused_3398_);
v___x_3391_ = v_p_3386_;
v_isShared_3392_ = v_isSharedCheck_3397_;
goto v_resetjp_3390_;
}
else
{
lean_dec(v_p_3386_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3397_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3393_; lean_object* v___x_3395_; 
v___x_3393_ = lean_box(0);
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 0, v___x_3393_);
v___x_3395_ = v___x_3391_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3393_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
else
{
lean_object* v_k_3399_; lean_object* v_v_3400_; lean_object* v_p_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v_k_3399_ = lean_ctor_get(v_p_3386_, 0);
lean_inc(v_k_3399_);
v_v_3400_ = lean_ctor_get(v_p_3386_, 1);
lean_inc(v_v_3400_);
v_p_3401_ = lean_ctor_get(v_p_3386_, 2);
lean_inc_ref(v_p_3401_);
lean_dec_ref_known(v_p_3386_, 3);
v___x_3402_ = lean_box(0);
v___x_3403_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3429_; 
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3406_ = v___x_3403_;
v_isShared_3407_ = v_isSharedCheck_3429_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3403_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3429_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___y_3409_; lean_object* v_elimEqs_3424_; lean_object* v_size_3425_; uint8_t v___x_3426_; 
v_elimEqs_3424_ = lean_ctor_get(v_a_3404_, 9);
lean_inc_ref(v_elimEqs_3424_);
lean_dec(v_a_3404_);
v_size_3425_ = lean_ctor_get(v_elimEqs_3424_, 2);
v___x_3426_ = lean_nat_dec_lt(v_v_3400_, v_size_3425_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
lean_dec_ref(v_elimEqs_3424_);
v___x_3427_ = l_outOfBounds___redArg(v___x_3402_);
v___y_3409_ = v___x_3427_;
goto v___jp_3408_;
}
else
{
lean_object* v___x_3428_; 
v___x_3428_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3402_, v_elimEqs_3424_, v_v_3400_);
lean_dec_ref(v_elimEqs_3424_);
v___y_3409_ = v___x_3428_;
goto v___jp_3408_;
}
v___jp_3408_:
{
if (lean_obj_tag(v___y_3409_) == 1)
{
lean_object* v_val_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3422_; 
lean_dec_ref(v_p_3401_);
v_val_3410_ = lean_ctor_get(v___y_3409_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___y_3409_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3412_ = v___y_3409_;
v_isShared_3413_ = v_isSharedCheck_3422_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_val_3410_);
lean_dec(v___y_3409_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3422_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3414_, 0, v_v_3400_);
lean_ctor_set(v___x_3414_, 1, v_val_3410_);
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v_k_3399_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 0, v___x_3415_);
v___x_3417_ = v___x_3412_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3415_);
v___x_3417_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
lean_object* v___x_3419_; 
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 0, v___x_3417_);
v___x_3419_ = v___x_3406_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
else
{
lean_dec(v___y_3409_);
lean_del_object(v___x_3406_);
lean_dec(v_v_3400_);
lean_dec(v_k_3399_);
v_p_3386_ = v_p_3401_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec_ref(v_p_3401_);
lean_dec(v_v_3400_);
lean_dec(v_k_3399_);
v_a_3430_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3403_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3403_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg___boxed(lean_object* v_p_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_3438_, v_a_3439_, v_a_3440_);
lean_dec_ref(v_a_3440_);
lean_dec(v_a_3439_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst(lean_object* v_p_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_){
_start:
{
lean_object* v___x_3455_; 
v___x_3455_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_3443_, v_a_3444_, v_a_3452_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___boxed(lean_object* v_p_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l_Int_Internal_Linear_Poly_findVarToSubst(v_p_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_);
lean_dec(v_a_3466_);
lean_dec_ref(v_a_3465_);
lean_dec(v_a_3464_);
lean_dec_ref(v_a_3463_);
lean_dec(v_a_3462_);
lean_dec_ref(v_a_3461_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
lean_dec(v_a_3458_);
lean_dec(v_a_3457_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(lean_object* v_pred_3469_){
_start:
{
lean_object* v_c_u2081_3470_; lean_object* v_c_u2082_3471_; uint8_t v_left_3472_; lean_object* v_c_u2083_x3f_3473_; lean_object* v_p_3474_; lean_object* v_p_3475_; lean_object* v_a_3476_; lean_object* v_b_3477_; 
v_c_u2081_3470_ = lean_ctor_get(v_pred_3469_, 0);
v_c_u2082_3471_ = lean_ctor_get(v_pred_3469_, 1);
v_left_3472_ = lean_ctor_get_uint8(v_pred_3469_, sizeof(void*)*3);
v_c_u2083_x3f_3473_ = lean_ctor_get(v_pred_3469_, 2);
v_p_3474_ = lean_ctor_get(v_c_u2081_3470_, 0);
v_p_3475_ = lean_ctor_get(v_c_u2082_3471_, 0);
v_a_3476_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3474_);
v_b_3477_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3475_);
if (lean_obj_tag(v_c_u2083_x3f_3473_) == 0)
{
if (v_left_3472_ == 0)
{
lean_object* v___x_3478_; 
lean_dec(v_a_3476_);
v___x_3478_ = lean_nat_abs(v_b_3477_);
lean_dec(v_b_3477_);
return v___x_3478_;
}
else
{
lean_object* v___x_3479_; 
lean_dec(v_b_3477_);
v___x_3479_ = lean_nat_abs(v_a_3476_);
lean_dec(v_a_3476_);
return v___x_3479_;
}
}
else
{
lean_object* v_val_3480_; lean_object* v_d_3481_; lean_object* v_p_3482_; lean_object* v_c_3483_; 
v_val_3480_ = lean_ctor_get(v_c_u2083_x3f_3473_, 0);
v_d_3481_ = lean_ctor_get(v_val_3480_, 0);
v_p_3482_ = lean_ctor_get(v_val_3480_, 1);
v_c_3483_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3482_);
if (v_left_3472_ == 0)
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
lean_dec(v_a_3476_);
v___x_3484_ = lean_int_mul(v_b_3477_, v_d_3481_);
v___x_3485_ = l_Int_gcd(v___x_3484_, v_c_3483_);
lean_dec(v_c_3483_);
v___x_3486_ = lean_nat_to_int(v___x_3485_);
v___x_3487_ = lean_int_ediv(v___x_3484_, v___x_3486_);
lean_dec(v___x_3486_);
lean_dec(v___x_3484_);
v___x_3488_ = l_Int_lcm(v_b_3477_, v___x_3487_);
lean_dec(v___x_3487_);
lean_dec(v_b_3477_);
return v___x_3488_;
}
else
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
lean_dec(v_b_3477_);
v___x_3489_ = lean_int_mul(v_a_3476_, v_d_3481_);
v___x_3490_ = l_Int_gcd(v___x_3489_, v_c_3483_);
lean_dec(v_c_3483_);
v___x_3491_ = lean_nat_to_int(v___x_3490_);
v___x_3492_ = lean_int_ediv(v___x_3489_, v___x_3491_);
lean_dec(v___x_3491_);
lean_dec(v___x_3489_);
v___x_3493_ = l_Int_lcm(v_a_3476_, v___x_3492_);
lean_dec(v___x_3492_);
lean_dec(v_a_3476_);
return v___x_3493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases___boxed(lean_object* v_pred_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(v_pred_3494_);
lean_dec_ref(v_pred_3494_);
return v_res_3495_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3497_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0));
v___x_3498_ = l_Lean_stringToMessageData(v___x_3497_);
return v___x_3498_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4(void){
_start:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3));
v___x_3503_ = l_Lean_MessageData_ofFormat(v___x_3502_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(lean_object* v_pred_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
lean_object* v_c_u2081_3508_; lean_object* v_c_u2082_3509_; lean_object* v_c_u2083_x3f_3510_; lean_object* v___x_3511_; 
v_c_u2081_3508_ = lean_ctor_get(v_pred_3504_, 0);
lean_inc_ref(v_c_u2081_3508_);
v_c_u2082_3509_ = lean_ctor_get(v_pred_3504_, 1);
lean_inc_ref(v_c_u2082_3509_);
v_c_u2083_x3f_3510_ = lean_ctor_get(v_pred_3504_, 2);
lean_inc(v_c_u2083_x3f_3510_);
lean_dec_ref(v_pred_3504_);
v___x_3511_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3508_, v_a_3505_, v_a_3506_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3513_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v___x_3511_, 1);
v___x_3513_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3509_, v_a_3505_, v_a_3506_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3532_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3516_ = v___x_3513_;
v_isShared_3517_ = v_isSharedCheck_3532_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3513_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3532_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v_____do__lift_3519_; 
if (lean_obj_tag(v_c_u2083_x3f_3510_) == 1)
{
lean_object* v_val_3528_; lean_object* v___x_3529_; 
v_val_3528_ = lean_ctor_get(v_c_u2083_x3f_3510_, 0);
lean_inc(v_val_3528_);
lean_dec_ref_known(v_c_u2083_x3f_3510_, 1);
v___x_3529_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_val_3528_, v_a_3505_, v_a_3506_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3530_);
lean_dec_ref_known(v___x_3529_, 1);
v_____do__lift_3519_ = v_a_3530_;
goto v___jp_3518_;
}
else
{
lean_del_object(v___x_3516_);
lean_dec(v_a_3514_);
lean_dec(v_a_3512_);
return v___x_3529_;
}
}
else
{
lean_object* v___x_3531_; 
lean_dec(v_c_u2083_x3f_3510_);
v___x_3531_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4);
v_____do__lift_3519_ = v___x_3531_;
goto v___jp_3518_;
}
v___jp_3518_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3520_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3521_, 0, v_a_3512_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
v___x_3522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
lean_ctor_set(v___x_3522_, 1, v_a_3514_);
v___x_3523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3522_);
lean_ctor_set(v___x_3523_, 1, v___x_3520_);
v___x_3524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
lean_ctor_set(v___x_3524_, 1, v_____do__lift_3519_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 0, v___x_3524_);
v___x_3526_ = v___x_3516_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
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
else
{
lean_dec(v_a_3512_);
lean_dec(v_c_u2083_x3f_3510_);
return v___x_3513_;
}
}
else
{
lean_dec(v_c_u2083_x3f_3510_);
lean_dec_ref(v_c_u2082_3509_);
return v___x_3511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___boxed(lean_object* v_pred_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_3533_, v_a_3534_, v_a_3535_);
lean_dec_ref(v_a_3535_);
lean_dec(v_a_3534_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(lean_object* v_pred_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_3538_, v_a_3539_, v_a_3547_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___boxed(lean_object* v_pred_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(v_pred_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
lean_dec(v_a_3557_);
lean_dec_ref(v_a_3556_);
lean_dec(v_a_3555_);
lean_dec_ref(v_a_3554_);
lean_dec(v_a_3553_);
lean_dec(v_a_3552_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(lean_object* v_h_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_){
_start:
{
switch(lean_obj_tag(v_h_3564_))
{
case 0:
{
lean_object* v_c_3568_; lean_object* v___x_3569_; 
v_c_3568_ = lean_ctor_get(v_h_3564_, 0);
lean_inc_ref(v_c_3568_);
lean_dec_ref_known(v_h_3564_, 1);
v___x_3569_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_3568_, v_a_3565_, v_a_3566_);
return v___x_3569_;
}
case 1:
{
lean_object* v_c_3570_; lean_object* v___x_3571_; 
v_c_3570_ = lean_ctor_get(v_h_3564_, 0);
lean_inc_ref(v_c_3570_);
lean_dec_ref_known(v_h_3564_, 1);
v___x_3571_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3570_, v_a_3565_, v_a_3566_);
return v___x_3571_;
}
case 2:
{
lean_object* v_c_3572_; lean_object* v___x_3573_; 
v_c_3572_ = lean_ctor_get(v_h_3564_, 0);
lean_inc_ref(v_c_3572_);
lean_dec_ref_known(v_h_3564_, 1);
v___x_3573_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_3572_, v_a_3565_, v_a_3566_);
return v___x_3573_;
}
case 3:
{
lean_object* v_c_3574_; lean_object* v___x_3575_; 
v_c_3574_ = lean_ctor_get(v_h_3564_, 0);
lean_inc_ref(v_c_3574_);
lean_dec_ref_known(v_h_3564_, 1);
v___x_3575_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_3574_, v_a_3565_, v_a_3566_);
return v___x_3575_;
}
default: 
{
lean_object* v_c_u2081_3576_; lean_object* v_c_u2082_3577_; lean_object* v_c_u2083_3578_; lean_object* v___x_3579_; 
v_c_u2081_3576_ = lean_ctor_get(v_h_3564_, 0);
lean_inc_ref(v_c_u2081_3576_);
v_c_u2082_3577_ = lean_ctor_get(v_h_3564_, 1);
lean_inc_ref(v_c_u2082_3577_);
v_c_u2083_3578_ = lean_ctor_get(v_h_3564_, 2);
lean_inc_ref(v_c_u2083_3578_);
lean_dec_ref_known(v_h_3564_, 3);
v___x_3579_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3576_, v_a_3565_, v_a_3566_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; lean_object* v___x_3581_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3580_);
lean_dec_ref_known(v___x_3579_, 1);
v___x_3581_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3577_, v_a_3565_, v_a_3566_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v___x_3583_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3582_);
lean_dec_ref_known(v___x_3581_, 1);
v___x_3583_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2083_3578_, v_a_3565_, v_a_3566_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3596_; 
v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3586_ = v___x_3583_;
v_isShared_3587_ = v_isSharedCheck_3596_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3583_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3596_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3594_; 
v___x_3588_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3589_, 0, v_a_3580_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
v___x_3590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
lean_ctor_set(v___x_3590_, 1, v_a_3582_);
v___x_3591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3590_);
lean_ctor_set(v___x_3591_, 1, v___x_3588_);
v___x_3592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
lean_ctor_set(v___x_3592_, 1, v_a_3584_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 0, v___x_3592_);
v___x_3594_ = v___x_3586_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
else
{
lean_dec(v_a_3582_);
lean_dec(v_a_3580_);
return v___x_3583_;
}
}
else
{
lean_dec(v_a_3580_);
lean_dec_ref(v_c_u2083_3578_);
return v___x_3581_;
}
}
else
{
lean_dec_ref(v_c_u2083_3578_);
lean_dec_ref(v_c_u2082_3577_);
return v___x_3579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg___boxed(lean_object* v_h_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3597_, v_a_3598_, v_a_3599_);
lean_dec_ref(v_a_3599_);
lean_dec(v_a_3598_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(lean_object* v_h_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_){
_start:
{
lean_object* v___x_3614_; 
v___x_3614_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3602_, v_a_3603_, v_a_3611_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___boxed(lean_object* v_h_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(v_h_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
lean_dec(v_a_3625_);
lean_dec_ref(v_a_3624_);
lean_dec(v_a_3623_);
lean_dec_ref(v_a_3622_);
lean_dec(v_a_3621_);
lean_dec_ref(v_a_3620_);
lean_dec(v_a_3619_);
lean_dec_ref(v_a_3618_);
lean_dec(v_a_3617_);
lean_dec(v_a_3616_);
return v_res_3627_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
}
#ifdef __cplusplus
}
#endif
