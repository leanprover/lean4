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
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_lia_291_ = lean_ctor_get_uint8(v_a_287_, sizeof(void*)*17 + 24);
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
lean_object* v_arg_367_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v_arg_367_ = lean_ctor_get(v___x_347_, 1);
lean_inc_ref(v_arg_367_);
v___x_395_ = l_Lean_Expr_appFnCleanup___redArg(v___x_347_);
lean_dec_ref(v___x_347_);
v___x_396_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__21));
v___x_397_ = l_Lean_Expr_isConstOf(v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__23));
v___x_399_ = l_Lean_Expr_isConstOf(v___x_395_, v___x_398_);
lean_dec_ref(v___x_395_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; 
lean_dec_ref(v_arg_367_);
v___x_400_ = lean_box(v___x_363_);
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
return v___x_401_;
}
else
{
v___y_369_ = v_a_338_;
v___y_370_ = v_a_339_;
v___y_371_ = v_a_340_;
v___y_372_ = v_a_341_;
goto v___jp_368_;
}
}
else
{
lean_dec_ref(v___x_395_);
v___y_369_ = v_a_338_;
v___y_370_ = v_a_339_;
v___y_371_ = v_a_340_;
v___y_372_ = v_a_341_;
goto v___jp_368_;
}
v___jp_368_:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_Meta_getNatValue_x3f(v_arg_367_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec_ref(v_arg_367_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_386_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_386_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_386_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_386_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
if (lean_obj_tag(v_a_374_) == 0)
{
lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_378_ = lean_box(v___x_363_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_378_);
v___x_380_ = v___x_376_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
else
{
lean_object* v___x_382_; lean_object* v___x_384_; 
lean_dec_ref_known(v_a_374_, 1);
v___x_382_ = lean_box(v___x_364_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_382_);
v___x_384_ = v___x_376_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
else
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_394_; 
v_a_387_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_394_ == 0)
{
v___x_389_ = v___x_373_;
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_373_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_394_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_392_; 
if (v_isShared_390_ == 0)
{
v___x_392_ = v___x_389_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_387_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg___boxed(lean_object* v_00_u03b1_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg(v_00_u03b1_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec_ref(v_00_u03b1_402_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated(lean_object* v_00_u03b1_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg(v_00_u03b1_409_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___boxed(lean_object* v_00_u03b1_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated(v_00_u03b1_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_00_u03b1_422_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_435_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; uint8_t v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v___x_440_ = lean_unbox(v_a_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; 
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
v___x_441_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_435_, v_a_436_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_455_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_455_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_455_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_455_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v_conflict_x3f_446_; 
v_conflict_x3f_446_ = lean_ctor_get(v_a_442_, 17);
lean_inc(v_conflict_x3f_446_);
lean_dec(v_a_442_);
if (lean_obj_tag(v_conflict_x3f_446_) == 0)
{
lean_object* v___x_448_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v_a_439_);
v___x_448_ = v___x_444_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_439_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
else
{
uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
lean_dec_ref_known(v_conflict_x3f_446_, 1);
lean_dec(v_a_439_);
v___x_450_ = 1;
v___x_451_ = lean_box(v___x_450_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_451_);
v___x_453_ = v___x_444_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_dec(v_a_439_);
v_a_456_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_441_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_441_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
else
{
return v___x_438_;
}
}
else
{
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg___boxed(lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_464_, v_a_465_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_468_, v_a_476_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___boxed(lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec(v_a_480_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVar___boxed(lean_object* v_e_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_00___x40___internal___hyg_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = lean_grind_cutsat_mk_var(v_e_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_517_, v_a_518_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_529_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_529_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_529_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_529_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_vars_525_; lean_object* v___x_527_; 
v_vars_525_ = lean_ctor_get(v_a_521_, 0);
lean_inc_ref(v_vars_525_);
lean_dec(v_a_521_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v_vars_525_);
v___x_527_ = v___x_523_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_vars_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
v_a_530_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_520_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_520_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg___boxed(lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_538_, v_a_539_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars(lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_542_, v_a_550_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___boxed(lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars(v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec(v_a_554_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object* v_x_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = l_Lean_instInhabitedExpr;
v___x_571_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_587_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_587_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_587_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_587_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v_vars_576_; lean_object* v_size_577_; uint8_t v___x_578_; 
v_vars_576_ = lean_ctor_get(v_a_572_, 0);
lean_inc_ref(v_vars_576_);
lean_dec(v_a_572_);
v_size_577_ = lean_ctor_get(v_vars_576_, 2);
v___x_578_ = lean_nat_dec_lt(v_x_566_, v_size_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_581_; 
lean_dec_ref(v_vars_576_);
v___x_579_ = l_outOfBounds___redArg(v___x_570_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_579_);
v___x_581_ = v___x_574_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_583_ = l_Lean_PersistentArray_get_x21___redArg(v___x_570_, v_vars_576_, v_x_566_);
lean_dec_ref(v_vars_576_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_583_);
v___x_585_ = v___x_574_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
v_a_588_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_571_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_571_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg___boxed(lean_object* v_x_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_596_, v_a_597_, v_a_598_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec(v_x_596_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar(lean_object* v_x_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_601_, v_a_602_, v_a_610_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___boxed(lean_object* v_x_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar(v_x_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec(v_a_616_);
lean_dec(v_a_615_);
lean_dec(v_x_614_);
return v_res_626_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_627_, lean_object* v_i_628_, lean_object* v_k_629_){
_start:
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_array_get_size(v_keys_627_);
v___x_631_ = lean_nat_dec_lt(v_i_628_, v___x_630_);
if (v___x_631_ == 0)
{
lean_dec(v_i_628_);
return v___x_631_;
}
else
{
lean_object* v_k_x27_632_; size_t v___x_633_; size_t v___x_634_; uint8_t v___x_635_; 
v_k_x27_632_ = lean_array_fget_borrowed(v_keys_627_, v_i_628_);
v___x_633_ = lean_ptr_addr(v_k_629_);
v___x_634_ = lean_ptr_addr(v_k_x27_632_);
v___x_635_ = lean_usize_dec_eq(v___x_633_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_unsigned_to_nat(1u);
v___x_637_ = lean_nat_add(v_i_628_, v___x_636_);
lean_dec(v_i_628_);
v_i_628_ = v___x_637_;
goto _start;
}
else
{
lean_dec(v_i_628_);
return v___x_631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_639_, lean_object* v_i_640_, lean_object* v_k_641_){
_start:
{
uint8_t v_res_642_; lean_object* v_r_643_; 
v_res_642_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_639_, v_i_640_, v_k_641_);
lean_dec_ref(v_k_641_);
lean_dec_ref(v_keys_639_);
v_r_643_ = lean_box(v_res_642_);
return v_r_643_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(lean_object* v_x_644_, size_t v_x_645_, lean_object* v_x_646_){
_start:
{
if (lean_obj_tag(v_x_644_) == 0)
{
lean_object* v_es_647_; lean_object* v___x_648_; size_t v___x_649_; size_t v___x_650_; lean_object* v_j_651_; lean_object* v___x_652_; 
v_es_647_ = lean_ctor_get(v_x_644_, 0);
v___x_648_ = lean_box(2);
v___x_649_ = ((size_t)31ULL);
v___x_650_ = lean_usize_land(v_x_645_, v___x_649_);
v_j_651_ = lean_usize_to_nat(v___x_650_);
v___x_652_ = lean_array_get_borrowed(v___x_648_, v_es_647_, v_j_651_);
lean_dec(v_j_651_);
switch(lean_obj_tag(v___x_652_))
{
case 0:
{
lean_object* v_key_653_; size_t v___x_654_; size_t v___x_655_; uint8_t v___x_656_; 
v_key_653_ = lean_ctor_get(v___x_652_, 0);
v___x_654_ = lean_ptr_addr(v_x_646_);
v___x_655_ = lean_ptr_addr(v_key_653_);
v___x_656_ = lean_usize_dec_eq(v___x_654_, v___x_655_);
return v___x_656_;
}
case 1:
{
lean_object* v_node_657_; size_t v___x_658_; size_t v___x_659_; 
v_node_657_ = lean_ctor_get(v___x_652_, 0);
v___x_658_ = ((size_t)5ULL);
v___x_659_ = lean_usize_shift_right(v_x_645_, v___x_658_);
v_x_644_ = v_node_657_;
v_x_645_ = v___x_659_;
goto _start;
}
default: 
{
uint8_t v___x_661_; 
v___x_661_ = 0;
return v___x_661_;
}
}
}
else
{
lean_object* v_ks_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_ks_662_ = lean_ctor_get(v_x_644_, 0);
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_ks_662_, v___x_663_, v_x_646_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___boxed(lean_object* v_x_665_, lean_object* v_x_666_, lean_object* v_x_667_){
_start:
{
size_t v_x_889__boxed_668_; uint8_t v_res_669_; lean_object* v_r_670_; 
v_x_889__boxed_668_ = lean_unbox_usize(v_x_666_);
lean_dec(v_x_666_);
v_res_669_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_665_, v_x_889__boxed_668_, v_x_667_);
lean_dec_ref(v_x_667_);
lean_dec_ref(v_x_665_);
v_r_670_ = lean_box(v_res_669_);
return v_r_670_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
size_t v___x_673_; size_t v___x_674_; size_t v___x_675_; uint64_t v___x_676_; size_t v___x_677_; uint8_t v___x_678_; 
v___x_673_ = lean_ptr_addr(v_x_672_);
v___x_674_ = ((size_t)3ULL);
v___x_675_ = lean_usize_shift_right(v___x_673_, v___x_674_);
v___x_676_ = lean_usize_to_uint64(v___x_675_);
v___x_677_ = lean_uint64_to_usize(v___x_676_);
v___x_678_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_671_, v___x_677_, v_x_672_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg___boxed(lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_679_, v_x_680_);
lean_dec_ref(v_x_680_);
lean_dec_ref(v_x_679_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(lean_object* v_e_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_684_, v_a_685_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_698_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_698_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_698_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_698_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_varMap_692_; uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v_varMap_692_ = lean_ctor_get(v_a_688_, 1);
lean_inc_ref(v_varMap_692_);
lean_dec(v_a_688_);
v___x_693_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_varMap_692_, v_e_683_);
lean_dec_ref(v_varMap_692_);
v___x_694_ = lean_box(v___x_693_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_694_);
v___x_696_ = v___x_690_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v_a_699_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_687_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_687_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg___boxed(lean_object* v_e_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_707_, v_a_708_, v_a_709_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_e_707_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar(lean_object* v_e_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_712_, v_a_713_, v_a_721_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___boxed(lean_object* v_e_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar(v_e_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
lean_dec(v_a_726_);
lean_dec_ref(v_e_725_);
return v_res_737_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(lean_object* v_00_u03b2_738_, lean_object* v_x_739_, lean_object* v_x_740_){
_start:
{
uint8_t v___x_741_; 
v___x_741_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_739_, v_x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___boxed(lean_object* v_00_u03b2_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(v_00_u03b2_742_, v_x_743_, v_x_744_);
lean_dec_ref(v_x_744_);
lean_dec_ref(v_x_743_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(lean_object* v_00_u03b2_747_, lean_object* v_x_748_, size_t v_x_749_, lean_object* v_x_750_){
_start:
{
uint8_t v___x_751_; 
v___x_751_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_748_, v_x_749_, v_x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_752_, lean_object* v_x_753_, lean_object* v_x_754_, lean_object* v_x_755_){
_start:
{
size_t v_x_1006__boxed_756_; uint8_t v_res_757_; lean_object* v_r_758_; 
v_x_1006__boxed_756_ = lean_unbox_usize(v_x_754_);
lean_dec(v_x_754_);
v_res_757_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(v_00_u03b2_752_, v_x_753_, v_x_1006__boxed_756_, v_x_755_);
lean_dec_ref(v_x_755_);
lean_dec_ref(v_x_753_);
v_r_758_ = lean_box(v_res_757_);
return v_r_758_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_759_, lean_object* v_keys_760_, lean_object* v_vals_761_, lean_object* v_heq_762_, lean_object* v_i_763_, lean_object* v_k_764_){
_start:
{
uint8_t v___x_765_; 
v___x_765_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_760_, v_i_763_, v_k_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_766_, lean_object* v_keys_767_, lean_object* v_vals_768_, lean_object* v_heq_769_, lean_object* v_i_770_, lean_object* v_k_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(v_00_u03b2_766_, v_keys_767_, v_vals_768_, v_heq_769_, v_i_770_, v_k_771_);
lean_dec_ref(v_k_771_);
lean_dec_ref(v_vals_768_);
lean_dec_ref(v_keys_767_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(lean_object* v_e_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_774_, v_a_775_, v_a_776_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg___boxed(lean_object* v_e_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(v_e_779_, v_a_780_, v_a_781_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_e_779_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(lean_object* v_e_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_784_, v_a_785_, v_a_793_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___boxed(lean_object* v_e_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(v_e_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_e_797_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(lean_object* v_x_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_box(0);
v___x_815_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_837_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_837_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_837_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_837_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___y_821_; lean_object* v_elimEqs_832_; lean_object* v_size_833_; uint8_t v___x_834_; 
v_elimEqs_832_ = lean_ctor_get(v_a_816_, 9);
lean_inc_ref(v_elimEqs_832_);
lean_dec(v_a_816_);
v_size_833_ = lean_ctor_get(v_elimEqs_832_, 2);
v___x_834_ = lean_nat_dec_lt(v_x_810_, v_size_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
lean_dec_ref(v_elimEqs_832_);
v___x_835_ = l_outOfBounds___redArg(v___x_814_);
v___y_821_ = v___x_835_;
goto v___jp_820_;
}
else
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_PersistentArray_get_x21___redArg(v___x_814_, v_elimEqs_832_, v_x_810_);
lean_dec_ref(v_elimEqs_832_);
v___y_821_ = v___x_836_;
goto v___jp_820_;
}
v___jp_820_:
{
if (lean_obj_tag(v___y_821_) == 0)
{
uint8_t v___x_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_822_ = 0;
v___x_823_ = lean_box(v___x_822_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_823_);
v___x_825_ = v___x_818_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
else
{
uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
lean_dec_ref_known(v___y_821_, 1);
v___x_827_ = 1;
v___x_828_ = lean_box(v___x_827_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_828_);
v___x_830_ = v___x_818_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
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
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
v_a_838_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_815_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_815_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg___boxed(lean_object* v_x_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_846_, v_a_847_, v_a_848_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec(v_x_846_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated(lean_object* v_x_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_851_, v_a_852_, v_a_860_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___boxed(lean_object* v_x_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated(v_x_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec_ref(v_a_869_);
lean_dec(v_a_868_);
lean_dec_ref(v_a_867_);
lean_dec(v_a_866_);
lean_dec(v_a_865_);
lean_dec(v_x_864_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_assert___boxed(lean_object* v_c_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_00___x40___internal___hyg_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = lean_grind_cutsat_assert_eq(v_c_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(lean_object* v_x_902_, lean_object* v_s_903_){
_start:
{
lean_object* v_vars_904_; lean_object* v_varMap_905_; lean_object* v_varsHistory_906_; lean_object* v_natToIntMap_907_; lean_object* v_natDef_908_; lean_object* v_dvds_909_; lean_object* v_lowers_910_; lean_object* v_uppers_911_; lean_object* v_diseqs_912_; lean_object* v_elimEqs_913_; lean_object* v_elimStack_914_; lean_object* v_occurs_915_; lean_object* v_assignment_916_; lean_object* v_nextCnstrId_917_; uint8_t v_caseSplits_918_; lean_object* v_steps_919_; lean_object* v_penalties_920_; lean_object* v_numReorderRequests_921_; lean_object* v_conflict_x3f_922_; lean_object* v_diseqSplits_923_; lean_object* v_divMod_924_; uint8_t v_usedCommRing_925_; lean_object* v_nonlinearOccs_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_934_; 
v_vars_904_ = lean_ctor_get(v_s_903_, 0);
v_varMap_905_ = lean_ctor_get(v_s_903_, 1);
v_varsHistory_906_ = lean_ctor_get(v_s_903_, 2);
v_natToIntMap_907_ = lean_ctor_get(v_s_903_, 3);
v_natDef_908_ = lean_ctor_get(v_s_903_, 4);
v_dvds_909_ = lean_ctor_get(v_s_903_, 5);
v_lowers_910_ = lean_ctor_get(v_s_903_, 6);
v_uppers_911_ = lean_ctor_get(v_s_903_, 7);
v_diseqs_912_ = lean_ctor_get(v_s_903_, 8);
v_elimEqs_913_ = lean_ctor_get(v_s_903_, 9);
v_elimStack_914_ = lean_ctor_get(v_s_903_, 10);
v_occurs_915_ = lean_ctor_get(v_s_903_, 11);
v_assignment_916_ = lean_ctor_get(v_s_903_, 12);
v_nextCnstrId_917_ = lean_ctor_get(v_s_903_, 13);
v_caseSplits_918_ = lean_ctor_get_uint8(v_s_903_, sizeof(void*)*21);
v_steps_919_ = lean_ctor_get(v_s_903_, 14);
v_penalties_920_ = lean_ctor_get(v_s_903_, 15);
v_numReorderRequests_921_ = lean_ctor_get(v_s_903_, 16);
v_conflict_x3f_922_ = lean_ctor_get(v_s_903_, 17);
v_diseqSplits_923_ = lean_ctor_get(v_s_903_, 18);
v_divMod_924_ = lean_ctor_get(v_s_903_, 19);
v_usedCommRing_925_ = lean_ctor_get_uint8(v_s_903_, sizeof(void*)*21 + 1);
v_nonlinearOccs_926_ = lean_ctor_get(v_s_903_, 20);
v_isSharedCheck_934_ = !lean_is_exclusive(v_s_903_);
if (v_isSharedCheck_934_ == 0)
{
v___x_928_ = v_s_903_;
v_isShared_929_ = v_isSharedCheck_934_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_nonlinearOccs_926_);
lean_inc(v_divMod_924_);
lean_inc(v_diseqSplits_923_);
lean_inc(v_conflict_x3f_922_);
lean_inc(v_numReorderRequests_921_);
lean_inc(v_penalties_920_);
lean_inc(v_steps_919_);
lean_inc(v_nextCnstrId_917_);
lean_inc(v_assignment_916_);
lean_inc(v_occurs_915_);
lean_inc(v_elimStack_914_);
lean_inc(v_elimEqs_913_);
lean_inc(v_diseqs_912_);
lean_inc(v_uppers_911_);
lean_inc(v_lowers_910_);
lean_inc(v_dvds_909_);
lean_inc(v_natDef_908_);
lean_inc(v_natToIntMap_907_);
lean_inc(v_varsHistory_906_);
lean_inc(v_varMap_905_);
lean_inc(v_vars_904_);
lean_dec(v_s_903_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_934_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_930_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_916_, v_x_902_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 12, v___x_930_);
v___x_932_ = v___x_928_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_vars_904_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_varMap_905_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_varsHistory_906_);
lean_ctor_set(v_reuseFailAlloc_933_, 3, v_natToIntMap_907_);
lean_ctor_set(v_reuseFailAlloc_933_, 4, v_natDef_908_);
lean_ctor_set(v_reuseFailAlloc_933_, 5, v_dvds_909_);
lean_ctor_set(v_reuseFailAlloc_933_, 6, v_lowers_910_);
lean_ctor_set(v_reuseFailAlloc_933_, 7, v_uppers_911_);
lean_ctor_set(v_reuseFailAlloc_933_, 8, v_diseqs_912_);
lean_ctor_set(v_reuseFailAlloc_933_, 9, v_elimEqs_913_);
lean_ctor_set(v_reuseFailAlloc_933_, 10, v_elimStack_914_);
lean_ctor_set(v_reuseFailAlloc_933_, 11, v_occurs_915_);
lean_ctor_set(v_reuseFailAlloc_933_, 12, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_933_, 13, v_nextCnstrId_917_);
lean_ctor_set(v_reuseFailAlloc_933_, 14, v_steps_919_);
lean_ctor_set(v_reuseFailAlloc_933_, 15, v_penalties_920_);
lean_ctor_set(v_reuseFailAlloc_933_, 16, v_numReorderRequests_921_);
lean_ctor_set(v_reuseFailAlloc_933_, 17, v_conflict_x3f_922_);
lean_ctor_set(v_reuseFailAlloc_933_, 18, v_diseqSplits_923_);
lean_ctor_set(v_reuseFailAlloc_933_, 19, v_divMod_924_);
lean_ctor_set(v_reuseFailAlloc_933_, 20, v_nonlinearOccs_926_);
lean_ctor_set_uint8(v_reuseFailAlloc_933_, sizeof(void*)*21, v_caseSplits_918_);
lean_ctor_set_uint8(v_reuseFailAlloc_933_, sizeof(void*)*21 + 1, v_usedCommRing_925_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_x_935_, lean_object* v_s_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(v_x_935_, v_s_936_);
lean_dec(v_x_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object* v_x_938_, lean_object* v_a_939_){
_start:
{
lean_object* v___f_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___f_941_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_941_, 0, v_x_938_);
v___x_942_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_943_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_942_, v___f_941_, v_a_939_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___boxed(lean_object* v_x_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_944_, v_a_945_);
lean_dec(v_a_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(lean_object* v_x_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_948_, v_a_949_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___boxed(lean_object* v_x_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(v_x_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec(v_a_962_);
return v_res_973_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__0));
v___x_976_ = l_Lean_stringToMessageData(v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_unsigned_to_nat(1u);
v___x_978_ = lean_nat_to_int(v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__3));
v___x_981_ = l_Lean_stringToMessageData(v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(lean_object* v_r_982_, lean_object* v_p_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
if (lean_obj_tag(v_p_983_) == 0)
{
lean_object* v_k_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1005_; 
v_k_987_ = lean_ctor_get(v_p_983_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_p_983_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_989_ = v_p_983_;
v_isShared_990_ = v_isSharedCheck_1005_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_k_987_);
lean_dec(v_p_983_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1005_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_992_ = lean_int_dec_eq(v_k_987_, v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_993_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v_r_982_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = l_Int_repr(v_k_987_);
lean_dec(v_k_987_);
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 3);
lean_ctor_set(v___x_989_, 0, v___x_995_);
v___x_997_ = v___x_989_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = l_Lean_MessageData_ofFormat(v___x_997_);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_994_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
else
{
lean_object* v___x_1003_; 
lean_dec(v_k_987_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v_r_982_);
v___x_1003_ = v___x_989_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_r_982_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
else
{
lean_object* v_k_1006_; lean_object* v_v_1007_; lean_object* v_p_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v_k_1006_ = lean_ctor_get(v_p_983_, 0);
lean_inc(v_k_1006_);
v_v_1007_ = lean_ctor_get(v_p_983_, 1);
lean_inc(v_v_1007_);
v_p_1008_ = lean_ctor_get(v_p_983_, 2);
lean_inc_ref(v_p_1008_);
lean_dec_ref_known(v_p_983_, 3);
v___x_1009_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_1010_ = lean_int_dec_eq(v_k_1006_, v___x_1009_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_1007_, v_a_984_, v_a_985_);
lean_dec(v_v_1007_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v___x_1013_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v_r_982_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = l_Int_repr(v_k_1006_);
lean_dec(v_k_1006_);
v___x_1016_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
v___x_1017_ = l_Lean_MessageData_ofFormat(v___x_1016_);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1014_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_1012_);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v_r_982_ = v___x_1022_;
v_p_983_ = v_p_1008_;
goto _start;
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec_ref(v_p_1008_);
lean_dec(v_k_1006_);
lean_dec_ref(v_r_982_);
v_a_1024_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1011_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1011_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
else
{
lean_object* v___x_1032_; 
lean_dec(v_k_1006_);
v___x_1032_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_1007_, v_a_984_, v_a_985_);
lean_dec(v_v_1007_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1032_, 1);
v___x_1034_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v_r_982_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_1033_);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v_r_982_ = v___x_1037_;
v_p_983_ = v_p_1008_;
goto _start;
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec_ref(v_p_1008_);
lean_dec_ref(v_r_982_);
v_a_1039_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1032_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1032_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___boxed(lean_object* v_r_1047_, lean_object* v_p_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v_r_1047_, v_p_1048_, v_a_1049_, v_a_1050_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(lean_object* v_r_1053_, lean_object* v_p_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v_r_1053_, v_p_1054_, v_a_1055_, v_a_1063_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___boxed(lean_object* v_r_1067_, lean_object* v_p_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(v_r_1067_, v_p_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec(v_a_1069_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___redArg(lean_object* v_p_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
if (lean_obj_tag(v_p_1081_) == 0)
{
lean_object* v_k_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1095_; 
v_k_1085_ = lean_ctor_get(v_p_1081_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_p_1081_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1087_ = v_p_1081_;
v_isShared_1088_ = v_isSharedCheck_1095_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_k_1085_);
lean_dec(v_p_1081_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1095_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1089_ = l_Int_repr(v_k_1085_);
lean_dec(v_k_1085_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set_tag(v___x_1087_, 3);
lean_ctor_set(v___x_1087_, 0, v___x_1089_);
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = l_Lean_MessageData_ofFormat(v___x_1091_);
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
return v___x_1093_;
}
}
}
else
{
lean_object* v_k_1096_; lean_object* v_v_1097_; lean_object* v_p_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v_k_1096_ = lean_ctor_get(v_p_1081_, 0);
lean_inc(v_k_1096_);
v_v_1097_ = lean_ctor_get(v_p_1081_, 1);
lean_inc(v_v_1097_);
v_p_1098_ = lean_ctor_get(v_p_1081_, 2);
lean_inc_ref(v_p_1098_);
lean_dec_ref_known(v_p_1081_, 3);
v___x_1099_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_1100_ = lean_int_dec_eq(v_k_1096_, v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_1097_, v_a_1082_, v_a_1083_);
lean_dec(v_v_1097_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v___x_1101_, 1);
v___x_1103_ = l_Int_repr(v_k_1096_);
lean_dec(v_k_1096_);
v___x_1104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
v___x_1105_ = l_Lean_MessageData_ofFormat(v___x_1104_);
v___x_1106_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_1102_);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v___x_1109_, v_p_1098_, v_a_1082_, v_a_1083_);
return v___x_1110_;
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec_ref(v_p_1098_);
lean_dec(v_k_1096_);
v_a_1111_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1101_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1101_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
else
{
lean_object* v___x_1119_; 
lean_dec(v_k_1096_);
v___x_1119_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_1097_, v_a_1082_, v_a_1083_);
lean_dec(v_v_1097_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v___x_1121_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_1120_);
v___x_1122_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v___x_1121_, v_p_1098_, v_a_1082_, v_a_1083_);
return v___x_1122_;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec_ref(v_p_1098_);
v_a_1123_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1119_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1119_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___redArg___boxed(lean_object* v_p_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1131_, v_a_1132_, v_a_1133_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp(lean_object* v_p_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1136_, v_a_1137_, v_a_1145_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___boxed(lean_object* v_p_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Int_Internal_Linear_Poly_pp(v_p_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec(v_a_1150_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0(lean_object* v_a_1162_, lean_object* v___x_1163_, lean_object* v_x_1164_){
_start:
{
lean_object* v_size_1165_; uint8_t v___x_1166_; 
v_size_1165_ = lean_ctor_get(v_a_1162_, 2);
v___x_1166_ = lean_nat_dec_lt(v_x_1164_, v_size_1165_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; 
v___x_1167_ = l_outOfBounds___redArg(v___x_1163_);
return v___x_1167_;
}
else
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1163_, v_a_1162_, v_x_1164_);
return v___x_1168_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed(lean_object* v_a_1169_, lean_object* v___x_1170_, lean_object* v_x_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0(v_a_1169_, v___x_1170_, v_x_1171_);
lean_dec(v_x_1171_);
lean_dec_ref(v___x_1170_);
lean_dec_ref(v_a_1169_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(lean_object* v_p_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = l_Lean_instInhabitedExpr;
v___x_1178_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_1174_, v_a_1175_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___f_1180_; lean_object* v___x_1181_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___x_1178_, 1);
v___f_1180_ = lean_alloc_closure((void*)(l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1180_, 0, v_a_1179_);
lean_closure_set(v___f_1180_, 1, v___x_1177_);
v___x_1181_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_1180_, v_p_1173_);
return v___x_1181_;
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec_ref(v_p_1173_);
v_a_1182_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1178_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1178_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___boxed(lean_object* v_p_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1190_, v_a_1191_, v_a_1192_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27(lean_object* v_p_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1195_, v_a_1196_, v_a_1204_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___boxed(lean_object* v_p_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Int_Internal_Linear_Poly_denoteExpr_x27(v_p_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec(v_a_1210_);
lean_dec(v_a_1209_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored___redArg(lean_object* v_c_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_depth_x3f_1224_; 
v_depth_x3f_1224_ = lean_ctor_get(v_c_1221_, 2);
lean_inc(v_depth_x3f_1224_);
if (lean_obj_tag(v_depth_x3f_1224_) == 0)
{
lean_object* v_p_1225_; lean_object* v_h_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1251_; 
v_p_1225_ = lean_ctor_get(v_c_1221_, 0);
v_h_1226_ = lean_ctor_get(v_c_1221_, 1);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_c_1221_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v_c_1221_, 2);
lean_dec(v_unused_1252_);
v___x_1228_ = v_c_1221_;
v_isShared_1229_ = v_isSharedCheck_1251_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_h_1226_);
lean_inc(v_p_1225_);
lean_dec(v_c_1221_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1251_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_Meta_Grind_getGoalStackDepth___redArg(v_a_1222_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1242_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1242_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1242_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1235_, 0, v_a_1231_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 2, v___x_1235_);
v___x_1237_ = v___x_1228_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_p_1225_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_h_1226_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1239_; 
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1237_);
v___x_1239_ = v___x_1233_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_del_object(v___x_1228_);
lean_dec_ref(v_h_1226_);
lean_dec_ref(v_p_1225_);
v_a_1243_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1230_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1230_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
else
{
lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
v_isSharedCheck_1259_ = !lean_is_exclusive(v_depth_x3f_1224_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v_depth_x3f_1224_, 0);
lean_dec(v_unused_1260_);
v___x_1254_ = v_depth_x3f_1224_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_dec(v_depth_x3f_1224_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set_tag(v___x_1254_, 0);
lean_ctor_set(v___x_1254_, 0, v_c_1221_);
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_c_1221_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored___redArg___boxed(lean_object* v_c_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored___redArg(v_c_1261_, v_a_1262_);
lean_dec(v_a_1262_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored(lean_object* v_c_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored___redArg(v_c_1265_, v_a_1266_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored___boxed(lean_object* v_c_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_markStored(v_c_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec(v_a_1279_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored___redArg(lean_object* v_c_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v_depth_x3f_1294_; 
v_depth_x3f_1294_ = lean_ctor_get(v_c_1291_, 3);
lean_inc(v_depth_x3f_1294_);
if (lean_obj_tag(v_depth_x3f_1294_) == 0)
{
lean_object* v_d_1295_; lean_object* v_p_1296_; lean_object* v_h_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1322_; 
v_d_1295_ = lean_ctor_get(v_c_1291_, 0);
v_p_1296_ = lean_ctor_get(v_c_1291_, 1);
v_h_1297_ = lean_ctor_get(v_c_1291_, 2);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_c_1291_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; 
v_unused_1323_ = lean_ctor_get(v_c_1291_, 3);
lean_dec(v_unused_1323_);
v___x_1299_ = v_c_1291_;
v_isShared_1300_ = v_isSharedCheck_1322_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_h_1297_);
lean_inc(v_p_1296_);
lean_inc(v_d_1295_);
lean_dec(v_c_1291_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1322_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_Meta_Grind_getGoalStackDepth___redArg(v_a_1292_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1313_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1313_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1313_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1306_, 0, v_a_1302_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 3, v___x_1306_);
v___x_1308_ = v___x_1299_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_d_1295_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_p_1296_);
lean_ctor_set(v_reuseFailAlloc_1312_, 2, v_h_1297_);
lean_ctor_set(v_reuseFailAlloc_1312_, 3, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1310_; 
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1308_);
v___x_1310_ = v___x_1304_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_del_object(v___x_1299_);
lean_dec_ref(v_h_1297_);
lean_dec_ref(v_p_1296_);
lean_dec(v_d_1295_);
v_a_1314_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1301_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1301_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
else
{
lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
v_isSharedCheck_1330_ = !lean_is_exclusive(v_depth_x3f_1294_);
if (v_isSharedCheck_1330_ == 0)
{
lean_object* v_unused_1331_; 
v_unused_1331_ = lean_ctor_get(v_depth_x3f_1294_, 0);
lean_dec(v_unused_1331_);
v___x_1325_ = v_depth_x3f_1294_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_dec(v_depth_x3f_1294_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
lean_ctor_set_tag(v___x_1325_, 0);
lean_ctor_set(v___x_1325_, 0, v_c_1291_);
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_c_1291_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored___redArg___boxed(lean_object* v_c_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored___redArg(v_c_1332_, v_a_1333_);
lean_dec(v_a_1333_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored(lean_object* v_c_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored___redArg(v_c_1336_, v_a_1337_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored___boxed(lean_object* v_c_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_markStored(v_c_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec(v_a_1350_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored___redArg(lean_object* v_c_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v_depth_x3f_1365_; 
v_depth_x3f_1365_ = lean_ctor_get(v_c_1362_, 2);
lean_inc(v_depth_x3f_1365_);
if (lean_obj_tag(v_depth_x3f_1365_) == 0)
{
lean_object* v_p_1366_; lean_object* v_h_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1392_; 
v_p_1366_ = lean_ctor_get(v_c_1362_, 0);
v_h_1367_ = lean_ctor_get(v_c_1362_, 1);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_c_1362_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v_c_1362_, 2);
lean_dec(v_unused_1393_);
v___x_1369_ = v_c_1362_;
v_isShared_1370_ = v_isSharedCheck_1392_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_h_1367_);
lean_inc(v_p_1366_);
lean_dec(v_c_1362_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1392_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Lean_Meta_Grind_getGoalStackDepth___redArg(v_a_1363_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1383_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1374_ = v___x_1371_;
v_isShared_1375_ = v_isSharedCheck_1383_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1371_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1383_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1376_, 0, v_a_1372_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 2, v___x_1376_);
v___x_1378_ = v___x_1369_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_p_1366_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_h_1367_);
lean_ctor_set(v_reuseFailAlloc_1382_, 2, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1380_; 
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1378_);
v___x_1380_ = v___x_1374_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_del_object(v___x_1369_);
lean_dec_ref(v_h_1367_);
lean_dec_ref(v_p_1366_);
v_a_1384_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1371_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1371_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
else
{
lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
v_isSharedCheck_1400_ = !lean_is_exclusive(v_depth_x3f_1365_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v_depth_x3f_1365_, 0);
lean_dec(v_unused_1401_);
v___x_1395_ = v_depth_x3f_1365_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_dec(v_depth_x3f_1365_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set_tag(v___x_1395_, 0);
lean_ctor_set(v___x_1395_, 0, v_c_1362_);
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_c_1362_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored___redArg___boxed(lean_object* v_c_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored___redArg(v_c_1402_, v_a_1403_);
lean_dec(v_a_1403_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored(lean_object* v_c_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored___redArg(v_c_1406_, v_a_1407_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored___boxed(lean_object* v_c_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored(v_c_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
lean_dec(v_a_1429_);
lean_dec_ref(v_a_1428_);
lean_dec(v_a_1427_);
lean_dec_ref(v_a_1426_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec(v_a_1420_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored___redArg(lean_object* v_c_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v_depth_x3f_1435_; 
v_depth_x3f_1435_ = lean_ctor_get(v_c_1432_, 2);
lean_inc(v_depth_x3f_1435_);
if (lean_obj_tag(v_depth_x3f_1435_) == 0)
{
lean_object* v_p_1436_; lean_object* v_h_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1462_; 
v_p_1436_ = lean_ctor_get(v_c_1432_, 0);
v_h_1437_ = lean_ctor_get(v_c_1432_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_c_1432_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v_c_1432_, 2);
lean_dec(v_unused_1463_);
v___x_1439_ = v_c_1432_;
v_isShared_1440_ = v_isSharedCheck_1462_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_h_1437_);
lean_inc(v_p_1436_);
lean_dec(v_c_1432_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1462_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_Meta_Grind_getGoalStackDepth___redArg(v_a_1433_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1453_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1453_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1453_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1446_, 0, v_a_1442_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 2, v___x_1446_);
v___x_1448_ = v___x_1439_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_p_1436_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_h_1437_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v___x_1446_);
v___x_1448_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1450_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1448_);
v___x_1450_ = v___x_1444_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_del_object(v___x_1439_);
lean_dec_ref(v_h_1437_);
lean_dec_ref(v_p_1436_);
v_a_1454_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1441_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1441_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
else
{
lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
v_isSharedCheck_1470_ = !lean_is_exclusive(v_depth_x3f_1435_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v_depth_x3f_1435_, 0);
lean_dec(v_unused_1471_);
v___x_1465_ = v_depth_x3f_1435_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_dec(v_depth_x3f_1435_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set_tag(v___x_1465_, 0);
lean_ctor_set(v___x_1465_, 0, v_c_1432_);
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_c_1432_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored___redArg___boxed(lean_object* v_c_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored___redArg(v_c_1472_, v_a_1473_);
lean_dec(v_a_1473_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored(lean_object* v_c_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored___redArg(v_c_1476_, v_a_1477_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored___boxed(lean_object* v_c_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_markStored(v_c_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec(v_a_1490_);
return v_res_1501_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object* v_c_1502_){
_start:
{
lean_object* v_p_1503_; 
v_p_1503_ = lean_ctor_get(v_c_1502_, 1);
if (lean_obj_tag(v_p_1503_) == 0)
{
lean_object* v_d_1504_; lean_object* v_k_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; 
v_d_1504_ = lean_ctor_get(v_c_1502_, 0);
v_k_1505_ = lean_ctor_get(v_p_1503_, 0);
v___x_1506_ = lean_int_emod(v_k_1505_, v_d_1504_);
v___x_1507_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1508_ = lean_int_dec_eq(v___x_1506_, v___x_1507_);
lean_dec(v___x_1506_);
return v___x_1508_;
}
else
{
lean_object* v_d_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v_d_1509_ = lean_ctor_get(v_c_1502_, 0);
v___x_1510_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_1511_ = lean_int_dec_eq(v_d_1509_, v___x_1510_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial___boxed(lean_object* v_c_1512_){
_start:
{
uint8_t v_res_1513_; lean_object* v_r_1514_; 
v_res_1513_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_c_1512_);
lean_dec_ref(v_c_1512_);
v_r_1514_ = lean_box(v_res_1513_);
return v_r_1514_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0));
v___x_1517_ = l_Lean_stringToMessageData(v___x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object* v_c_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_d_1522_; lean_object* v_p_1523_; lean_object* v___x_1524_; 
v_d_1522_ = lean_ctor_get(v_c_1518_, 0);
lean_inc(v_d_1522_);
v_p_1523_ = lean_ctor_get(v_c_1518_, 1);
lean_inc_ref(v_p_1523_);
lean_dec_ref(v_c_1518_);
v___x_1524_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1523_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1538_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1527_ = v___x_1524_;
v_isShared_1528_ = v_isSharedCheck_1538_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1524_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1538_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1529_ = l_Int_repr(v_d_1522_);
lean_dec(v_d_1522_);
v___x_1530_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
v___x_1531_ = l_Lean_MessageData_ofFormat(v___x_1530_);
v___x_1532_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v_a_1525_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 0, v___x_1534_);
v___x_1536_ = v___x_1527_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
else
{
lean_dec(v_d_1522_);
return v___x_1524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___boxed(lean_object* v_c_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1539_, v_a_1540_, v_a_1541_);
lean_dec_ref(v_a_1541_);
lean_dec(v_a_1540_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(lean_object* v_c_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1544_, v_a_1545_, v_a_1553_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___boxed(lean_object* v_c_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(v_c_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec(v_a_1565_);
lean_dec_ref(v_a_1564_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec(v_a_1559_);
lean_dec(v_a_1558_);
return v_res_1569_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = lean_unsigned_to_nat(0u);
v___x_1576_ = l_Lean_Level_ofNat(v___x_1575_);
return v___x_1576_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3);
v___x_1579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
lean_ctor_set(v___x_1579_, 1, v___x_1577_);
return v___x_1579_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4);
v___x_1581_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2));
v___x_1582_ = l_Lean_Expr_const___override(v___x_1581_, v___x_1580_);
return v___x_1582_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1586_ = lean_box(0);
v___x_1587_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7));
v___x_1588_ = l_Lean_Expr_const___override(v___x_1587_, v___x_1586_);
return v___x_1588_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = lean_box(0);
v___x_1594_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10));
v___x_1595_ = l_Lean_Expr_const___override(v___x_1594_, v___x_1593_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(lean_object* v_c_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v_d_1600_; lean_object* v_p_1601_; lean_object* v___x_1602_; 
v_d_1600_ = lean_ctor_get(v_c_1596_, 0);
lean_inc(v_d_1600_);
v_p_1601_ = lean_ctor_get(v_c_1596_, 1);
lean_inc_ref(v_p_1601_);
lean_dec_ref(v_c_1596_);
v___x_1602_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1601_, v_a_1597_, v_a_1598_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1624_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1624_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1624_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___y_1608_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1613_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1614_ = lean_int_dec_le(v___x_1613_, v_d_1600_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1615_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5);
v___x_1616_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8);
v___x_1617_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11);
v___x_1618_ = lean_int_neg(v_d_1600_);
lean_dec(v_d_1600_);
v___x_1619_ = l_Int_toNat(v___x_1618_);
lean_dec(v___x_1618_);
v___x_1620_ = l_Lean_instToExprInt_mkNat(v___x_1619_);
v___x_1621_ = l_Lean_mkApp3(v___x_1615_, v___x_1616_, v___x_1617_, v___x_1620_);
v___y_1608_ = v___x_1621_;
goto v___jp_1607_;
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = l_Int_toNat(v_d_1600_);
lean_dec(v_d_1600_);
v___x_1623_ = l_Lean_instToExprInt_mkNat(v___x_1622_);
v___y_1608_ = v___x_1623_;
goto v___jp_1607_;
}
v___jp_1607_:
{
lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1609_ = l_Lean_mkIntDvd(v___y_1608_, v_a_1603_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v___x_1609_);
v___x_1611_ = v___x_1605_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
else
{
lean_dec(v_d_1600_);
return v___x_1602_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1625_, v_a_1626_, v_a_1627_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(lean_object* v_c_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1630_, v_a_1631_, v_a_1639_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___boxed(lean_object* v_c_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(v_c_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec(v_a_1644_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(lean_object* v_msgData_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; lean_object* v_env_1663_; uint8_t v___x_1664_; lean_object* v_env_1665_; lean_object* v___x_1666_; lean_object* v_toCold_1667_; lean_object* v_mctx_1668_; lean_object* v_lctx_1669_; lean_object* v_options_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1662_ = lean_st_ref_get(v___y_1660_);
v_env_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc_ref(v_env_1663_);
lean_dec(v___x_1662_);
v___x_1664_ = 0;
v_env_1665_ = l_Lean_Environment_setRecordingDeps(v_env_1663_, v___x_1664_);
v___x_1666_ = lean_st_ref_get(v___y_1658_);
v_toCold_1667_ = lean_ctor_get(v___y_1659_, 0);
v_mctx_1668_ = lean_ctor_get(v___x_1666_, 0);
lean_inc_ref(v_mctx_1668_);
lean_dec(v___x_1666_);
v_lctx_1669_ = lean_ctor_get(v___y_1657_, 2);
v_options_1670_ = lean_ctor_get(v_toCold_1667_, 2);
lean_inc_ref(v_options_1670_);
lean_inc_ref(v_lctx_1669_);
v___x_1671_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1671_, 0, v_env_1665_);
lean_ctor_set(v___x_1671_, 1, v_mctx_1668_);
lean_ctor_set(v___x_1671_, 2, v_lctx_1669_);
lean_ctor_set(v___x_1671_, 3, v_options_1670_);
v___x_1672_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v_msgData_1656_);
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object* v_msgData_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msgData_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(lean_object* v_msg_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_ref_1687_; lean_object* v___x_1688_; lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1697_; 
v_ref_1687_ = lean_ctor_get(v___y_1684_, 2);
v___x_1688_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msg_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1697_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1697_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; lean_object* v___x_1695_; 
lean_inc(v_ref_1687_);
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v_ref_1687_);
lean_ctor_set(v___x_1693_, 1, v_a_1689_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set_tag(v___x_1691_, 1);
lean_ctor_set(v___x_1691_, 0, v___x_1693_);
v___x_1695_ = v___x_1691_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg___boxed(lean_object* v_msg_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
return v_res_1704_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0));
v___x_1707_ = l_Lean_stringToMessageData(v___x_1706_);
return v___x_1707_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2));
v___x_1710_ = l_Lean_stringToMessageData(v___x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object* v_c_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1711_, v_a_1712_, v_a_1720_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1726_ = l_Lean_indentD(v_a_1724_);
v___x_1727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1725_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v___x_1728_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3);
v___x_1729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1727_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v___x_1730_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1729_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_);
return v___x_1730_;
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
v_a_1731_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1723_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1723_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
lean_dec(v_a_1749_);
lean_dec_ref(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec(v_a_1743_);
lean_dec_ref(v_a_1742_);
lean_dec(v_a_1741_);
lean_dec(v_a_1740_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(lean_object* v_00_u03b1_1752_, lean_object* v_c_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1766_, lean_object* v_c_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(v_00_u03b1_1766_, v_c_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
lean_dec(v_a_1771_);
lean_dec_ref(v_a_1770_);
lean_dec(v_a_1769_);
lean_dec(v_a_1768_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(lean_object* v_00_u03b1_1780_, lean_object* v_msg_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1781_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___boxed(lean_object* v_00_u03b1_1794_, lean_object* v_msg_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(v_00_u03b1_1794_, v_msg_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec(v___y_1796_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial_spec__0(lean_object* v_a_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = lean_nat_to_int(v_a_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(lean_object* v_c_1810_){
_start:
{
lean_object* v_p_1811_; 
v_p_1811_ = lean_ctor_get(v_c_1810_, 0);
if (lean_obj_tag(v_p_1811_) == 0)
{
lean_object* v_k_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v_k_1812_ = lean_ctor_get(v_p_1811_, 0);
v___x_1813_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1814_ = lean_int_dec_eq(v_k_1812_, v___x_1813_);
if (v___x_1814_ == 0)
{
uint8_t v___x_1815_; 
v___x_1815_ = 1;
return v___x_1815_;
}
else
{
uint8_t v___x_1816_; 
v___x_1816_ = 0;
return v___x_1816_;
}
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1817_ = l_Int_Internal_Linear_Poly_getConst(v_p_1811_);
v___x_1818_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v_p_1811_);
v___x_1819_ = lean_nat_to_int(v___x_1818_);
v___x_1820_ = lean_int_emod(v___x_1817_, v___x_1819_);
lean_dec(v___x_1819_);
lean_dec(v___x_1817_);
v___x_1821_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1822_ = lean_int_dec_eq(v___x_1820_, v___x_1821_);
lean_dec(v___x_1820_);
if (v___x_1822_ == 0)
{
uint8_t v___x_1823_; 
v___x_1823_ = 1;
return v___x_1823_;
}
else
{
uint8_t v___x_1824_; 
v___x_1824_ = 0;
return v___x_1824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial___boxed(lean_object* v_c_1825_){
_start:
{
uint8_t v_res_1826_; lean_object* v_r_1827_; 
v_res_1826_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(v_c_1825_);
lean_dec_ref(v_c_1825_);
v_r_1827_ = lean_box(v_res_1826_);
return v_r_1827_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0));
v___x_1830_ = l_Lean_stringToMessageData(v___x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(lean_object* v_c_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v_p_1835_; lean_object* v___x_1836_; 
v_p_1835_ = lean_ctor_get(v_c_1831_, 0);
lean_inc_ref(v_p_1835_);
lean_dec_ref(v_c_1831_);
v___x_1836_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1835_, v_a_1832_, v_a_1833_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1846_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1846_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1846_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1841_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v_a_1837_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1842_);
v___x_1844_ = v___x_1839_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
else
{
return v___x_1836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___boxed(lean_object* v_c_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1847_, v_a_1848_, v_a_1849_);
lean_dec_ref(v_a_1849_);
lean_dec(v_a_1848_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(lean_object* v_c_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1852_, v_a_1853_, v_a_1861_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___boxed(lean_object* v_c_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(v_c_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec(v_a_1866_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(lean_object* v_c_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1878_, v_a_1879_, v_a_1882_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v___x_1887_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1888_ = l_Lean_indentD(v_a_1886_);
v___x_1889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1887_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v___x_1890_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1889_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
return v___x_1890_;
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
v_a_1891_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1885_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1885_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(lean_object* v_00_u03b1_1907_, lean_object* v_c_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1908_, v_a_1909_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1921_, lean_object* v_c_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(v_00_u03b1_1921_, v_c_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
lean_dec(v_a_1928_);
lean_dec_ref(v_a_1927_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
lean_dec(v_a_1924_);
lean_dec(v_a_1923_);
return v_res_1934_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1936_ = l_Lean_mkIntLit(v___x_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(lean_object* v_c_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v_p_1941_; lean_object* v___x_1942_; 
v_p_1941_ = lean_ctor_get(v_c_1937_, 0);
lean_inc_ref(v_p_1941_);
lean_dec_ref(v_c_1937_);
v___x_1942_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1941_, v_a_1938_, v_a_1939_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1953_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1953_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1953_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1951_; 
v___x_1947_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1948_ = l_Lean_mkIntEq(v_a_1943_, v___x_1947_);
v___x_1949_ = l_Lean_mkNot(v___x_1948_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1949_);
v___x_1951_ = v___x_1945_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1949_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
else
{
return v___x_1942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1954_, v_a_1955_, v_a_1956_);
lean_dec_ref(v_a_1956_);
lean_dec(v_a_1955_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(lean_object* v_c_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1959_, v_a_1960_, v_a_1968_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___boxed(lean_object* v_c_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(v_c_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
lean_dec(v_a_1982_);
lean_dec_ref(v_a_1981_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
lean_dec(v_a_1974_);
lean_dec(v_a_1973_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert___boxed(lean_object* v_c_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_00___x40___internal___hyg_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = lean_grind_cutsat_assert_le(v_c_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(lean_object* v_c_2010_){
_start:
{
lean_object* v_p_2011_; 
v_p_2011_ = lean_ctor_get(v_c_2010_, 0);
if (lean_obj_tag(v_p_2011_) == 0)
{
lean_object* v_k_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v_k_2012_ = lean_ctor_get(v_p_2011_, 0);
v___x_2013_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_2014_ = lean_int_dec_le(v_k_2012_, v___x_2013_);
return v___x_2014_;
}
else
{
uint8_t v___x_2015_; 
v___x_2015_ = 0;
return v___x_2015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial___boxed(lean_object* v_c_2016_){
_start:
{
uint8_t v_res_2017_; lean_object* v_r_2018_; 
v_res_2017_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_c_2016_);
lean_dec_ref(v_c_2016_);
v_r_2018_ = lean_box(v_res_2017_);
return v_r_2018_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0));
v___x_2021_ = l_Lean_stringToMessageData(v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(lean_object* v_c_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v_p_2026_; lean_object* v___x_2027_; 
v_p_2026_ = lean_ctor_get(v_c_2022_, 0);
lean_inc_ref(v_p_2026_);
lean_dec_ref(v_c_2022_);
v___x_2027_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_2026_, v_a_2023_, v_a_2024_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2037_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2037_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2037_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2032_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1);
v___x_2033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2033_, 0, v_a_2028_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2033_);
v___x_2035_ = v___x_2030_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
else
{
return v___x_2027_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___boxed(lean_object* v_c_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_2038_, v_a_2039_, v_a_2040_);
lean_dec_ref(v_a_2040_);
lean_dec(v_a_2039_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(lean_object* v_c_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_2043_, v_a_2044_, v_a_2052_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___boxed(lean_object* v_c_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(v_c_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
lean_dec(v_a_2066_);
lean_dec_ref(v_a_2065_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2061_);
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2059_);
lean_dec(v_a_2058_);
lean_dec(v_a_2057_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(lean_object* v_c_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v_p_2073_; lean_object* v___x_2074_; 
v_p_2073_ = lean_ctor_get(v_c_2069_, 0);
lean_inc_ref(v_p_2073_);
lean_dec_ref(v_c_2069_);
v___x_2074_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_2073_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2084_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2084_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2084_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2079_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_2080_ = l_Lean_mkIntLE(v_a_2075_, v___x_2079_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2080_);
v___x_2082_ = v___x_2077_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
else
{
return v___x_2074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg___boxed(lean_object* v_c_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_2085_, v_a_2086_, v_a_2087_);
lean_dec_ref(v_a_2087_);
lean_dec(v_a_2086_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(lean_object* v_c_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_2090_, v_a_2091_, v_a_2099_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___boxed(lean_object* v_c_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(v_c_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(lean_object* v_c_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_2116_, v_a_2117_, v_a_2120_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
v___x_2125_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_2126_ = l_Lean_indentD(v_a_2124_);
v___x_2127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2125_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2127_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
return v___x_2128_;
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
v_a_2129_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2123_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2123_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(lean_object* v_00_u03b1_2145_, lean_object* v_c_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_2146_, v_a_2147_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_2159_, lean_object* v_c_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(v_00_u03b1_2159_, v_c_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
lean_dec(v_a_2170_);
lean_dec_ref(v_a_2169_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec(v_a_2161_);
return v_res_2172_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(lean_object* v_c_2173_){
_start:
{
lean_object* v_p_2174_; 
v_p_2174_ = lean_ctor_get(v_c_2173_, 0);
if (lean_obj_tag(v_p_2174_) == 0)
{
lean_object* v_k_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v_k_2175_ = lean_ctor_get(v_p_2174_, 0);
v___x_2176_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_2177_ = lean_int_dec_eq(v_k_2175_, v___x_2176_);
return v___x_2177_;
}
else
{
uint8_t v___x_2178_; 
v___x_2178_ = 0;
return v___x_2178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial___boxed(lean_object* v_c_2179_){
_start:
{
uint8_t v_res_2180_; lean_object* v_r_2181_; 
v_res_2180_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(v_c_2179_);
lean_dec_ref(v_c_2179_);
v_r_2181_ = lean_box(v_res_2180_);
return v_r_2181_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0));
v___x_2184_ = l_Lean_stringToMessageData(v___x_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object* v_c_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_){
_start:
{
lean_object* v_p_2189_; lean_object* v___x_2190_; 
v_p_2189_ = lean_ctor_get(v_c_2185_, 0);
lean_inc_ref(v_p_2189_);
lean_dec_ref(v_c_2185_);
v___x_2190_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_2189_, v_a_2186_, v_a_2187_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2200_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2200_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2200_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2195_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1);
v___x_2196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2196_, 0, v_a_2191_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2196_);
v___x_2198_ = v___x_2193_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
else
{
return v___x_2190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___boxed(lean_object* v_c_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_2201_, v_a_2202_, v_a_2203_);
lean_dec_ref(v_a_2203_);
lean_dec(v_a_2202_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(lean_object* v_c_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_2206_, v_a_2207_, v_a_2215_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___boxed(lean_object* v_c_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(v_c_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec(v_a_2220_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(lean_object* v_c_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v_p_2236_; lean_object* v___x_2237_; 
v_p_2236_ = lean_ctor_get(v_c_2232_, 0);
lean_inc_ref(v_p_2236_);
lean_dec_ref(v_c_2232_);
v___x_2237_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_2236_, v_a_2233_, v_a_2234_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2247_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2247_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2247_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2245_; 
v___x_2242_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_2243_ = l_Lean_mkIntEq(v_a_2238_, v___x_2242_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v___x_2243_);
v___x_2245_ = v___x_2240_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
else
{
return v___x_2237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_2248_, v_a_2249_, v_a_2250_);
lean_dec_ref(v_a_2250_);
lean_dec(v_a_2249_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(lean_object* v_c_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_2253_, v_a_2254_, v_a_2262_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___boxed(lean_object* v_c_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(v_c_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
lean_dec(v_a_2272_);
lean_dec_ref(v_a_2271_);
lean_dec(v_a_2270_);
lean_dec_ref(v_a_2269_);
lean_dec(v_a_2268_);
lean_dec(v_a_2267_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(lean_object* v_c_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_2279_, v_a_2280_, v_a_2283_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2286_, 1);
v___x_2288_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_2289_ = l_Lean_indentD(v_a_2287_);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2288_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2290_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_);
return v___x_2291_;
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
v_a_2292_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2286_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2286_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec(v_a_2301_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(lean_object* v_00_u03b1_2308_, lean_object* v_c_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_2309_, v_a_2310_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_2322_, lean_object* v_c_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(v_00_u03b1_2322_, v_c_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(lean_object* v_x_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v___x_2340_; 
v___x_2340_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2337_, v_a_2338_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2357_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2343_ = v___x_2340_;
v_isShared_2344_ = v_isSharedCheck_2357_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2340_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2357_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v_occurs_2345_; lean_object* v_size_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v_occurs_2345_ = lean_ctor_get(v_a_2341_, 11);
lean_inc_ref(v_occurs_2345_);
lean_dec(v_a_2341_);
v_size_2346_ = lean_ctor_get(v_occurs_2345_, 2);
v___x_2347_ = lean_box(1);
v___x_2348_ = lean_nat_dec_lt(v_x_2336_, v_size_2346_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; lean_object* v___x_2351_; 
lean_dec_ref(v_occurs_2345_);
v___x_2349_ = l_outOfBounds___redArg(v___x_2347_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v___x_2349_);
v___x_2351_ = v___x_2343_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2353_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2347_, v_occurs_2345_, v_x_2336_);
lean_dec_ref(v_occurs_2345_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v___x_2353_);
v___x_2355_ = v___x_2343_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
v_a_2358_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2340_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2340_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg___boxed(lean_object* v_x_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2366_, v_a_2367_, v_a_2368_);
lean_dec_ref(v_a_2368_);
lean_dec(v_a_2367_);
lean_dec(v_x_2366_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(lean_object* v_x_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2371_, v_a_2372_, v_a_2380_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___boxed(lean_object* v_x_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(v_x_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec(v_x_2384_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(lean_object* v_k_2397_, lean_object* v_v_2398_, lean_object* v_t_2399_){
_start:
{
if (lean_obj_tag(v_t_2399_) == 0)
{
lean_object* v_size_2400_; lean_object* v_k_2401_; lean_object* v_v_2402_; lean_object* v_l_2403_; lean_object* v_r_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2685_; 
v_size_2400_ = lean_ctor_get(v_t_2399_, 0);
v_k_2401_ = lean_ctor_get(v_t_2399_, 1);
v_v_2402_ = lean_ctor_get(v_t_2399_, 2);
v_l_2403_ = lean_ctor_get(v_t_2399_, 3);
v_r_2404_ = lean_ctor_get(v_t_2399_, 4);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_t_2399_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2406_ = v_t_2399_;
v_isShared_2407_ = v_isSharedCheck_2685_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_r_2404_);
lean_inc(v_l_2403_);
lean_inc(v_v_2402_);
lean_inc(v_k_2401_);
lean_inc(v_size_2400_);
lean_dec(v_t_2399_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2685_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
uint8_t v___x_2408_; 
v___x_2408_ = lean_nat_dec_lt(v_k_2397_, v_k_2401_);
if (v___x_2408_ == 0)
{
uint8_t v___x_2409_; 
v___x_2409_ = lean_nat_dec_eq(v_k_2397_, v_k_2401_);
if (v___x_2409_ == 0)
{
lean_object* v_impl_2410_; lean_object* v___x_2411_; 
lean_dec(v_size_2400_);
v_impl_2410_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2397_, v_v_2398_, v_r_2404_);
v___x_2411_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2403_) == 0)
{
lean_object* v_size_2412_; lean_object* v_size_2413_; lean_object* v_k_2414_; lean_object* v_v_2415_; lean_object* v_l_2416_; lean_object* v_r_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v_size_2412_ = lean_ctor_get(v_l_2403_, 0);
v_size_2413_ = lean_ctor_get(v_impl_2410_, 0);
v_k_2414_ = lean_ctor_get(v_impl_2410_, 1);
v_v_2415_ = lean_ctor_get(v_impl_2410_, 2);
v_l_2416_ = lean_ctor_get(v_impl_2410_, 3);
lean_inc(v_l_2416_);
v_r_2417_ = lean_ctor_get(v_impl_2410_, 4);
v___x_2418_ = lean_unsigned_to_nat(3u);
v___x_2419_ = lean_nat_mul(v___x_2418_, v_size_2412_);
v___x_2420_ = lean_nat_dec_lt(v___x_2419_, v_size_2413_);
lean_dec(v___x_2419_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2424_; 
lean_dec(v_l_2416_);
v___x_2421_ = lean_nat_add(v___x_2411_, v_size_2412_);
v___x_2422_ = lean_nat_add(v___x_2421_, v_size_2413_);
lean_dec(v___x_2421_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 4, v_impl_2410_);
lean_ctor_set(v___x_2406_, 0, v___x_2422_);
v___x_2424_ = v___x_2406_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2422_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_k_2401_);
lean_ctor_set(v_reuseFailAlloc_2425_, 2, v_v_2402_);
lean_ctor_set(v_reuseFailAlloc_2425_, 3, v_l_2403_);
lean_ctor_set(v_reuseFailAlloc_2425_, 4, v_impl_2410_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
else
{
lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2489_; 
lean_inc(v_r_2417_);
lean_inc(v_v_2415_);
lean_inc(v_k_2414_);
lean_inc(v_size_2413_);
v_isSharedCheck_2489_ = !lean_is_exclusive(v_impl_2410_);
if (v_isSharedCheck_2489_ == 0)
{
lean_object* v_unused_2490_; lean_object* v_unused_2491_; lean_object* v_unused_2492_; lean_object* v_unused_2493_; lean_object* v_unused_2494_; 
v_unused_2490_ = lean_ctor_get(v_impl_2410_, 4);
lean_dec(v_unused_2490_);
v_unused_2491_ = lean_ctor_get(v_impl_2410_, 3);
lean_dec(v_unused_2491_);
v_unused_2492_ = lean_ctor_get(v_impl_2410_, 2);
lean_dec(v_unused_2492_);
v_unused_2493_ = lean_ctor_get(v_impl_2410_, 1);
lean_dec(v_unused_2493_);
v_unused_2494_ = lean_ctor_get(v_impl_2410_, 0);
lean_dec(v_unused_2494_);
v___x_2427_ = v_impl_2410_;
v_isShared_2428_ = v_isSharedCheck_2489_;
goto v_resetjp_2426_;
}
else
{
lean_dec(v_impl_2410_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2489_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v_size_2429_; lean_object* v_k_2430_; lean_object* v_v_2431_; lean_object* v_l_2432_; lean_object* v_r_2433_; lean_object* v_size_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; uint8_t v___x_2437_; 
v_size_2429_ = lean_ctor_get(v_l_2416_, 0);
v_k_2430_ = lean_ctor_get(v_l_2416_, 1);
v_v_2431_ = lean_ctor_get(v_l_2416_, 2);
v_l_2432_ = lean_ctor_get(v_l_2416_, 3);
v_r_2433_ = lean_ctor_get(v_l_2416_, 4);
v_size_2434_ = lean_ctor_get(v_r_2417_, 0);
v___x_2435_ = lean_unsigned_to_nat(2u);
v___x_2436_ = lean_nat_mul(v___x_2435_, v_size_2434_);
v___x_2437_ = lean_nat_dec_lt(v_size_2429_, v___x_2436_);
lean_dec(v___x_2436_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2465_; 
lean_inc(v_r_2433_);
lean_inc(v_l_2432_);
lean_inc(v_v_2431_);
lean_inc(v_k_2430_);
v_isSharedCheck_2465_ = !lean_is_exclusive(v_l_2416_);
if (v_isSharedCheck_2465_ == 0)
{
lean_object* v_unused_2466_; lean_object* v_unused_2467_; lean_object* v_unused_2468_; lean_object* v_unused_2469_; lean_object* v_unused_2470_; 
v_unused_2466_ = lean_ctor_get(v_l_2416_, 4);
lean_dec(v_unused_2466_);
v_unused_2467_ = lean_ctor_get(v_l_2416_, 3);
lean_dec(v_unused_2467_);
v_unused_2468_ = lean_ctor_get(v_l_2416_, 2);
lean_dec(v_unused_2468_);
v_unused_2469_ = lean_ctor_get(v_l_2416_, 1);
lean_dec(v_unused_2469_);
v_unused_2470_ = lean_ctor_get(v_l_2416_, 0);
lean_dec(v_unused_2470_);
v___x_2439_ = v_l_2416_;
v_isShared_2440_ = v_isSharedCheck_2465_;
goto v_resetjp_2438_;
}
else
{
lean_dec(v_l_2416_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2465_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2455_; 
v___x_2441_ = lean_nat_add(v___x_2411_, v_size_2412_);
v___x_2442_ = lean_nat_add(v___x_2441_, v_size_2413_);
lean_dec(v_size_2413_);
if (lean_obj_tag(v_l_2432_) == 0)
{
lean_object* v_size_2463_; 
v_size_2463_ = lean_ctor_get(v_l_2432_, 0);
lean_inc(v_size_2463_);
v___y_2455_ = v_size_2463_;
goto v___jp_2454_;
}
else
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_unsigned_to_nat(0u);
v___y_2455_ = v___x_2464_;
goto v___jp_2454_;
}
v___jp_2443_:
{
lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2447_ = lean_nat_add(v___y_2444_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec(v___y_2444_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 4, v_r_2417_);
lean_ctor_set(v___x_2439_, 3, v_r_2433_);
lean_ctor_set(v___x_2439_, 2, v_v_2415_);
lean_ctor_set(v___x_2439_, 1, v_k_2414_);
lean_ctor_set(v___x_2439_, 0, v___x_2447_);
v___x_2449_ = v___x_2439_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2447_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_k_2414_);
lean_ctor_set(v_reuseFailAlloc_2453_, 2, v_v_2415_);
lean_ctor_set(v_reuseFailAlloc_2453_, 3, v_r_2433_);
lean_ctor_set(v_reuseFailAlloc_2453_, 4, v_r_2417_);
v___x_2449_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2451_; 
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 4, v___x_2449_);
lean_ctor_set(v___x_2427_, 3, v___y_2445_);
lean_ctor_set(v___x_2427_, 2, v_v_2431_);
lean_ctor_set(v___x_2427_, 1, v_k_2430_);
lean_ctor_set(v___x_2427_, 0, v___x_2442_);
v___x_2451_ = v___x_2427_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_k_2430_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v_v_2431_);
lean_ctor_set(v_reuseFailAlloc_2452_, 3, v___y_2445_);
lean_ctor_set(v_reuseFailAlloc_2452_, 4, v___x_2449_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
v___jp_2454_:
{
lean_object* v___x_2456_; lean_object* v___x_2458_; 
v___x_2456_ = lean_nat_add(v___x_2441_, v___y_2455_);
lean_dec(v___y_2455_);
lean_dec(v___x_2441_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 4, v_l_2432_);
lean_ctor_set(v___x_2406_, 0, v___x_2456_);
v___x_2458_ = v___x_2406_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2456_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v_k_2401_);
lean_ctor_set(v_reuseFailAlloc_2462_, 2, v_v_2402_);
lean_ctor_set(v_reuseFailAlloc_2462_, 3, v_l_2403_);
lean_ctor_set(v_reuseFailAlloc_2462_, 4, v_l_2432_);
v___x_2458_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_nat_add(v___x_2411_, v_size_2434_);
if (lean_obj_tag(v_r_2433_) == 0)
{
lean_object* v_size_2460_; 
v_size_2460_ = lean_ctor_get(v_r_2433_, 0);
lean_inc(v_size_2460_);
v___y_2444_ = v___x_2459_;
v___y_2445_ = v___x_2458_;
v___y_2446_ = v_size_2460_;
goto v___jp_2443_;
}
else
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_unsigned_to_nat(0u);
v___y_2444_ = v___x_2459_;
v___y_2445_ = v___x_2458_;
v___y_2446_ = v___x_2461_;
goto v___jp_2443_;
}
}
}
}
}
else
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2475_; 
lean_del_object(v___x_2406_);
v___x_2471_ = lean_nat_add(v___x_2411_, v_size_2412_);
v___x_2472_ = lean_nat_add(v___x_2471_, v_size_2413_);
lean_dec(v_size_2413_);
v___x_2473_ = lean_nat_add(v___x_2471_, v_size_2429_);
lean_dec(v___x_2471_);
lean_inc_ref(v_l_2403_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 4, v_l_2416_);
lean_ctor_set(v___x_2427_, 3, v_l_2403_);
lean_ctor_set(v___x_2427_, 2, v_v_2402_);
lean_ctor_set(v___x_2427_, 1, v_k_2401_);
lean_ctor_set(v___x_2427_, 0, v___x_2473_);
v___x_2475_ = v___x_2427_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v_k_2401_);
lean_ctor_set(v_reuseFailAlloc_2488_, 2, v_v_2402_);
lean_ctor_set(v_reuseFailAlloc_2488_, 3, v_l_2403_);
lean_ctor_set(v_reuseFailAlloc_2488_, 4, v_l_2416_);
v___x_2475_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
v_isSharedCheck_2482_ = !lean_is_exclusive(v_l_2403_);
if (v_isSharedCheck_2482_ == 0)
{
lean_object* v_unused_2483_; lean_object* v_unused_2484_; lean_object* v_unused_2485_; lean_object* v_unused_2486_; lean_object* v_unused_2487_; 
v_unused_2483_ = lean_ctor_get(v_l_2403_, 4);
lean_dec(v_unused_2483_);
v_unused_2484_ = lean_ctor_get(v_l_2403_, 3);
lean_dec(v_unused_2484_);
v_unused_2485_ = lean_ctor_get(v_l_2403_, 2);
lean_dec(v_unused_2485_);
v_unused_2486_ = lean_ctor_get(v_l_2403_, 1);
lean_dec(v_unused_2486_);
v_unused_2487_ = lean_ctor_get(v_l_2403_, 0);
lean_dec(v_unused_2487_);
v___x_2477_ = v_l_2403_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_dec(v_l_2403_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 4, v_r_2417_);
lean_ctor_set(v___x_2477_, 3, v___x_2475_);
lean_ctor_set(v___x_2477_, 2, v_v_2415_);
lean_ctor_set(v___x_2477_, 1, v_k_2414_);
lean_ctor_set(v___x_2477_, 0, v___x_2472_);
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v_k_2414_);
lean_ctor_set(v_reuseFailAlloc_2481_, 2, v_v_2415_);
lean_ctor_set(v_reuseFailAlloc_2481_, 3, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2481_, 4, v_r_2417_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2495_; 
v_l_2495_ = lean_ctor_get(v_impl_2410_, 3);
lean_inc(v_l_2495_);
if (lean_obj_tag(v_l_2495_) == 0)
{
lean_object* v_r_2496_; lean_object* v_k_2497_; lean_object* v_v_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2521_; 
v_r_2496_ = lean_ctor_get(v_impl_2410_, 4);
v_k_2497_ = lean_ctor_get(v_impl_2410_, 1);
v_v_2498_ = lean_ctor_get(v_impl_2410_, 2);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_impl_2410_);
if (v_isSharedCheck_2521_ == 0)
{
lean_object* v_unused_2522_; lean_object* v_unused_2523_; 
v_unused_2522_ = lean_ctor_get(v_impl_2410_, 3);
lean_dec(v_unused_2522_);
v_unused_2523_ = lean_ctor_get(v_impl_2410_, 0);
lean_dec(v_unused_2523_);
v___x_2500_ = v_impl_2410_;
v_isShared_2501_ = v_isSharedCheck_2521_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_r_2496_);
lean_inc(v_v_2498_);
lean_inc(v_k_2497_);
lean_dec(v_impl_2410_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2521_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v_k_2502_; lean_object* v_v_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2517_; 
v_k_2502_ = lean_ctor_get(v_l_2495_, 1);
v_v_2503_ = lean_ctor_get(v_l_2495_, 2);
v_isSharedCheck_2517_ = !lean_is_exclusive(v_l_2495_);
if (v_isSharedCheck_2517_ == 0)
{
lean_object* v_unused_2518_; lean_object* v_unused_2519_; lean_object* v_unused_2520_; 
v_unused_2518_ = lean_ctor_get(v_l_2495_, 4);
lean_dec(v_unused_2518_);
v_unused_2519_ = lean_ctor_get(v_l_2495_, 3);
lean_dec(v_unused_2519_);
v_unused_2520_ = lean_ctor_get(v_l_2495_, 0);
lean_dec(v_unused_2520_);
v___x_2505_ = v_l_2495_;
v_isShared_2506_ = v_isSharedCheck_2517_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_v_2503_);
lean_inc(v_k_2502_);
lean_dec(v_l_2495_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2517_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2507_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2496_, 2);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 4, v_r_2496_);
lean_ctor_set(v___x_2505_, 3, v_r_2496_);
lean_ctor_set(v___x_2505_, 2, v_v_2402_);
lean_ctor_set(v___x_2505_, 1, v_k_2401_);
lean_ctor_set(v___x_2505_, 0, v___x_2411_);
v___x_2509_ = v___x_2505_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v_k_2401_);
lean_ctor_set(v_reuseFailAlloc_2516_, 2, v_v_2402_);
lean_ctor_set(v_reuseFailAlloc_2516_, 3, v_r_2496_);
lean_ctor_set(v_reuseFailAlloc_2516_, 4, v_r_2496_);
v___x_2509_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2511_; 
lean_inc(v_r_2496_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 3, v_r_2496_);
lean_ctor_set(v___x_2500_, 0, v___x_2411_);
v___x_2511_ = v___x_2500_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_k_2497_);
lean_ctor_set(v_reuseFailAlloc_2515_, 2, v_v_2498_);
lean_ctor_set(v_reuseFailAlloc_2515_, 3, v_r_2496_);
lean_ctor_set(v_reuseFailAlloc_2515_, 4, v_r_2496_);
v___x_2511_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2513_; 
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 4, v___x_2511_);
lean_ctor_set(v___x_2406_, 3, v___x_2509_);
lean_ctor_set(v___x_2406_, 2, v_v_2503_);
lean_ctor_set(v___x_2406_, 1, v_k_2502_);
lean_ctor_set(v___x_2406_, 0, v___x_2507_);
v___x_2513_ = v___x_2406_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_k_2502_);
lean_ctor_set(v_reuseFailAlloc_2514_, 2, v_v_2503_);
lean_ctor_set(v_reuseFailAlloc_2514_, 3, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2514_, 4, v___x_2511_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
}
}
else
{
lean_object* v_r_2524_; 
v_r_2524_ = lean_ctor_get(v_impl_2410_, 4);
lean_inc(v_r_2524_);
if (lean_obj_tag(v_r_2524_) == 0)
{
lean_object* v_k_2525_; lean_object* v_v_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2537_; 
v_k_2525_ = lean_ctor_get(v_impl_2410_, 1);
v_v_2526_ = lean_ctor_get(v_impl_2410_, 2);
v_isSharedCheck_2537_ = !lean_is_exclusive(v_impl_2410_);
if (v_isSharedCheck_2537_ == 0)
{
lean_object* v_unused_2538_; lean_object* v_unused_2539_; lean_object* v_unused_2540_; 
v_unused_2538_ = lean_ctor_get(v_impl_2410_, 4);
lean_dec(v_unused_2538_);
v_unused_2539_ = lean_ctor_get(v_impl_2410_, 3);
lean_dec(v_unused_2539_);
v_unused_2540_ = lean_ctor_get(v_impl_2410_, 0);
lean_dec(v_unused_2540_);
v___x_2528_ = v_impl_2410_;
v_isShared_2529_ = v_isSharedCheck_2537_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_v_2526_);
lean_inc(v_k_2525_);
lean_dec(v_impl_2410_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2537_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2530_ = lean_unsigned_to_nat(3u);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 4, v_l_2495_);
lean_ctor_set(v___x_2528_, 2, v_v_2402_);
lean_ctor_set(v___x_2528_, 1, v_k_2401_);
lean_ctor_set(v___x_2528_, 0, v___x_2411_);
v___x_2532_ = v___x_2528_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_k_2401_);
lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_v_2402_);
lean_ctor_set(v_reuseFailAlloc_2536_, 3, v_l_2495_);
lean_ctor_set(v_reuseFailAlloc_2536_, 4, v_l_2495_);
v___x_2532_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
lean_object* v___x_2534_; 
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 4, v_r_2524_);
lean_ctor_set(v___x_2406_, 3, v___x_2532_);
lean_ctor_set(v___x_2406_, 2, v_v_2526_);
lean_ctor_set(v___x_2406_, 1, v_k_2525_);
lean_ctor_set(v___x_2406_, 0, v___x_2530_);
v___x_2534_ = v___x_2406_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2530_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_k_2525_);
lean_ctor_set(v_reuseFailAlloc_2535_, 2, v_v_2526_);
lean_ctor_set(v_reuseFailAlloc_2535_, 3, v___x_2532_);
lean_ctor_set(v_reuseFailAlloc_2535_, 4, v_r_2524_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2543_; 
v___x_2541_ = lean_unsigned_to_nat(2u);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 4, v_impl_2410_);
lean_ctor_set(v___x_2406_, 3, v_r_2524_);
lean_ctor_set(v___x_2406_, 0, v___x_2541_);
v___x_2543_ = v___x_2406_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2541_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_k_2401_);
lean_ctor_set(v_reuseFailAlloc_2544_, 2, v_v_2402_);
lean_ctor_set(v_reuseFailAlloc_2544_, 3, v_r_2524_);
lean_ctor_set(v_reuseFailAlloc_2544_, 4, v_impl_2410_);
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
else
{
lean_object* v___x_2546_; 
lean_dec(v_v_2402_);
lean_dec(v_k_2401_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 2, v_v_2398_);
lean_ctor_set(v___x_2406_, 1, v_k_2397_);
v___x_2546_ = v___x_2406_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_size_2400_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_k_2397_);
lean_ctor_set(v_reuseFailAlloc_2547_, 2, v_v_2398_);
lean_ctor_set(v_reuseFailAlloc_2547_, 3, v_l_2403_);
lean_ctor_set(v_reuseFailAlloc_2547_, 4, v_r_2404_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
else
{
lean_object* v_impl_2548_; lean_object* v___x_2549_; 
lean_dec(v_size_2400_);
v_impl_2548_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2397_, v_v_2398_, v_l_2403_);
v___x_2549_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2404_) == 0)
{
lean_object* v_size_2550_; lean_object* v_size_2551_; lean_object* v_k_2552_; lean_object* v_v_2553_; lean_object* v_l_2554_; lean_object* v_r_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; 
v_size_2550_ = lean_ctor_get(v_r_2404_, 0);
v_size_2551_ = lean_ctor_get(v_impl_2548_, 0);
v_k_2552_ = lean_ctor_get(v_impl_2548_, 1);
v_v_2553_ = lean_ctor_get(v_impl_2548_, 2);
v_l_2554_ = lean_ctor_get(v_impl_2548_, 3);
v_r_2555_ = lean_ctor_get(v_impl_2548_, 4);
lean_inc(v_r_2555_);
v___x_2556_ = lean_unsigned_to_nat(3u);
v___x_2557_ = lean_nat_mul(v___x_2556_, v_size_2550_);
v___x_2558_ = lean_nat_dec_lt(v___x_2557_, v_size_2551_);
lean_dec(v___x_2557_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2562_; 
lean_dec(v_r_2555_);
v___x_2559_ = lean_nat_add(v___x_2549_, v_size_2551_);
v___x_2560_ = lean_nat_add(v___x_2559_, v_size_2550_);
lean_dec(v___x_2559_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 3, v_impl_2548_);
lean_ctor_set(v___x_2406_, 0, v___x_2560_);
v___x_2562_ = v___x_2406_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_k_2401_);
lean_ctor_set(v_reuseFailAlloc_2563_, 2, v_v_2402_);
lean_ctor_set(v_reuseFailAlloc_2563_, 3, v_impl_2548_);
lean_ctor_set(v_reuseFailAlloc_2563_, 4, v_r_2404_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
else
{
lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2629_; 
lean_inc(v_l_2554_);
lean_inc(v_v_2553_);
lean_inc(v_k_2552_);
lean_inc(v_size_2551_);
v_isSharedCheck_2629_ = !lean_is_exclusive(v_impl_2548_);
if (v_isSharedCheck_2629_ == 0)
{
lean_object* v_unused_2630_; lean_object* v_unused_2631_; lean_object* v_unused_2632_; lean_object* v_unused_2633_; lean_object* v_unused_2634_; 
v_unused_2630_ = lean_ctor_get(v_impl_2548_, 4);
lean_dec(v_unused_2630_);
v_unused_2631_ = lean_ctor_get(v_impl_2548_, 3);
lean_dec(v_unused_2631_);
v_unused_2632_ = lean_ctor_get(v_impl_2548_, 2);
lean_dec(v_unused_2632_);
v_unused_2633_ = lean_ctor_get(v_impl_2548_, 1);
lean_dec(v_unused_2633_);
v_unused_2634_ = lean_ctor_get(v_impl_2548_, 0);
lean_dec(v_unused_2634_);
v___x_2565_ = v_impl_2548_;
v_isShared_2566_ = v_isSharedCheck_2629_;
goto v_resetjp_2564_;
}
else
{
lean_dec(v_impl_2548_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2629_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v_size_2567_; lean_object* v_size_2568_; lean_object* v_k_2569_; lean_object* v_v_2570_; lean_object* v_l_2571_; lean_object* v_r_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v_size_2567_ = lean_ctor_get(v_l_2554_, 0);
v_size_2568_ = lean_ctor_get(v_r_2555_, 0);
v_k_2569_ = lean_ctor_get(v_r_2555_, 1);
v_v_2570_ = lean_ctor_get(v_r_2555_, 2);
v_l_2571_ = lean_ctor_get(v_r_2555_, 3);
v_r_2572_ = lean_ctor_get(v_r_2555_, 4);
v___x_2573_ = lean_unsigned_to_nat(2u);
v___x_2574_ = lean_nat_mul(v___x_2573_, v_size_2567_);
v___x_2575_ = lean_nat_dec_lt(v_size_2568_, v___x_2574_);
lean_dec(v___x_2574_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2604_; 
lean_inc(v_r_2572_);
lean_inc(v_l_2571_);
lean_inc(v_v_2570_);
lean_inc(v_k_2569_);
v_isSharedCheck_2604_ = !lean_is_exclusive(v_r_2555_);
if (v_isSharedCheck_2604_ == 0)
{
lean_object* v_unused_2605_; lean_object* v_unused_2606_; lean_object* v_unused_2607_; lean_object* v_unused_2608_; lean_object* v_unused_2609_; 
v_unused_2605_ = lean_ctor_get(v_r_2555_, 4);
lean_dec(v_unused_2605_);
v_unused_2606_ = lean_ctor_get(v_r_2555_, 3);
lean_dec(v_unused_2606_);
v_unused_2607_ = lean_ctor_get(v_r_2555_, 2);
lean_dec(v_unused_2607_);
v_unused_2608_ = lean_ctor_get(v_r_2555_, 1);
lean_dec(v_unused_2608_);
v_unused_2609_ = lean_ctor_get(v_r_2555_, 0);
lean_dec(v_unused_2609_);
v___x_2577_ = v_r_2555_;
v_isShared_2578_ = v_isSharedCheck_2604_;
goto v_resetjp_2576_;
}
else
{
lean_dec(v_r_2555_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2604_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___x_2592_; lean_object* v___y_2594_; 
v___x_2579_ = lean_nat_add(v___x_2549_, v_size_2551_);
lean_dec(v_size_2551_);
v___x_2580_ = lean_nat_add(v___x_2579_, v_size_2550_);
lean_dec(v___x_2579_);
v___x_2592_ = lean_nat_add(v___x_2549_, v_size_2567_);
if (lean_obj_tag(v_l_2571_) == 0)
{
lean_object* v_size_2602_; 
v_size_2602_ = lean_ctor_get(v_l_2571_, 0);
lean_inc(v_size_2602_);
v___y_2594_ = v_size_2602_;
goto v___jp_2593_;
}
else
{
lean_object* v___x_2603_; 
v___x_2603_ = lean_unsigned_to_nat(0u);
v___y_2594_ = v___x_2603_;
goto v___jp_2593_;
}
v___jp_2581_:
{
lean_object* v___x_2585_; lean_object* v___x_2587_; 
v___x_2585_ = lean_nat_add(v___y_2582_, v___y_2584_);
lean_dec(v___y_2584_);
lean_dec(v___y_2582_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 4, v_r_2404_);
lean_ctor_set(v___x_2577_, 3, v_r_2572_);
lean_ctor_set(v___x_2577_, 2, v_v_2402_);
lean_ctor_set(v___x_2577_, 1, v_k_2401_);
lean_ctor_set(v___x_2577_, 0, v___x_2585_);
v___x_2587_ = v___x_2577_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2585_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v_k_2401_);
lean_ctor_set(v_reuseFailAlloc_2591_, 2, v_v_2402_);
lean_ctor_set(v_reuseFailAlloc_2591_, 3, v_r_2572_);
lean_ctor_set(v_reuseFailAlloc_2591_, 4, v_r_2404_);
v___x_2587_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
lean_object* v___x_2589_; 
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 4, v___x_2587_);
lean_ctor_set(v___x_2565_, 3, v___y_2583_);
lean_ctor_set(v___x_2565_, 2, v_v_2570_);
lean_ctor_set(v___x_2565_, 1, v_k_2569_);
lean_ctor_set(v___x_2565_, 0, v___x_2580_);
v___x_2589_ = v___x_2565_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2580_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_k_2569_);
lean_ctor_set(v_reuseFailAlloc_2590_, 2, v_v_2570_);
lean_ctor_set(v_reuseFailAlloc_2590_, 3, v___y_2583_);
lean_ctor_set(v_reuseFailAlloc_2590_, 4, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
v___jp_2593_:
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2595_ = lean_nat_add(v___x_2592_, v___y_2594_);
lean_dec(v___y_2594_);
lean_dec(v___x_2592_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 4, v_l_2571_);
lean_ctor_set(v___x_2406_, 3, v_l_2554_);
lean_ctor_set(v___x_2406_, 2, v_v_2553_);
lean_ctor_set(v___x_2406_, 1, v_k_2552_);
lean_ctor_set(v___x_2406_, 0, v___x_2595_);
v___x_2597_ = v___x_2406_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_2601_, 3, v_l_2554_);
lean_ctor_set(v_reuseFailAlloc_2601_, 4, v_l_2571_);
v___x_2597_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2598_; 
v___x_2598_ = lean_nat_add(v___x_2549_, v_size_2550_);
if (lean_obj_tag(v_r_2572_) == 0)
{
lean_object* v_size_2599_; 
v_size_2599_ = lean_ctor_get(v_r_2572_, 0);
lean_inc(v_size_2599_);
v___y_2582_ = v___x_2598_;
v___y_2583_ = v___x_2597_;
v___y_2584_ = v_size_2599_;
goto v___jp_2581_;
}
else
{
lean_object* v___x_2600_; 
v___x_2600_ = lean_unsigned_to_nat(0u);
v___y_2582_ = v___x_2598_;
v___y_2583_ = v___x_2597_;
v___y_2584_ = v___x_2600_;
goto v___jp_2581_;
}
}
}
}
}
else
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2615_; 
lean_del_object(v___x_2406_);
v___x_2610_ = lean_nat_add(v___x_2549_, v_size_2551_);
lean_dec(v_size_2551_);
v___x_2611_ = lean_nat_add(v___x_2610_, v_size_2550_);
lean_dec(v___x_2610_);
v___x_2612_ = lean_nat_add(v___x_2549_, v_size_2550_);
v___x_2613_ = lean_nat_add(v___x_2612_, v_size_2568_);
lean_dec(v___x_2612_);
lean_inc_ref(v_r_2404_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 4, v_r_2404_);
lean_ctor_set(v___x_2565_, 3, v_r_2555_);
lean_ctor_set(v___x_2565_, 2, v_v_2402_);
lean_ctor_set(v___x_2565_, 1, v_k_2401_);
lean_ctor_set(v___x_2565_, 0, v___x_2613_);
v___x_2615_ = v___x_2565_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2613_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v_k_2401_);
lean_ctor_set(v_reuseFailAlloc_2628_, 2, v_v_2402_);
lean_ctor_set(v_reuseFailAlloc_2628_, 3, v_r_2555_);
lean_ctor_set(v_reuseFailAlloc_2628_, 4, v_r_2404_);
v___x_2615_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
v_isSharedCheck_2622_ = !lean_is_exclusive(v_r_2404_);
if (v_isSharedCheck_2622_ == 0)
{
lean_object* v_unused_2623_; lean_object* v_unused_2624_; lean_object* v_unused_2625_; lean_object* v_unused_2626_; lean_object* v_unused_2627_; 
v_unused_2623_ = lean_ctor_get(v_r_2404_, 4);
lean_dec(v_unused_2623_);
v_unused_2624_ = lean_ctor_get(v_r_2404_, 3);
lean_dec(v_unused_2624_);
v_unused_2625_ = lean_ctor_get(v_r_2404_, 2);
lean_dec(v_unused_2625_);
v_unused_2626_ = lean_ctor_get(v_r_2404_, 1);
lean_dec(v_unused_2626_);
v_unused_2627_ = lean_ctor_get(v_r_2404_, 0);
lean_dec(v_unused_2627_);
v___x_2617_ = v_r_2404_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_dec(v_r_2404_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 4, v___x_2615_);
lean_ctor_set(v___x_2617_, 3, v_l_2554_);
lean_ctor_set(v___x_2617_, 2, v_v_2553_);
lean_ctor_set(v___x_2617_, 1, v_k_2552_);
lean_ctor_set(v___x_2617_, 0, v___x_2611_);
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_k_2552_);
lean_ctor_set(v_reuseFailAlloc_2621_, 2, v_v_2553_);
lean_ctor_set(v_reuseFailAlloc_2621_, 3, v_l_2554_);
lean_ctor_set(v_reuseFailAlloc_2621_, 4, v___x_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2635_; 
v_l_2635_ = lean_ctor_get(v_impl_2548_, 3);
if (lean_obj_tag(v_l_2635_) == 0)
{
lean_object* v_r_2636_; lean_object* v_k_2637_; lean_object* v_v_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2649_; 
lean_inc_ref(v_l_2635_);
v_r_2636_ = lean_ctor_get(v_impl_2548_, 4);
v_k_2637_ = lean_ctor_get(v_impl_2548_, 1);
v_v_2638_ = lean_ctor_get(v_impl_2548_, 2);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_impl_2548_);
if (v_isSharedCheck_2649_ == 0)
{
lean_object* v_unused_2650_; lean_object* v_unused_2651_; 
v_unused_2650_ = lean_ctor_get(v_impl_2548_, 3);
lean_dec(v_unused_2650_);
v_unused_2651_ = lean_ctor_get(v_impl_2548_, 0);
lean_dec(v_unused_2651_);
v___x_2640_ = v_impl_2548_;
v_isShared_2641_ = v_isSharedCheck_2649_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_r_2636_);
lean_inc(v_v_2638_);
lean_inc(v_k_2637_);
lean_dec(v_impl_2548_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2649_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2642_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2636_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 3, v_r_2636_);
lean_ctor_set(v___x_2640_, 2, v_v_2402_);
lean_ctor_set(v___x_2640_, 1, v_k_2401_);
lean_ctor_set(v___x_2640_, 0, v___x_2549_);
v___x_2644_ = v___x_2640_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_k_2401_);
lean_ctor_set(v_reuseFailAlloc_2648_, 2, v_v_2402_);
lean_ctor_set(v_reuseFailAlloc_2648_, 3, v_r_2636_);
lean_ctor_set(v_reuseFailAlloc_2648_, 4, v_r_2636_);
v___x_2644_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
lean_object* v___x_2646_; 
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 4, v___x_2644_);
lean_ctor_set(v___x_2406_, 3, v_l_2635_);
lean_ctor_set(v___x_2406_, 2, v_v_2638_);
lean_ctor_set(v___x_2406_, 1, v_k_2637_);
lean_ctor_set(v___x_2406_, 0, v___x_2642_);
v___x_2646_ = v___x_2406_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v_k_2637_);
lean_ctor_set(v_reuseFailAlloc_2647_, 2, v_v_2638_);
lean_ctor_set(v_reuseFailAlloc_2647_, 3, v_l_2635_);
lean_ctor_set(v_reuseFailAlloc_2647_, 4, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
else
{
lean_object* v_r_2652_; 
v_r_2652_ = lean_ctor_get(v_impl_2548_, 4);
lean_inc(v_r_2652_);
if (lean_obj_tag(v_r_2652_) == 0)
{
lean_object* v_k_2653_; lean_object* v_v_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2677_; 
lean_inc(v_l_2635_);
v_k_2653_ = lean_ctor_get(v_impl_2548_, 1);
v_v_2654_ = lean_ctor_get(v_impl_2548_, 2);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_impl_2548_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; lean_object* v_unused_2679_; lean_object* v_unused_2680_; 
v_unused_2678_ = lean_ctor_get(v_impl_2548_, 4);
lean_dec(v_unused_2678_);
v_unused_2679_ = lean_ctor_get(v_impl_2548_, 3);
lean_dec(v_unused_2679_);
v_unused_2680_ = lean_ctor_get(v_impl_2548_, 0);
lean_dec(v_unused_2680_);
v___x_2656_ = v_impl_2548_;
v_isShared_2657_ = v_isSharedCheck_2677_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_v_2654_);
lean_inc(v_k_2653_);
lean_dec(v_impl_2548_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2677_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v_k_2658_; lean_object* v_v_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2673_; 
v_k_2658_ = lean_ctor_get(v_r_2652_, 1);
v_v_2659_ = lean_ctor_get(v_r_2652_, 2);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_r_2652_);
if (v_isSharedCheck_2673_ == 0)
{
lean_object* v_unused_2674_; lean_object* v_unused_2675_; lean_object* v_unused_2676_; 
v_unused_2674_ = lean_ctor_get(v_r_2652_, 4);
lean_dec(v_unused_2674_);
v_unused_2675_ = lean_ctor_get(v_r_2652_, 3);
lean_dec(v_unused_2675_);
v_unused_2676_ = lean_ctor_get(v_r_2652_, 0);
lean_dec(v_unused_2676_);
v___x_2661_ = v_r_2652_;
v_isShared_2662_ = v_isSharedCheck_2673_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_v_2659_);
lean_inc(v_k_2658_);
lean_dec(v_r_2652_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2673_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2663_; lean_object* v___x_2665_; 
v___x_2663_ = lean_unsigned_to_nat(3u);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 4, v_l_2635_);
lean_ctor_set(v___x_2661_, 3, v_l_2635_);
lean_ctor_set(v___x_2661_, 2, v_v_2654_);
lean_ctor_set(v___x_2661_, 1, v_k_2653_);
lean_ctor_set(v___x_2661_, 0, v___x_2549_);
v___x_2665_ = v___x_2661_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v_k_2653_);
lean_ctor_set(v_reuseFailAlloc_2672_, 2, v_v_2654_);
lean_ctor_set(v_reuseFailAlloc_2672_, 3, v_l_2635_);
lean_ctor_set(v_reuseFailAlloc_2672_, 4, v_l_2635_);
v___x_2665_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2667_; 
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 4, v_l_2635_);
lean_ctor_set(v___x_2656_, 2, v_v_2402_);
lean_ctor_set(v___x_2656_, 1, v_k_2401_);
lean_ctor_set(v___x_2656_, 0, v___x_2549_);
v___x_2667_ = v___x_2656_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_k_2401_);
lean_ctor_set(v_reuseFailAlloc_2671_, 2, v_v_2402_);
lean_ctor_set(v_reuseFailAlloc_2671_, 3, v_l_2635_);
lean_ctor_set(v_reuseFailAlloc_2671_, 4, v_l_2635_);
v___x_2667_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2669_; 
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 4, v___x_2667_);
lean_ctor_set(v___x_2406_, 3, v___x_2665_);
lean_ctor_set(v___x_2406_, 2, v_v_2659_);
lean_ctor_set(v___x_2406_, 1, v_k_2658_);
lean_ctor_set(v___x_2406_, 0, v___x_2663_);
v___x_2669_ = v___x_2406_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2663_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_k_2658_);
lean_ctor_set(v_reuseFailAlloc_2670_, 2, v_v_2659_);
lean_ctor_set(v_reuseFailAlloc_2670_, 3, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2670_, 4, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
}
else
{
lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2681_ = lean_unsigned_to_nat(2u);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 4, v_r_2652_);
lean_ctor_set(v___x_2406_, 3, v_impl_2548_);
lean_ctor_set(v___x_2406_, 0, v___x_2681_);
v___x_2683_ = v___x_2406_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_k_2401_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v_v_2402_);
lean_ctor_set(v_reuseFailAlloc_2684_, 3, v_impl_2548_);
lean_ctor_set(v_reuseFailAlloc_2684_, 4, v_r_2652_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = lean_unsigned_to_nat(1u);
v___x_2687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2686_);
lean_ctor_set(v___x_2687_, 1, v_k_2397_);
lean_ctor_set(v___x_2687_, 2, v_v_2398_);
lean_ctor_set(v___x_2687_, 3, v_t_2399_);
lean_ctor_set(v___x_2687_, 4, v_t_2399_);
return v___x_2687_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(lean_object* v_k_2688_, lean_object* v_t_2689_){
_start:
{
if (lean_obj_tag(v_t_2689_) == 0)
{
lean_object* v_k_2690_; lean_object* v_l_2691_; lean_object* v_r_2692_; uint8_t v___x_2693_; 
v_k_2690_ = lean_ctor_get(v_t_2689_, 1);
v_l_2691_ = lean_ctor_get(v_t_2689_, 3);
v_r_2692_ = lean_ctor_get(v_t_2689_, 4);
v___x_2693_ = lean_nat_dec_lt(v_k_2688_, v_k_2690_);
if (v___x_2693_ == 0)
{
uint8_t v___x_2694_; 
v___x_2694_ = lean_nat_dec_eq(v_k_2688_, v_k_2690_);
if (v___x_2694_ == 0)
{
v_t_2689_ = v_r_2692_;
goto _start;
}
else
{
return v___x_2694_;
}
}
else
{
v_t_2689_ = v_l_2691_;
goto _start;
}
}
else
{
uint8_t v___x_2697_; 
v___x_2697_ = 0;
return v___x_2697_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg___boxed(lean_object* v_k_2698_, lean_object* v_t_2699_){
_start:
{
uint8_t v_res_2700_; lean_object* v_r_2701_; 
v_res_2700_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2698_, v_t_2699_);
lean_dec(v_t_2699_);
lean_dec(v_k_2698_);
v_r_2701_ = lean_box(v_res_2700_);
return v_r_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(lean_object* v_y_2702_, lean_object* v_x_2703_, size_t v_x_2704_, size_t v_x_2705_){
_start:
{
if (lean_obj_tag(v_x_2703_) == 0)
{
lean_object* v_cs_2706_; size_t v_j_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; uint8_t v___x_2710_; 
v_cs_2706_ = lean_ctor_get(v_x_2703_, 0);
v_j_2707_ = lean_usize_shift_right(v_x_2704_, v_x_2705_);
v___x_2708_ = lean_usize_to_nat(v_j_2707_);
v___x_2709_ = lean_array_get_size(v_cs_2706_);
v___x_2710_ = lean_nat_dec_lt(v___x_2708_, v___x_2709_);
if (v___x_2710_ == 0)
{
lean_dec(v___x_2708_);
lean_dec(v_y_2702_);
return v_x_2703_;
}
else
{
lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2728_; 
lean_inc_ref(v_cs_2706_);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_x_2703_);
if (v_isSharedCheck_2728_ == 0)
{
lean_object* v_unused_2729_; 
v_unused_2729_ = lean_ctor_get(v_x_2703_, 0);
lean_dec(v_unused_2729_);
v___x_2712_ = v_x_2703_;
v_isShared_2713_ = v_isSharedCheck_2728_;
goto v_resetjp_2711_;
}
else
{
lean_dec(v_x_2703_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2728_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
size_t v___x_2714_; size_t v___x_2715_; size_t v___x_2716_; size_t v_i_2717_; size_t v___x_2718_; size_t v_shift_2719_; lean_object* v_v_2720_; lean_object* v___x_2721_; lean_object* v_xs_x27_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2726_; 
v___x_2714_ = ((size_t)1ULL);
v___x_2715_ = lean_usize_shift_left(v___x_2714_, v_x_2705_);
v___x_2716_ = lean_usize_sub(v___x_2715_, v___x_2714_);
v_i_2717_ = lean_usize_land(v_x_2704_, v___x_2716_);
v___x_2718_ = ((size_t)5ULL);
v_shift_2719_ = lean_usize_sub(v_x_2705_, v___x_2718_);
v_v_2720_ = lean_array_fget(v_cs_2706_, v___x_2708_);
v___x_2721_ = lean_box(0);
v_xs_x27_2722_ = lean_array_fset(v_cs_2706_, v___x_2708_, v___x_2721_);
v___x_2723_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2702_, v_v_2720_, v_i_2717_, v_shift_2719_);
v___x_2724_ = lean_array_fset(v_xs_x27_2722_, v___x_2708_, v___x_2723_);
lean_dec(v___x_2708_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v___x_2724_);
v___x_2726_ = v___x_2712_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2724_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
else
{
lean_object* v_vs_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; 
v_vs_2730_ = lean_ctor_get(v_x_2703_, 0);
v___x_2731_ = lean_usize_to_nat(v_x_2704_);
v___x_2732_ = lean_array_get_size(v_vs_2730_);
v___x_2733_ = lean_nat_dec_lt(v___x_2731_, v___x_2732_);
if (v___x_2733_ == 0)
{
lean_dec(v___x_2731_);
lean_dec(v_y_2702_);
return v_x_2703_;
}
else
{
lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2748_; 
lean_inc_ref(v_vs_2730_);
v_isSharedCheck_2748_ = !lean_is_exclusive(v_x_2703_);
if (v_isSharedCheck_2748_ == 0)
{
lean_object* v_unused_2749_; 
v_unused_2749_ = lean_ctor_get(v_x_2703_, 0);
lean_dec(v_unused_2749_);
v___x_2735_ = v_x_2703_;
v_isShared_2736_ = v_isSharedCheck_2748_;
goto v_resetjp_2734_;
}
else
{
lean_dec(v_x_2703_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2748_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v_v_2737_; lean_object* v___x_2738_; lean_object* v_xs_x27_2739_; lean_object* v___y_2741_; uint8_t v___x_2746_; 
v_v_2737_ = lean_array_fget(v_vs_2730_, v___x_2731_);
v___x_2738_ = lean_box(0);
v_xs_x27_2739_ = lean_array_fset(v_vs_2730_, v___x_2731_, v___x_2738_);
v___x_2746_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2702_, v_v_2737_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2702_, v___x_2738_, v_v_2737_);
v___y_2741_ = v___x_2747_;
goto v___jp_2740_;
}
else
{
lean_dec(v_y_2702_);
v___y_2741_ = v_v_2737_;
goto v___jp_2740_;
}
v___jp_2740_:
{
lean_object* v___x_2742_; lean_object* v___x_2744_; 
v___x_2742_ = lean_array_fset(v_xs_x27_2739_, v___x_2731_, v___y_2741_);
lean_dec(v___x_2731_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v___x_2742_);
v___x_2744_ = v___x_2735_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2742_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2750_, lean_object* v_x_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_){
_start:
{
size_t v_x_3936__boxed_2754_; size_t v_x_3937__boxed_2755_; lean_object* v_res_2756_; 
v_x_3936__boxed_2754_ = lean_unbox_usize(v_x_2752_);
lean_dec(v_x_2752_);
v_x_3937__boxed_2755_ = lean_unbox_usize(v_x_2753_);
lean_dec(v_x_2753_);
v_res_2756_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2750_, v_x_2751_, v_x_3936__boxed_2754_, v_x_3937__boxed_2755_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(lean_object* v_y_2757_, lean_object* v_t_2758_, lean_object* v_i_2759_){
_start:
{
lean_object* v_root_2760_; lean_object* v_tail_2761_; lean_object* v_size_2762_; size_t v_shift_2763_; lean_object* v_tailOff_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2791_; 
v_root_2760_ = lean_ctor_get(v_t_2758_, 0);
v_tail_2761_ = lean_ctor_get(v_t_2758_, 1);
v_size_2762_ = lean_ctor_get(v_t_2758_, 2);
v_shift_2763_ = lean_ctor_get_usize(v_t_2758_, 4);
v_tailOff_2764_ = lean_ctor_get(v_t_2758_, 3);
v_isSharedCheck_2791_ = !lean_is_exclusive(v_t_2758_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2766_ = v_t_2758_;
v_isShared_2767_ = v_isSharedCheck_2791_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_tailOff_2764_);
lean_inc(v_size_2762_);
lean_inc(v_tail_2761_);
lean_inc(v_root_2760_);
lean_dec(v_t_2758_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2791_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
uint8_t v___x_2768_; 
v___x_2768_ = lean_nat_dec_le(v_tailOff_2764_, v_i_2759_);
if (v___x_2768_ == 0)
{
size_t v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2769_ = lean_usize_of_nat(v_i_2759_);
v___x_2770_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2757_, v_root_2760_, v___x_2769_, v_shift_2763_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v___x_2770_);
v___x_2772_ = v___x_2766_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_tail_2761_);
lean_ctor_set(v_reuseFailAlloc_2773_, 2, v_size_2762_);
lean_ctor_set(v_reuseFailAlloc_2773_, 3, v_tailOff_2764_);
lean_ctor_set_usize(v_reuseFailAlloc_2773_, 4, v_shift_2763_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
else
{
lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; 
v___x_2774_ = lean_nat_sub(v_i_2759_, v_tailOff_2764_);
v___x_2775_ = lean_array_get_size(v_tail_2761_);
v___x_2776_ = lean_nat_dec_lt(v___x_2774_, v___x_2775_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2778_; 
lean_dec(v___x_2774_);
lean_dec(v_y_2757_);
if (v_isShared_2767_ == 0)
{
v___x_2778_ = v___x_2766_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_root_2760_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_tail_2761_);
lean_ctor_set(v_reuseFailAlloc_2779_, 2, v_size_2762_);
lean_ctor_set(v_reuseFailAlloc_2779_, 3, v_tailOff_2764_);
lean_ctor_set_usize(v_reuseFailAlloc_2779_, 4, v_shift_2763_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
else
{
lean_object* v_v_2780_; lean_object* v___x_2781_; lean_object* v_xs_x27_2782_; lean_object* v___y_2784_; uint8_t v___x_2789_; 
v_v_2780_ = lean_array_fget(v_tail_2761_, v___x_2774_);
v___x_2781_ = lean_box(0);
v_xs_x27_2782_ = lean_array_fset(v_tail_2761_, v___x_2774_, v___x_2781_);
v___x_2789_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2757_, v_v_2780_);
if (v___x_2789_ == 0)
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2757_, v___x_2781_, v_v_2780_);
v___y_2784_ = v___x_2790_;
goto v___jp_2783_;
}
else
{
lean_dec(v_y_2757_);
v___y_2784_ = v_v_2780_;
goto v___jp_2783_;
}
v___jp_2783_:
{
lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2785_ = lean_array_fset(v_xs_x27_2782_, v___x_2774_, v___y_2784_);
lean_dec(v___x_2774_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 1, v___x_2785_);
v___x_2787_ = v___x_2766_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_root_2760_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2788_, 2, v_size_2762_);
lean_ctor_set(v_reuseFailAlloc_2788_, 3, v_tailOff_2764_);
lean_ctor_set_usize(v_reuseFailAlloc_2788_, 4, v_shift_2763_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2___boxed(lean_object* v_y_2792_, lean_object* v_t_2793_, lean_object* v_i_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2792_, v_t_2793_, v_i_2794_);
lean_dec(v_i_2794_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(lean_object* v_y_2796_, lean_object* v_x_2797_, lean_object* v_s_2798_){
_start:
{
lean_object* v_vars_2799_; lean_object* v_varMap_2800_; lean_object* v_varsHistory_2801_; lean_object* v_natToIntMap_2802_; lean_object* v_natDef_2803_; lean_object* v_dvds_2804_; lean_object* v_lowers_2805_; lean_object* v_uppers_2806_; lean_object* v_diseqs_2807_; lean_object* v_elimEqs_2808_; lean_object* v_elimStack_2809_; lean_object* v_occurs_2810_; lean_object* v_assignment_2811_; lean_object* v_nextCnstrId_2812_; uint8_t v_caseSplits_2813_; lean_object* v_steps_2814_; lean_object* v_penalties_2815_; lean_object* v_numReorderRequests_2816_; lean_object* v_conflict_x3f_2817_; lean_object* v_diseqSplits_2818_; lean_object* v_divMod_2819_; uint8_t v_usedCommRing_2820_; lean_object* v_nonlinearOccs_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2829_; 
v_vars_2799_ = lean_ctor_get(v_s_2798_, 0);
v_varMap_2800_ = lean_ctor_get(v_s_2798_, 1);
v_varsHistory_2801_ = lean_ctor_get(v_s_2798_, 2);
v_natToIntMap_2802_ = lean_ctor_get(v_s_2798_, 3);
v_natDef_2803_ = lean_ctor_get(v_s_2798_, 4);
v_dvds_2804_ = lean_ctor_get(v_s_2798_, 5);
v_lowers_2805_ = lean_ctor_get(v_s_2798_, 6);
v_uppers_2806_ = lean_ctor_get(v_s_2798_, 7);
v_diseqs_2807_ = lean_ctor_get(v_s_2798_, 8);
v_elimEqs_2808_ = lean_ctor_get(v_s_2798_, 9);
v_elimStack_2809_ = lean_ctor_get(v_s_2798_, 10);
v_occurs_2810_ = lean_ctor_get(v_s_2798_, 11);
v_assignment_2811_ = lean_ctor_get(v_s_2798_, 12);
v_nextCnstrId_2812_ = lean_ctor_get(v_s_2798_, 13);
v_caseSplits_2813_ = lean_ctor_get_uint8(v_s_2798_, sizeof(void*)*21);
v_steps_2814_ = lean_ctor_get(v_s_2798_, 14);
v_penalties_2815_ = lean_ctor_get(v_s_2798_, 15);
v_numReorderRequests_2816_ = lean_ctor_get(v_s_2798_, 16);
v_conflict_x3f_2817_ = lean_ctor_get(v_s_2798_, 17);
v_diseqSplits_2818_ = lean_ctor_get(v_s_2798_, 18);
v_divMod_2819_ = lean_ctor_get(v_s_2798_, 19);
v_usedCommRing_2820_ = lean_ctor_get_uint8(v_s_2798_, sizeof(void*)*21 + 1);
v_nonlinearOccs_2821_ = lean_ctor_get(v_s_2798_, 20);
v_isSharedCheck_2829_ = !lean_is_exclusive(v_s_2798_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2823_ = v_s_2798_;
v_isShared_2824_ = v_isSharedCheck_2829_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_nonlinearOccs_2821_);
lean_inc(v_divMod_2819_);
lean_inc(v_diseqSplits_2818_);
lean_inc(v_conflict_x3f_2817_);
lean_inc(v_numReorderRequests_2816_);
lean_inc(v_penalties_2815_);
lean_inc(v_steps_2814_);
lean_inc(v_nextCnstrId_2812_);
lean_inc(v_assignment_2811_);
lean_inc(v_occurs_2810_);
lean_inc(v_elimStack_2809_);
lean_inc(v_elimEqs_2808_);
lean_inc(v_diseqs_2807_);
lean_inc(v_uppers_2806_);
lean_inc(v_lowers_2805_);
lean_inc(v_dvds_2804_);
lean_inc(v_natDef_2803_);
lean_inc(v_natToIntMap_2802_);
lean_inc(v_varsHistory_2801_);
lean_inc(v_varMap_2800_);
lean_inc(v_vars_2799_);
lean_dec(v_s_2798_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2829_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2825_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2796_, v_occurs_2810_, v_x_2797_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 11, v___x_2825_);
v___x_2827_ = v___x_2823_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_vars_2799_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_varMap_2800_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v_varsHistory_2801_);
lean_ctor_set(v_reuseFailAlloc_2828_, 3, v_natToIntMap_2802_);
lean_ctor_set(v_reuseFailAlloc_2828_, 4, v_natDef_2803_);
lean_ctor_set(v_reuseFailAlloc_2828_, 5, v_dvds_2804_);
lean_ctor_set(v_reuseFailAlloc_2828_, 6, v_lowers_2805_);
lean_ctor_set(v_reuseFailAlloc_2828_, 7, v_uppers_2806_);
lean_ctor_set(v_reuseFailAlloc_2828_, 8, v_diseqs_2807_);
lean_ctor_set(v_reuseFailAlloc_2828_, 9, v_elimEqs_2808_);
lean_ctor_set(v_reuseFailAlloc_2828_, 10, v_elimStack_2809_);
lean_ctor_set(v_reuseFailAlloc_2828_, 11, v___x_2825_);
lean_ctor_set(v_reuseFailAlloc_2828_, 12, v_assignment_2811_);
lean_ctor_set(v_reuseFailAlloc_2828_, 13, v_nextCnstrId_2812_);
lean_ctor_set(v_reuseFailAlloc_2828_, 14, v_steps_2814_);
lean_ctor_set(v_reuseFailAlloc_2828_, 15, v_penalties_2815_);
lean_ctor_set(v_reuseFailAlloc_2828_, 16, v_numReorderRequests_2816_);
lean_ctor_set(v_reuseFailAlloc_2828_, 17, v_conflict_x3f_2817_);
lean_ctor_set(v_reuseFailAlloc_2828_, 18, v_diseqSplits_2818_);
lean_ctor_set(v_reuseFailAlloc_2828_, 19, v_divMod_2819_);
lean_ctor_set(v_reuseFailAlloc_2828_, 20, v_nonlinearOccs_2821_);
lean_ctor_set_uint8(v_reuseFailAlloc_2828_, sizeof(void*)*21, v_caseSplits_2813_);
lean_ctor_set_uint8(v_reuseFailAlloc_2828_, sizeof(void*)*21 + 1, v_usedCommRing_2820_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed(lean_object* v_y_2830_, lean_object* v_x_2831_, lean_object* v_s_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(v_y_2830_, v_x_2831_, v_s_2832_);
lean_dec(v_x_2831_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(lean_object* v_x_2834_, lean_object* v_y_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_){
_start:
{
lean_object* v___f_2839_; lean_object* v___x_2840_; 
lean_inc(v_x_2834_);
lean_inc(v_y_2835_);
v___f_2839_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2839_, 0, v_y_2835_);
lean_closure_set(v___f_2839_, 1, v_x_2834_);
v___x_2840_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2834_, v_a_2836_, v_a_2837_);
lean_dec(v_x_2834_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2852_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_2852_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2852_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
uint8_t v___x_2845_; 
v___x_2845_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2835_, v_a_2841_);
lean_dec(v_a_2841_);
lean_dec(v_y_2835_);
if (v___x_2845_ == 0)
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
lean_del_object(v___x_2843_);
v___x_2846_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2847_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2846_, v___f_2839_, v_a_2836_);
return v___x_2847_;
}
else
{
lean_object* v___x_2848_; lean_object* v___x_2850_; 
lean_dec_ref(v___f_2839_);
v___x_2848_ = lean_box(0);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v___x_2848_);
v___x_2850_ = v___x_2843_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec_ref(v___f_2839_);
lean_dec(v_y_2835_);
v_a_2853_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2840_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2840_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___boxed(lean_object* v_x_2861_, lean_object* v_y_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2861_, v_y_2862_, v_a_2863_, v_a_2864_);
lean_dec_ref(v_a_2864_);
lean_dec(v_a_2863_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc(lean_object* v_x_2867_, lean_object* v_y_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2867_, v_y_2868_, v_a_2869_, v_a_2877_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___boxed(lean_object* v_x_2881_, lean_object* v_y_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc(v_x_2881_, v_y_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
lean_dec(v_a_2892_);
lean_dec_ref(v_a_2891_);
lean_dec(v_a_2890_);
lean_dec_ref(v_a_2889_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
lean_dec(v_a_2884_);
lean_dec(v_a_2883_);
return v_res_2894_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(lean_object* v_00_u03b2_2895_, lean_object* v_k_2896_, lean_object* v_t_2897_){
_start:
{
uint8_t v___x_2898_; 
v___x_2898_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2896_, v_t_2897_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2899_, lean_object* v_k_2900_, lean_object* v_t_2901_){
_start:
{
uint8_t v_res_2902_; lean_object* v_r_2903_; 
v_res_2902_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(v_00_u03b2_2899_, v_k_2900_, v_t_2901_);
lean_dec(v_t_2901_);
lean_dec(v_k_2900_);
v_r_2903_ = lean_box(v_res_2902_);
return v_r_2903_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1(lean_object* v_00_u03b2_2904_, lean_object* v_k_2905_, lean_object* v_v_2906_, lean_object* v_t_2907_, lean_object* v_hl_2908_){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2905_, v_v_2906_, v_t_2907_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(lean_object* v_y_2910_, lean_object* v_p_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
if (lean_obj_tag(v_p_2911_) == 1)
{
lean_object* v_v_2915_; lean_object* v_p_2916_; lean_object* v___x_2917_; 
v_v_2915_ = lean_ctor_get(v_p_2911_, 1);
lean_inc(v_v_2915_);
v_p_2916_ = lean_ctor_get(v_p_2911_, 2);
lean_inc_ref(v_p_2916_);
lean_dec_ref_known(v_p_2911_, 3);
lean_inc(v_y_2910_);
v___x_2917_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_v_2915_, v_y_2910_, v_a_2912_, v_a_2913_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_dec_ref_known(v___x_2917_, 1);
v_p_2911_ = v_p_2916_;
goto _start;
}
else
{
lean_dec_ref(v_p_2916_);
lean_dec(v_y_2910_);
return v___x_2917_;
}
}
else
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
lean_dec_ref(v_p_2911_);
lean_dec(v_y_2910_);
v___x_2919_ = lean_box(0);
v___x_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2919_);
return v___x_2920_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg___boxed(lean_object* v_y_2921_, lean_object* v_p_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2921_, v_p_2922_, v_a_2923_, v_a_2924_);
lean_dec_ref(v_a_2924_);
lean_dec(v_a_2923_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(lean_object* v_y_2927_, lean_object* v_p_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2927_, v_p_2928_, v_a_2929_, v_a_2937_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___boxed(lean_object* v_y_2941_, lean_object* v_p_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(v_y_2941_, v_p_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec(v_a_2943_);
return v_res_2954_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = ((lean_object*)(l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__0));
v___x_2957_ = l_Lean_stringToMessageData(v___x_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg(lean_object* v_p_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
if (lean_obj_tag(v_p_2958_) == 1)
{
lean_object* v_v_2965_; lean_object* v_p_2966_; lean_object* v___x_2967_; 
v_v_2965_ = lean_ctor_get(v_p_2958_, 1);
lean_inc(v_v_2965_);
v_p_2966_ = lean_ctor_get(v_p_2958_, 2);
lean_inc_ref(v_p_2966_);
lean_dec_ref_known(v_p_2958_, 3);
v___x_2967_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_v_2965_, v_p_2966_, v_a_2959_, v_a_2962_);
return v___x_2967_;
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
lean_dec_ref(v_p_2958_);
v___x_2968_ = lean_obj_once(&l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1, &l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1_once, _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1);
v___x_2969_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2968_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_);
return v___x_2969_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg___boxed(lean_object* v_p_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_);
lean_dec(v_a_2975_);
lean_dec_ref(v_a_2974_);
lean_dec(v_a_2973_);
lean_dec_ref(v_a_2972_);
lean_dec(v_a_2971_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs(lean_object* v_p_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2978_, v_a_2979_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___boxed(lean_object* v_p_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Int_Internal_Linear_Poly_updateOccs(v_p_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_, v_a_3001_);
lean_dec(v_a_3001_);
lean_dec_ref(v_a_3000_);
lean_dec(v_a_2999_);
lean_dec_ref(v_a_2998_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec(v_a_2992_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go_spec__0(lean_object* v_a_3004_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Rat_ofInt(v_a_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(lean_object* v_a_3006_, lean_object* v_v_3007_, lean_object* v_a_3008_){
_start:
{
if (lean_obj_tag(v_a_3008_) == 0)
{
lean_object* v_k_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3018_; 
v_k_3009_ = lean_ctor_get(v_a_3008_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_a_3008_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3011_ = v_a_3008_;
v_isShared_3012_ = v_isSharedCheck_3018_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_k_3009_);
lean_dec(v_a_3008_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3018_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3016_; 
v___x_3013_ = l_Rat_ofInt(v_k_3009_);
v___x_3014_ = l_Rat_add(v_v_3007_, v___x_3013_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set_tag(v___x_3011_, 1);
lean_ctor_set(v___x_3011_, 0, v___x_3014_);
v___x_3016_ = v___x_3011_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3014_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
else
{
lean_object* v_k_3019_; lean_object* v_v_3020_; lean_object* v_p_3021_; lean_object* v_size_3022_; uint8_t v___x_3023_; 
v_k_3019_ = lean_ctor_get(v_a_3008_, 0);
lean_inc(v_k_3019_);
v_v_3020_ = lean_ctor_get(v_a_3008_, 1);
lean_inc(v_v_3020_);
v_p_3021_ = lean_ctor_get(v_a_3008_, 2);
lean_inc_ref(v_p_3021_);
lean_dec_ref_known(v_a_3008_, 3);
v_size_3022_ = lean_ctor_get(v_a_3006_, 2);
v___x_3023_ = lean_nat_dec_lt(v_v_3020_, v_size_3022_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; 
lean_dec_ref(v_p_3021_);
lean_dec(v_v_3020_);
lean_dec(v_k_3019_);
lean_dec_ref(v_v_3007_);
v___x_3024_ = lean_box(0);
return v___x_3024_;
}
else
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3025_ = l_instInhabitedRat;
v___x_3026_ = l_Rat_ofInt(v_k_3019_);
v___x_3027_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3025_, v_a_3006_, v_v_3020_);
lean_dec(v_v_3020_);
v___x_3028_ = l_Rat_mul(v___x_3026_, v___x_3027_);
lean_dec_ref(v___x_3026_);
v___x_3029_ = l_Rat_add(v_v_3007_, v___x_3028_);
v_v_3007_ = v___x_3029_;
v_a_3008_ = v_p_3021_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go___boxed(lean_object* v_a_3031_, lean_object* v_v_3032_, lean_object* v_a_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_a_3031_, v_v_3032_, v_a_3033_);
lean_dec_ref(v_a_3031_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(lean_object* v_a_3035_){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3036_ = lean_nat_to_int(v_a_3035_);
v___x_3037_ = l_Rat_ofInt(v___x_3036_);
return v___x_3037_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3038_ = lean_unsigned_to_nat(0u);
v___x_3039_ = l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(v___x_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg(lean_object* v_p_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3041_, v_a_3042_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3055_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3047_ = v___x_3044_;
v_isShared_3048_ = v_isSharedCheck_3055_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3044_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3055_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v_assignment_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3053_; 
v_assignment_3049_ = lean_ctor_get(v_a_3045_, 12);
lean_inc_ref(v_assignment_3049_);
lean_dec(v_a_3045_);
v___x_3050_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_3051_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_assignment_3049_, v___x_3050_, v_p_3040_);
lean_dec_ref(v_assignment_3049_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___x_3051_);
v___x_3053_ = v___x_3047_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3051_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec_ref(v_p_3040_);
v_a_3056_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3044_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3044_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg___boxed(lean_object* v_p_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3064_, v_a_3065_, v_a_3066_);
lean_dec_ref(v_a_3066_);
lean_dec(v_a_3065_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f(lean_object* v_p_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_){
_start:
{
lean_object* v___x_3081_; 
v___x_3081_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3069_, v_a_3070_, v_a_3078_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___boxed(lean_object* v_p_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Int_Internal_Linear_Poly_eval_x3f(v_p_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
lean_dec(v_a_3092_);
lean_dec_ref(v_a_3091_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec(v_a_3083_);
return v_res_3094_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(lean_object* v_c_3095_){
_start:
{
lean_object* v_p_3096_; uint8_t v___x_3097_; 
v_p_3096_ = lean_ctor_get(v_c_3095_, 0);
v___x_3097_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_3096_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat___boxed(lean_object* v_c_3098_){
_start:
{
uint8_t v_res_3099_; lean_object* v_r_3100_; 
v_res_3099_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(v_c_3098_);
lean_dec_ref(v_c_3098_);
v_r_3100_ = lean_box(v_res_3099_);
return v_r_3100_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(lean_object* v_c_3101_){
_start:
{
lean_object* v_d_3102_; lean_object* v_p_3103_; uint8_t v___x_3104_; 
v_d_3102_ = lean_ctor_get(v_c_3101_, 0);
lean_inc(v_d_3102_);
v_p_3103_ = lean_ctor_get(v_c_3101_, 1);
lean_inc_ref(v_p_3103_);
lean_dec_ref(v_c_3101_);
v___x_3104_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_3102_, v_p_3103_);
lean_dec_ref(v_p_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat___boxed(lean_object* v_c_3105_){
_start:
{
uint8_t v_res_3106_; lean_object* v_r_3107_; 
v_res_3106_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(v_c_3105_);
v_r_3107_ = lean_box(v_res_3106_);
return v_r_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object* v_c_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_){
_start:
{
lean_object* v_d_3112_; lean_object* v_p_3113_; lean_object* v___x_3114_; 
v_d_3112_ = lean_ctor_get(v_c_3108_, 0);
lean_inc(v_d_3112_);
v_p_3113_ = lean_ctor_get(v_c_3108_, 1);
lean_inc_ref(v_p_3113_);
lean_dec_ref(v_c_3108_);
v___x_3114_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3113_, v_a_3109_, v_a_3110_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3142_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3117_ = v___x_3114_;
v_isShared_3118_ = v_isSharedCheck_3142_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3114_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3142_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
if (lean_obj_tag(v_a_3115_) == 1)
{
lean_object* v_val_3119_; lean_object* v_num_3120_; lean_object* v_den_3121_; lean_object* v___x_3122_; uint8_t v___x_3123_; 
v_val_3119_ = lean_ctor_get(v_a_3115_, 0);
lean_inc(v_val_3119_);
lean_dec_ref_known(v_a_3115_, 1);
v_num_3120_ = lean_ctor_get(v_val_3119_, 0);
lean_inc(v_num_3120_);
v_den_3121_ = lean_ctor_get(v_val_3119_, 1);
lean_inc(v_den_3121_);
lean_dec(v_val_3119_);
v___x_3122_ = lean_unsigned_to_nat(1u);
v___x_3123_ = lean_nat_dec_eq(v_den_3121_, v___x_3122_);
lean_dec(v_den_3121_);
if (v___x_3123_ == 0)
{
uint8_t v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3127_; 
lean_dec(v_num_3120_);
lean_dec(v_d_3112_);
v___x_3124_ = 0;
v___x_3125_ = lean_box(v___x_3124_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 0, v___x_3125_);
v___x_3127_ = v___x_3117_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3125_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
else
{
lean_object* v___x_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; uint8_t v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3135_; 
v___x_3129_ = lean_int_emod(v_num_3120_, v_d_3112_);
lean_dec(v_d_3112_);
lean_dec(v_num_3120_);
v___x_3130_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_3131_ = lean_int_dec_eq(v___x_3129_, v___x_3130_);
lean_dec(v___x_3129_);
v___x_3132_ = l_Lean_Bool_toLBool(v___x_3131_);
v___x_3133_ = lean_box(v___x_3132_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 0, v___x_3133_);
v___x_3135_ = v___x_3117_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3133_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
else
{
uint8_t v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3140_; 
lean_dec(v_a_3115_);
lean_dec(v_d_3112_);
v___x_3137_ = 2;
v___x_3138_ = lean_box(v___x_3137_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 0, v___x_3138_);
v___x_3140_ = v___x_3117_;
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
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_dec(v_d_3112_);
v_a_3143_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3114_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3114_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg___boxed(lean_object* v_c_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_3151_, v_a_3152_, v_a_3153_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(lean_object* v_c_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_3156_, v_a_3157_, v_a_3165_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___boxed(lean_object* v_c_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(v_c_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_);
lean_dec(v_a_3179_);
lean_dec_ref(v_a_3178_);
lean_dec(v_a_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_a_3175_);
lean_dec_ref(v_a_3174_);
lean_dec(v_a_3173_);
lean_dec_ref(v_a_3172_);
lean_dec(v_a_3171_);
lean_dec(v_a_3170_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg(lean_object* v_p_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3182_, v_a_3183_, v_a_3184_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3204_; 
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3189_ = v___x_3186_;
v_isShared_3190_ = v_isSharedCheck_3204_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3186_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3204_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
if (lean_obj_tag(v_a_3187_) == 1)
{
lean_object* v_val_3191_; lean_object* v___x_3192_; uint8_t v___x_3193_; uint8_t v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3197_; 
v_val_3191_ = lean_ctor_get(v_a_3187_, 0);
lean_inc(v_val_3191_);
lean_dec_ref_known(v_a_3187_, 1);
v___x_3192_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_3193_ = l_Rat_instDecidableLe(v_val_3191_, v___x_3192_);
v___x_3194_ = l_Lean_Bool_toLBool(v___x_3193_);
v___x_3195_ = lean_box(v___x_3194_);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 0, v___x_3195_);
v___x_3197_ = v___x_3189_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
else
{
uint8_t v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3202_; 
lean_dec(v_a_3187_);
v___x_3199_ = 2;
v___x_3200_ = lean_box(v___x_3199_);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 0, v___x_3200_);
v___x_3202_ = v___x_3189_;
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
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
v_a_3205_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3186_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3186_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg___boxed(lean_object* v_p_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_3213_, v_a_3214_, v_a_3215_);
lean_dec_ref(v_a_3215_);
lean_dec(v_a_3214_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe(lean_object* v_p_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_3218_, v_a_3219_, v_a_3227_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___boxed(lean_object* v_p_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Int_Internal_Linear_Poly_satisfiedLe(v_p_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
lean_dec(v_a_3241_);
lean_dec_ref(v_a_3240_);
lean_dec(v_a_3239_);
lean_dec_ref(v_a_3238_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
lean_dec(v_a_3232_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(lean_object* v_c_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_){
_start:
{
lean_object* v_p_3248_; lean_object* v___x_3249_; 
v_p_3248_ = lean_ctor_get(v_c_3244_, 0);
lean_inc_ref(v_p_3248_);
lean_dec_ref(v_c_3244_);
v___x_3249_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_3248_, v_a_3245_, v_a_3246_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg___boxed(lean_object* v_c_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_3250_, v_a_3251_, v_a_3252_);
lean_dec_ref(v_a_3252_);
lean_dec(v_a_3251_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(lean_object* v_c_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_3255_, v_a_3256_, v_a_3264_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___boxed(lean_object* v_c_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(v_c_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_);
lean_dec(v_a_3278_);
lean_dec_ref(v_a_3277_);
lean_dec(v_a_3276_);
lean_dec_ref(v_a_3275_);
lean_dec(v_a_3274_);
lean_dec_ref(v_a_3273_);
lean_dec(v_a_3272_);
lean_dec_ref(v_a_3271_);
lean_dec(v_a_3270_);
lean_dec(v_a_3269_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(lean_object* v_c_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_){
_start:
{
lean_object* v_p_3285_; lean_object* v___x_3286_; 
v_p_3285_ = lean_ctor_get(v_c_3281_, 0);
lean_inc_ref(v_p_3285_);
lean_dec_ref(v_c_3281_);
v___x_3286_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3285_, v_a_3282_, v_a_3283_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3306_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3289_ = v___x_3286_;
v_isShared_3290_ = v_isSharedCheck_3306_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3286_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3306_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
uint8_t v___y_3292_; 
if (lean_obj_tag(v_a_3287_) == 1)
{
lean_object* v_val_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; 
v_val_3298_ = lean_ctor_get(v_a_3287_, 0);
lean_inc(v_val_3298_);
lean_dec_ref_known(v_a_3287_, 1);
v___x_3299_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_3300_ = l_instDecidableEqRat_decEq(v_val_3298_, v___x_3299_);
lean_dec(v_val_3298_);
if (v___x_3300_ == 0)
{
uint8_t v___x_3301_; 
v___x_3301_ = 1;
v___y_3292_ = v___x_3301_;
goto v___jp_3291_;
}
else
{
uint8_t v___x_3302_; 
v___x_3302_ = 0;
v___y_3292_ = v___x_3302_;
goto v___jp_3291_;
}
}
else
{
uint8_t v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
lean_del_object(v___x_3289_);
lean_dec(v_a_3287_);
v___x_3303_ = 2;
v___x_3304_ = lean_box(v___x_3303_);
v___x_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
return v___x_3305_;
}
v___jp_3291_:
{
uint8_t v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3293_ = l_Lean_Bool_toLBool(v___y_3292_);
v___x_3294_ = lean_box(v___x_3293_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set(v___x_3289_, 0, v___x_3294_);
v___x_3296_ = v___x_3289_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3294_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
else
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
v_a_3307_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3286_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3286_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg___boxed(lean_object* v_c_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_3315_, v_a_3316_, v_a_3317_);
lean_dec_ref(v_a_3317_);
lean_dec(v_a_3316_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(lean_object* v_c_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_3320_, v_a_3321_, v_a_3329_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___boxed(lean_object* v_c_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(v_c_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_);
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
lean_dec(v_a_3341_);
lean_dec_ref(v_a_3340_);
lean_dec(v_a_3339_);
lean_dec_ref(v_a_3338_);
lean_dec(v_a_3337_);
lean_dec_ref(v_a_3336_);
lean_dec(v_a_3335_);
lean_dec(v_a_3334_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(lean_object* v_c_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_){
_start:
{
lean_object* v_p_3350_; lean_object* v___x_3351_; 
v_p_3350_ = lean_ctor_get(v_c_3346_, 0);
lean_inc_ref(v_p_3350_);
lean_dec_ref(v_c_3346_);
v___x_3351_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3350_, v_a_3347_, v_a_3348_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3369_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3354_ = v___x_3351_;
v_isShared_3355_ = v_isSharedCheck_3369_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3351_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3369_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
if (lean_obj_tag(v_a_3352_) == 1)
{
lean_object* v_val_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; uint8_t v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3362_; 
v_val_3356_ = lean_ctor_get(v_a_3352_, 0);
lean_inc(v_val_3356_);
lean_dec_ref_known(v_a_3352_, 1);
v___x_3357_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_3358_ = l_instDecidableEqRat_decEq(v_val_3356_, v___x_3357_);
lean_dec(v_val_3356_);
v___x_3359_ = l_Lean_Bool_toLBool(v___x_3358_);
v___x_3360_ = lean_box(v___x_3359_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v___x_3360_);
v___x_3362_ = v___x_3354_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
else
{
uint8_t v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3367_; 
lean_dec(v_a_3352_);
v___x_3364_ = 2;
v___x_3365_ = lean_box(v___x_3364_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v___x_3365_);
v___x_3367_ = v___x_3354_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3365_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
else
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
v_a_3370_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3351_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3351_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3373_ == 0)
{
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3370_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg___boxed(lean_object* v_c_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_3378_, v_a_3379_, v_a_3380_);
lean_dec_ref(v_a_3380_);
lean_dec(v_a_3379_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(lean_object* v_c_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_3383_, v_a_3384_, v_a_3392_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___boxed(lean_object* v_c_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(v_c_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_);
lean_dec(v_a_3406_);
lean_dec_ref(v_a_3405_);
lean_dec(v_a_3404_);
lean_dec_ref(v_a_3403_);
lean_dec(v_a_3402_);
lean_dec_ref(v_a_3401_);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3399_);
lean_dec(v_a_3398_);
lean_dec(v_a_3397_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg(lean_object* v_p_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_){
_start:
{
if (lean_obj_tag(v_p_3409_) == 0)
{
lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3420_; 
v_isSharedCheck_3420_ = !lean_is_exclusive(v_p_3409_);
if (v_isSharedCheck_3420_ == 0)
{
lean_object* v_unused_3421_; 
v_unused_3421_ = lean_ctor_get(v_p_3409_, 0);
lean_dec(v_unused_3421_);
v___x_3414_ = v_p_3409_;
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
else
{
lean_dec(v_p_3409_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3416_; lean_object* v___x_3418_; 
v___x_3416_ = lean_box(0);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 0, v___x_3416_);
v___x_3418_ = v___x_3414_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
else
{
lean_object* v_k_3422_; lean_object* v_v_3423_; lean_object* v_p_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v_k_3422_ = lean_ctor_get(v_p_3409_, 0);
lean_inc(v_k_3422_);
v_v_3423_ = lean_ctor_get(v_p_3409_, 1);
lean_inc(v_v_3423_);
v_p_3424_ = lean_ctor_get(v_p_3409_, 2);
lean_inc_ref(v_p_3424_);
lean_dec_ref_known(v_p_3409_, 3);
v___x_3425_ = lean_box(0);
v___x_3426_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3410_, v_a_3411_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3452_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3429_ = v___x_3426_;
v_isShared_3430_ = v_isSharedCheck_3452_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3426_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3452_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___y_3432_; lean_object* v_elimEqs_3447_; lean_object* v_size_3448_; uint8_t v___x_3449_; 
v_elimEqs_3447_ = lean_ctor_get(v_a_3427_, 9);
lean_inc_ref(v_elimEqs_3447_);
lean_dec(v_a_3427_);
v_size_3448_ = lean_ctor_get(v_elimEqs_3447_, 2);
v___x_3449_ = lean_nat_dec_lt(v_v_3423_, v_size_3448_);
if (v___x_3449_ == 0)
{
lean_object* v___x_3450_; 
lean_dec_ref(v_elimEqs_3447_);
v___x_3450_ = l_outOfBounds___redArg(v___x_3425_);
v___y_3432_ = v___x_3450_;
goto v___jp_3431_;
}
else
{
lean_object* v___x_3451_; 
v___x_3451_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3425_, v_elimEqs_3447_, v_v_3423_);
lean_dec_ref(v_elimEqs_3447_);
v___y_3432_ = v___x_3451_;
goto v___jp_3431_;
}
v___jp_3431_:
{
if (lean_obj_tag(v___y_3432_) == 1)
{
lean_object* v_val_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3445_; 
lean_dec_ref(v_p_3424_);
v_val_3433_ = lean_ctor_get(v___y_3432_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___y_3432_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3435_ = v___y_3432_;
v_isShared_3436_ = v_isSharedCheck_3445_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_val_3433_);
lean_dec(v___y_3432_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3445_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3440_; 
v___x_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3437_, 0, v_v_3423_);
lean_ctor_set(v___x_3437_, 1, v_val_3433_);
v___x_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3438_, 0, v_k_3422_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3438_);
v___x_3440_ = v___x_3435_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
lean_object* v___x_3442_; 
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3440_);
v___x_3442_ = v___x_3429_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
else
{
lean_dec(v___y_3432_);
lean_del_object(v___x_3429_);
lean_dec(v_v_3423_);
lean_dec(v_k_3422_);
v_p_3409_ = v_p_3424_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_dec_ref(v_p_3424_);
lean_dec(v_v_3423_);
lean_dec(v_k_3422_);
v_a_3453_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3426_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3426_);
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
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg___boxed(lean_object* v_p_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_3461_, v_a_3462_, v_a_3463_);
lean_dec_ref(v_a_3463_);
lean_dec(v_a_3462_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst(lean_object* v_p_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_3466_, v_a_3467_, v_a_3475_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___boxed(lean_object* v_p_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Int_Internal_Linear_Poly_findVarToSubst(v_p_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_);
lean_dec(v_a_3489_);
lean_dec_ref(v_a_3488_);
lean_dec(v_a_3487_);
lean_dec_ref(v_a_3486_);
lean_dec(v_a_3485_);
lean_dec_ref(v_a_3484_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec(v_a_3480_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(lean_object* v_pred_3492_){
_start:
{
lean_object* v_c_u2081_3493_; lean_object* v_c_u2082_3494_; uint8_t v_left_3495_; lean_object* v_c_u2083_x3f_3496_; lean_object* v_p_3497_; lean_object* v_p_3498_; lean_object* v_a_3499_; lean_object* v_b_3500_; 
v_c_u2081_3493_ = lean_ctor_get(v_pred_3492_, 0);
v_c_u2082_3494_ = lean_ctor_get(v_pred_3492_, 1);
v_left_3495_ = lean_ctor_get_uint8(v_pred_3492_, sizeof(void*)*3);
v_c_u2083_x3f_3496_ = lean_ctor_get(v_pred_3492_, 2);
v_p_3497_ = lean_ctor_get(v_c_u2081_3493_, 0);
v_p_3498_ = lean_ctor_get(v_c_u2082_3494_, 0);
v_a_3499_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3497_);
v_b_3500_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3498_);
if (lean_obj_tag(v_c_u2083_x3f_3496_) == 0)
{
if (v_left_3495_ == 0)
{
lean_object* v___x_3501_; 
lean_dec(v_a_3499_);
v___x_3501_ = lean_nat_abs(v_b_3500_);
lean_dec(v_b_3500_);
return v___x_3501_;
}
else
{
lean_object* v___x_3502_; 
lean_dec(v_b_3500_);
v___x_3502_ = lean_nat_abs(v_a_3499_);
lean_dec(v_a_3499_);
return v___x_3502_;
}
}
else
{
lean_object* v_val_3503_; lean_object* v_d_3504_; lean_object* v_p_3505_; lean_object* v_c_3506_; 
v_val_3503_ = lean_ctor_get(v_c_u2083_x3f_3496_, 0);
v_d_3504_ = lean_ctor_get(v_val_3503_, 0);
v_p_3505_ = lean_ctor_get(v_val_3503_, 1);
v_c_3506_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3505_);
if (v_left_3495_ == 0)
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
lean_dec(v_a_3499_);
v___x_3507_ = lean_int_mul(v_b_3500_, v_d_3504_);
v___x_3508_ = l_Int_gcd(v___x_3507_, v_c_3506_);
lean_dec(v_c_3506_);
v___x_3509_ = lean_nat_to_int(v___x_3508_);
v___x_3510_ = lean_int_ediv(v___x_3507_, v___x_3509_);
lean_dec(v___x_3509_);
lean_dec(v___x_3507_);
v___x_3511_ = l_Int_lcm(v_b_3500_, v___x_3510_);
lean_dec(v___x_3510_);
lean_dec(v_b_3500_);
return v___x_3511_;
}
else
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
lean_dec(v_b_3500_);
v___x_3512_ = lean_int_mul(v_a_3499_, v_d_3504_);
v___x_3513_ = l_Int_gcd(v___x_3512_, v_c_3506_);
lean_dec(v_c_3506_);
v___x_3514_ = lean_nat_to_int(v___x_3513_);
v___x_3515_ = lean_int_ediv(v___x_3512_, v___x_3514_);
lean_dec(v___x_3514_);
lean_dec(v___x_3512_);
v___x_3516_ = l_Int_lcm(v_a_3499_, v___x_3515_);
lean_dec(v___x_3515_);
lean_dec(v_a_3499_);
return v___x_3516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases___boxed(lean_object* v_pred_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(v_pred_3517_);
lean_dec_ref(v_pred_3517_);
return v_res_3518_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0));
v___x_3521_ = l_Lean_stringToMessageData(v___x_3520_);
return v___x_3521_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4(void){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3));
v___x_3526_ = l_Lean_MessageData_ofFormat(v___x_3525_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(lean_object* v_pred_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_){
_start:
{
lean_object* v_c_u2081_3531_; lean_object* v_c_u2082_3532_; lean_object* v_c_u2083_x3f_3533_; lean_object* v___x_3534_; 
v_c_u2081_3531_ = lean_ctor_get(v_pred_3527_, 0);
lean_inc_ref(v_c_u2081_3531_);
v_c_u2082_3532_ = lean_ctor_get(v_pred_3527_, 1);
lean_inc_ref(v_c_u2082_3532_);
v_c_u2083_x3f_3533_ = lean_ctor_get(v_pred_3527_, 2);
lean_inc(v_c_u2083_x3f_3533_);
lean_dec_ref(v_pred_3527_);
v___x_3534_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3531_, v_a_3528_, v_a_3529_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3536_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref_known(v___x_3534_, 1);
v___x_3536_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3532_, v_a_3528_, v_a_3529_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3555_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3539_ = v___x_3536_;
v_isShared_3540_ = v_isSharedCheck_3555_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3536_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3555_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v_____do__lift_3542_; 
if (lean_obj_tag(v_c_u2083_x3f_3533_) == 1)
{
lean_object* v_val_3551_; lean_object* v___x_3552_; 
v_val_3551_ = lean_ctor_get(v_c_u2083_x3f_3533_, 0);
lean_inc(v_val_3551_);
lean_dec_ref_known(v_c_u2083_x3f_3533_, 1);
v___x_3552_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_val_3551_, v_a_3528_, v_a_3529_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v___x_3552_, 1);
v_____do__lift_3542_ = v_a_3553_;
goto v___jp_3541_;
}
else
{
lean_del_object(v___x_3539_);
lean_dec(v_a_3537_);
lean_dec(v_a_3535_);
return v___x_3552_;
}
}
else
{
lean_object* v___x_3554_; 
lean_dec(v_c_u2083_x3f_3533_);
v___x_3554_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4);
v_____do__lift_3542_ = v___x_3554_;
goto v___jp_3541_;
}
v___jp_3541_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3549_; 
v___x_3543_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3544_, 0, v_a_3535_);
lean_ctor_set(v___x_3544_, 1, v___x_3543_);
v___x_3545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
lean_ctor_set(v___x_3545_, 1, v_a_3537_);
v___x_3546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
lean_ctor_set(v___x_3546_, 1, v___x_3543_);
v___x_3547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3546_);
lean_ctor_set(v___x_3547_, 1, v_____do__lift_3542_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v___x_3547_);
v___x_3549_ = v___x_3539_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3547_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
else
{
lean_dec(v_a_3535_);
lean_dec(v_c_u2083_x3f_3533_);
return v___x_3536_;
}
}
else
{
lean_dec(v_c_u2083_x3f_3533_);
lean_dec_ref(v_c_u2082_3532_);
return v___x_3534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___boxed(lean_object* v_pred_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_3556_, v_a_3557_, v_a_3558_);
lean_dec_ref(v_a_3558_);
lean_dec(v_a_3557_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(lean_object* v_pred_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_3561_, v_a_3562_, v_a_3570_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___boxed(lean_object* v_pred_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(v_pred_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec(v_a_3575_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(lean_object* v_h_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_){
_start:
{
switch(lean_obj_tag(v_h_3587_))
{
case 0:
{
lean_object* v_c_3591_; lean_object* v___x_3592_; 
v_c_3591_ = lean_ctor_get(v_h_3587_, 0);
lean_inc_ref(v_c_3591_);
lean_dec_ref_known(v_h_3587_, 1);
v___x_3592_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_3591_, v_a_3588_, v_a_3589_);
return v___x_3592_;
}
case 1:
{
lean_object* v_c_3593_; lean_object* v___x_3594_; 
v_c_3593_ = lean_ctor_get(v_h_3587_, 0);
lean_inc_ref(v_c_3593_);
lean_dec_ref_known(v_h_3587_, 1);
v___x_3594_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3593_, v_a_3588_, v_a_3589_);
return v___x_3594_;
}
case 2:
{
lean_object* v_c_3595_; lean_object* v___x_3596_; 
v_c_3595_ = lean_ctor_get(v_h_3587_, 0);
lean_inc_ref(v_c_3595_);
lean_dec_ref_known(v_h_3587_, 1);
v___x_3596_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_3595_, v_a_3588_, v_a_3589_);
return v___x_3596_;
}
case 3:
{
lean_object* v_c_3597_; lean_object* v___x_3598_; 
v_c_3597_ = lean_ctor_get(v_h_3587_, 0);
lean_inc_ref(v_c_3597_);
lean_dec_ref_known(v_h_3587_, 1);
v___x_3598_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_3597_, v_a_3588_, v_a_3589_);
return v___x_3598_;
}
default: 
{
lean_object* v_c_u2081_3599_; lean_object* v_c_u2082_3600_; lean_object* v_c_u2083_3601_; lean_object* v___x_3602_; 
v_c_u2081_3599_ = lean_ctor_get(v_h_3587_, 0);
lean_inc_ref(v_c_u2081_3599_);
v_c_u2082_3600_ = lean_ctor_get(v_h_3587_, 1);
lean_inc_ref(v_c_u2082_3600_);
v_c_u2083_3601_ = lean_ctor_get(v_h_3587_, 2);
lean_inc_ref(v_c_u2083_3601_);
lean_dec_ref_known(v_h_3587_, 3);
v___x_3602_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3599_, v_a_3588_, v_a_3589_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; lean_object* v___x_3604_; 
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_a_3603_);
lean_dec_ref_known(v___x_3602_, 1);
v___x_3604_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3600_, v_a_3588_, v_a_3589_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; lean_object* v___x_3606_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_a_3605_);
lean_dec_ref_known(v___x_3604_, 1);
v___x_3606_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2083_3601_, v_a_3588_, v_a_3589_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3619_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3609_ = v___x_3606_;
v_isShared_3610_ = v_isSharedCheck_3619_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3606_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3619_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3617_; 
v___x_3611_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3612_, 0, v_a_3603_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
v___x_3613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3612_);
lean_ctor_set(v___x_3613_, 1, v_a_3605_);
v___x_3614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3613_);
lean_ctor_set(v___x_3614_, 1, v___x_3611_);
v___x_3615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3614_);
lean_ctor_set(v___x_3615_, 1, v_a_3607_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v___x_3615_);
v___x_3617_ = v___x_3609_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3615_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
else
{
lean_dec(v_a_3605_);
lean_dec(v_a_3603_);
return v___x_3606_;
}
}
else
{
lean_dec(v_a_3603_);
lean_dec_ref(v_c_u2083_3601_);
return v___x_3604_;
}
}
else
{
lean_dec_ref(v_c_u2083_3601_);
lean_dec_ref(v_c_u2082_3600_);
return v___x_3602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg___boxed(lean_object* v_h_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3620_, v_a_3621_, v_a_3622_);
lean_dec_ref(v_a_3622_);
lean_dec(v_a_3621_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(lean_object* v_h_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_){
_start:
{
lean_object* v___x_3637_; 
v___x_3637_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3625_, v_a_3626_, v_a_3634_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___boxed(lean_object* v_h_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(v_h_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
lean_dec(v_a_3648_);
lean_dec_ref(v_a_3647_);
lean_dec(v_a_3646_);
lean_dec_ref(v_a_3645_);
lean_dec(v_a_3644_);
lean_dec_ref(v_a_3643_);
lean_dec(v_a_3642_);
lean_dec_ref(v_a_3641_);
lean_dec(v_a_3640_);
lean_dec(v_a_3639_);
return v_res_3650_;
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
