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
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isNatType(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isIntType(lean_object*);
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
uint8_t l_Int_Internal_Linear_Poly_isZero(lean_object* v_x_3_){
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
LEAN_EXPORT void l_Int_Internal_Linear_Poly_isZero_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3_ = stack[0].m_obj;
uint8_t v_res_8_;
v_res_8_ = l_Int_Internal_Linear_Poly_isZero(v_x_3_);
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isZero___boxed(lean_object* v_x_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Int_Internal_Linear_Poly_isZero(v_x_9_);
lean_dec_ref(v_x_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_isSorted_go(lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
if (lean_obj_tag(v_a_13_) == 0)
{
uint8_t v___x_14_; 
lean_dec(v_a_12_);
v___x_14_ = 1;
return v___x_14_;
}
else
{
if (lean_obj_tag(v_a_12_) == 0)
{
lean_object* v_v_15_; lean_object* v_p_16_; lean_object* v___x_17_; 
v_v_15_ = lean_ctor_get(v_a_13_, 1);
v_p_16_ = lean_ctor_get(v_a_13_, 2);
lean_inc(v_v_15_);
v___x_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_17_, 0, v_v_15_);
v_a_12_ = v___x_17_;
v_a_13_ = v_p_16_;
goto _start;
}
else
{
lean_object* v_v_19_; lean_object* v_p_20_; lean_object* v_val_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_30_; 
v_v_19_ = lean_ctor_get(v_a_13_, 1);
v_p_20_ = lean_ctor_get(v_a_13_, 2);
v_val_21_ = lean_ctor_get(v_a_12_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v_a_12_);
if (v_isSharedCheck_30_ == 0)
{
v___x_23_ = v_a_12_;
v_isShared_24_ = v_isSharedCheck_30_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_val_21_);
lean_dec(v_a_12_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_30_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
uint8_t v___x_25_; 
v___x_25_ = lean_nat_dec_lt(v_v_19_, v_val_21_);
lean_dec(v_val_21_);
if (v___x_25_ == 0)
{
lean_del_object(v___x_23_);
return v___x_25_;
}
else
{
lean_object* v___x_27_; 
lean_inc(v_v_19_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 0, v_v_19_);
v___x_27_ = v___x_23_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_v_19_);
v___x_27_ = v_reuseFailAlloc_29_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
v_a_12_ = v___x_27_;
v_a_13_ = v_p_20_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_isSorted_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_12_ = stack[0].m_obj;
lean_object* v_a_13_ = stack[1].m_obj;
uint8_t v_res_31_;
v_res_31_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_isSorted_go(v_a_12_, v_a_13_);
stack->m_num = v_res_31_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_isSorted_go___boxed(lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_isSorted_go(v_a_32_, v_a_33_);
lean_dec_ref(v_a_33_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
uint8_t l_Int_Internal_Linear_Poly_isSorted(lean_object* v_p_36_){
_start:
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = lean_box(0);
v___x_38_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_isSorted_go(v___x_37_, v_p_36_);
return v___x_38_;
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_isSorted_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_36_ = stack[0].m_obj;
uint8_t v_res_39_;
v_res_39_ = l_Int_Internal_Linear_Poly_isSorted(v_p_36_);
stack->m_num = v_res_39_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isSorted___boxed(lean_object* v_p_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Int_Internal_Linear_Poly_isSorted(v_p_40_);
lean_dec_ref(v_p_40_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_47_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_46_, v_a_43_, v_a_44_);
return v___x_47_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_43_ = stack[0].m_obj;
lean_object* v_a_44_ = stack[1].m_obj;
lean_object* v_res_48_;
v_res_48_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_43_, v_a_44_);
stack->m_obj
 = v_res_48_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg___boxed(lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_49_, v_a_50_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
return v_res_52_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27(lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_53_, v_a_61_);
return v___x_64_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_get_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_53_ = stack[0].m_obj;
lean_object* v_a_54_ = stack[1].m_obj;
lean_object* v_a_55_ = stack[2].m_obj;
lean_object* v_a_56_ = stack[3].m_obj;
lean_object* v_a_57_ = stack[4].m_obj;
lean_object* v_a_58_ = stack[5].m_obj;
lean_object* v_a_59_ = stack[6].m_obj;
lean_object* v_a_60_ = stack[7].m_obj;
lean_object* v_a_61_ = stack[8].m_obj;
lean_object* v_a_62_ = stack[9].m_obj;
lean_object* v_res_65_;
v_res_65_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___boxed(lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
lean_dec(v_a_67_);
lean_dec(v_a_66_);
return v_res_77_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___redArg(lean_object* v_f_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_82_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_81_, v_f_78_, v_a_79_);
return v___x_82_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_78_ = stack[0].m_obj;
lean_object* v_a_79_ = stack[1].m_obj;
lean_object* v_res_83_;
v_res_83_ = l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___redArg(v_f_78_, v_a_79_);
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___redArg___boxed(lean_object* v_f_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___redArg(v_f_84_, v_a_85_);
lean_dec(v_a_85_);
return v_res_87_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modify_x27(lean_object* v_f_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_101_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_100_, v_f_88_, v_a_89_);
return v___x_101_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_modify_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_88_ = stack[0].m_obj;
lean_object* v_a_89_ = stack[1].m_obj;
lean_object* v_a_90_ = stack[2].m_obj;
lean_object* v_a_91_ = stack[3].m_obj;
lean_object* v_a_92_ = stack[4].m_obj;
lean_object* v_a_93_ = stack[5].m_obj;
lean_object* v_a_94_ = stack[6].m_obj;
lean_object* v_a_95_ = stack[7].m_obj;
lean_object* v_a_96_ = stack[8].m_obj;
lean_object* v_a_97_ = stack[9].m_obj;
lean_object* v_a_98_ = stack[10].m_obj;
lean_object* v_res_102_;
v_res_102_ = l_Lean_Meta_Grind_Arith_Cutsat_modify_x27(v_f_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
stack->m_obj
 = v_res_102_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___boxed(lean_object* v_f_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Meta_Grind_Arith_Cutsat_modify_x27(v_f_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec(v_a_104_);
return v_res_115_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg(lean_object* v_type_152_, lean_object* v_a_153_){
_start:
{
uint8_t v___y_156_; uint8_t v___x_257_; 
v___x_257_ = l_Lean_Meta_Grind_Arith_isNatType(v_type_152_);
if (v___x_257_ == 0)
{
uint8_t v___x_258_; 
v___x_258_ = l_Lean_Meta_Grind_Arith_isIntType(v_type_152_);
v___y_156_ = v___x_258_;
goto v___jp_155_;
}
else
{
v___y_156_ = v___x_257_;
goto v___jp_155_;
}
v___jp_155_:
{
uint8_t v___x_157_; 
v___x_157_ = 1;
if (v___y_156_ == 0)
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_type_152_, v_a_153_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_246_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_246_ == 0)
{
v___x_161_ = v___x_158_;
v_isShared_162_ = v_isSharedCheck_246_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_246_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_163_ = l_Lean_Expr_cleanupAnnotations(v_a_159_);
v___x_164_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__1));
v___x_165_ = l_Lean_Expr_isConstOf(v___x_163_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__3));
v___x_167_ = l_Lean_Expr_isConstOf(v___x_163_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__5));
v___x_169_ = l_Lean_Expr_isConstOf(v___x_163_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__7));
v___x_171_ = l_Lean_Expr_isConstOf(v___x_163_, v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__9));
v___x_173_ = l_Lean_Expr_isConstOf(v___x_163_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__11));
v___x_175_ = l_Lean_Expr_isConstOf(v___x_163_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__13));
v___x_177_ = l_Lean_Expr_isConstOf(v___x_163_, v___x_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__15));
v___x_179_ = l_Lean_Expr_isConstOf(v___x_163_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__17));
v___x_181_ = l_Lean_Expr_isConstOf(v___x_163_, v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__19));
v___x_183_ = l_Lean_Expr_isConstOf(v___x_163_, v___x_182_);
if (v___x_183_ == 0)
{
uint8_t v___x_184_; 
v___x_184_ = l_Lean_Expr_isApp(v___x_163_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_187_; 
lean_dec_ref(v___x_163_);
v___x_185_ = lean_box(v___y_156_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_185_);
v___x_187_ = v___x_161_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_189_ = l_Lean_Expr_appFnCleanup___redArg(v___x_163_);
v___x_190_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__21));
v___x_191_ = l_Lean_Expr_isConstOf(v___x_189_, v___x_190_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__23));
v___x_193_ = l_Lean_Expr_isConstOf(v___x_189_, v___x_192_);
lean_dec_ref(v___x_189_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_box(v___y_156_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_194_);
v___x_196_ = v___x_161_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
else
{
lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_198_ = lean_box(v___x_157_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_198_);
v___x_200_ = v___x_161_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
else
{
lean_object* v___x_202_; lean_object* v___x_204_; 
lean_dec_ref(v___x_189_);
v___x_202_ = lean_box(v___x_157_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_202_);
v___x_204_ = v___x_161_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_object* v___x_206_; lean_object* v___x_208_; 
lean_dec_ref(v___x_163_);
v___x_206_ = lean_box(v___x_157_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_206_);
v___x_208_ = v___x_161_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
else
{
lean_object* v___x_210_; lean_object* v___x_212_; 
lean_dec_ref(v___x_163_);
v___x_210_ = lean_box(v___x_157_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_210_);
v___x_212_ = v___x_161_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
else
{
lean_object* v___x_214_; lean_object* v___x_216_; 
lean_dec_ref(v___x_163_);
v___x_214_ = lean_box(v___x_157_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_214_);
v___x_216_ = v___x_161_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
else
{
lean_object* v___x_218_; lean_object* v___x_220_; 
lean_dec_ref(v___x_163_);
v___x_218_ = lean_box(v___x_157_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_218_);
v___x_220_ = v___x_161_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
else
{
lean_object* v___x_222_; lean_object* v___x_224_; 
lean_dec_ref(v___x_163_);
v___x_222_ = lean_box(v___x_157_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_222_);
v___x_224_ = v___x_161_;
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
else
{
lean_object* v___x_226_; lean_object* v___x_228_; 
lean_dec_ref(v___x_163_);
v___x_226_ = lean_box(v___x_157_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_226_);
v___x_228_ = v___x_161_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
else
{
lean_object* v___x_230_; lean_object* v___x_232_; 
lean_dec_ref(v___x_163_);
v___x_230_ = lean_box(v___x_157_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_230_);
v___x_232_ = v___x_161_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
else
{
lean_object* v___x_234_; lean_object* v___x_236_; 
lean_dec_ref(v___x_163_);
v___x_234_ = lean_box(v___x_157_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_234_);
v___x_236_ = v___x_161_;
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
lean_object* v___x_238_; lean_object* v___x_240_; 
lean_dec_ref(v___x_163_);
v___x_238_ = lean_box(v___x_157_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_238_);
v___x_240_ = v___x_161_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
else
{
lean_object* v___x_242_; lean_object* v___x_244_; 
lean_dec_ref(v___x_163_);
v___x_242_ = lean_box(v___x_157_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_242_);
v___x_244_ = v___x_161_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
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
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
v_a_247_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_158_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_158_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec_ref(v_type_152_);
v___x_255_ = lean_box(v___x_157_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_152_ = stack[0].m_obj;
lean_object* v_a_153_ = stack[1].m_obj;
lean_object* v_res_259_;
v_res_259_ = l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg(v_type_152_, v_a_153_);
stack->m_obj
 = v_res_259_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___boxed(lean_object* v_type_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg(v_type_260_, v_a_261_);
lean_dec(v_a_261_);
return v_res_263_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType(lean_object* v_type_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg(v_type_264_, v_a_272_);
return v___x_276_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_264_ = stack[0].m_obj;
lean_object* v_a_265_ = stack[1].m_obj;
lean_object* v_a_266_ = stack[2].m_obj;
lean_object* v_a_267_ = stack[3].m_obj;
lean_object* v_a_268_ = stack[4].m_obj;
lean_object* v_a_269_ = stack[5].m_obj;
lean_object* v_a_270_ = stack[6].m_obj;
lean_object* v_a_271_ = stack[7].m_obj;
lean_object* v_a_272_ = stack[8].m_obj;
lean_object* v_a_273_ = stack[9].m_obj;
lean_object* v_a_274_ = stack[10].m_obj;
lean_object* v_res_277_;
v_res_277_ = l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType(v_type_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
stack->m_obj
 = v_res_277_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___boxed(lean_object* v_type_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType(v_type_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec(v_a_279_);
return v_res_290_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg(lean_object* v_00_u03b1_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_301_ = l_Lean_Expr_cleanupAnnotations(v_00_u03b1_291_);
v___x_302_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__3));
v___x_303_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__5));
v___x_305_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__7));
v___x_307_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__9));
v___x_309_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__13));
v___x_311_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__15));
v___x_313_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__17));
v___x_315_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__19));
v___x_317_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_316_);
if (v___x_317_ == 0)
{
uint8_t v___x_318_; 
v___x_318_ = l_Lean_Expr_isApp(v___x_301_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref(v___x_301_);
v___x_319_ = lean_box(v___x_317_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
else
{
lean_object* v_arg_321_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v_arg_321_ = lean_ctor_get(v___x_301_, 1);
lean_inc_ref(v_arg_321_);
v___x_349_ = l_Lean_Expr_appFnCleanup___redArg(v___x_301_);
v___x_350_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__21));
v___x_351_ = l_Lean_Expr_isConstOf(v___x_349_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__23));
v___x_353_ = l_Lean_Expr_isConstOf(v___x_349_, v___x_352_);
lean_dec_ref(v___x_349_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec_ref(v_arg_321_);
v___x_354_ = lean_box(v___x_317_);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
else
{
v___y_323_ = v_a_292_;
v___y_324_ = v_a_293_;
v___y_325_ = v_a_294_;
v___y_326_ = v_a_295_;
goto v___jp_322_;
}
}
else
{
lean_dec_ref(v___x_349_);
v___y_323_ = v_a_292_;
v___y_324_ = v_a_293_;
v___y_325_ = v_a_294_;
v___y_326_ = v_a_295_;
goto v___jp_322_;
}
v___jp_322_:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Meta_getNatValue_x3f(v_arg_321_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
lean_dec_ref(v_arg_321_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_340_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_340_ == 0)
{
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_340_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_340_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
if (lean_obj_tag(v_a_328_) == 0)
{
lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_332_ = lean_box(v___x_317_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_332_);
v___x_334_ = v___x_330_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_338_; 
lean_dec_ref_known(v_a_328_, 1);
v___x_336_ = lean_box(v___x_318_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_336_);
v___x_338_ = v___x_330_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
v_a_341_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_327_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_327_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
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
}
else
{
lean_dec_ref(v___x_301_);
goto v___jp_297_;
}
}
else
{
lean_dec_ref(v___x_301_);
goto v___jp_297_;
}
}
else
{
lean_dec_ref(v___x_301_);
goto v___jp_297_;
}
}
else
{
lean_dec_ref(v___x_301_);
goto v___jp_297_;
}
}
else
{
lean_dec_ref(v___x_301_);
goto v___jp_297_;
}
}
else
{
lean_dec_ref(v___x_301_);
goto v___jp_297_;
}
}
else
{
lean_dec_ref(v___x_301_);
goto v___jp_297_;
}
}
else
{
lean_dec_ref(v___x_301_);
goto v___jp_297_;
}
v___jp_297_:
{
uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = 1;
v___x_299_ = lean_box(v___x_298_);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03b1_291_ = stack[0].m_obj;
lean_object* v_a_292_ = stack[1].m_obj;
lean_object* v_a_293_ = stack[2].m_obj;
lean_object* v_a_294_ = stack[3].m_obj;
lean_object* v_a_295_ = stack[4].m_obj;
lean_object* v_res_356_;
v_res_356_ = l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg(v_00_u03b1_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
stack->m_obj
 = v_res_356_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg___boxed(lean_object* v_00_u03b1_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg(v_00_u03b1_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
return v_res_363_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated(lean_object* v_00_u03b1_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg(v_00_u03b1_364_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
return v___x_376_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03b1_364_ = stack[0].m_obj;
lean_object* v_a_365_ = stack[1].m_obj;
lean_object* v_a_366_ = stack[2].m_obj;
lean_object* v_a_367_ = stack[3].m_obj;
lean_object* v_a_368_ = stack[4].m_obj;
lean_object* v_a_369_ = stack[5].m_obj;
lean_object* v_a_370_ = stack[6].m_obj;
lean_object* v_a_371_ = stack[7].m_obj;
lean_object* v_a_372_ = stack[8].m_obj;
lean_object* v_a_373_ = stack[9].m_obj;
lean_object* v_a_374_ = stack[10].m_obj;
lean_object* v_res_377_;
v_res_377_ = l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated(v_00_u03b1_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
stack->m_obj
 = v_res_377_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___boxed(lean_object* v_00_u03b1_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated(v_00_u03b1_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec(v_a_379_);
return v_res_390_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_391_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; uint8_t v___x_396_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v___x_396_ = lean_unbox(v_a_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; 
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 1);
v___x_397_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_391_, v_a_392_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_411_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_411_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_411_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_411_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v_conflict_x3f_402_; 
v_conflict_x3f_402_ = lean_ctor_get(v_a_398_, 15);
lean_inc(v_conflict_x3f_402_);
lean_dec(v_a_398_);
if (lean_obj_tag(v_conflict_x3f_402_) == 0)
{
lean_object* v___x_404_; 
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v_a_395_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_395_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
else
{
uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
lean_dec_ref_known(v_conflict_x3f_402_, 1);
lean_dec(v_a_395_);
v___x_406_ = 1;
v___x_407_ = lean_box(v___x_406_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_407_);
v___x_409_ = v___x_400_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec(v_a_395_);
v_a_412_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_397_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_397_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
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
else
{
return v___x_394_;
}
}
else
{
return v___x_394_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_391_ = stack[0].m_obj;
lean_object* v_a_392_ = stack[1].m_obj;
lean_object* v_res_420_;
v_res_420_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_391_, v_a_392_);
stack->m_obj
 = v_res_420_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg___boxed(lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_421_, v_a_422_);
lean_dec_ref(v_a_422_);
lean_dec(v_a_421_);
return v_res_424_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_425_, v_a_433_);
return v___x_436_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_inconsistent_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_425_ = stack[0].m_obj;
lean_object* v_a_426_ = stack[1].m_obj;
lean_object* v_a_427_ = stack[2].m_obj;
lean_object* v_a_428_ = stack[3].m_obj;
lean_object* v_a_429_ = stack[4].m_obj;
lean_object* v_a_430_ = stack[5].m_obj;
lean_object* v_a_431_ = stack[6].m_obj;
lean_object* v_a_432_ = stack[7].m_obj;
lean_object* v_a_433_ = stack[8].m_obj;
lean_object* v_a_434_ = stack[9].m_obj;
lean_object* v_res_437_;
v_res_437_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
stack->m_obj
 = v_res_437_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___boxed(lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec(v_a_438_);
return v_res_449_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_mkVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_450_ = stack[0].m_obj;
lean_object* v_a_451_ = stack[1].m_obj;
lean_object* v_a_452_ = stack[2].m_obj;
lean_object* v_a_453_ = stack[3].m_obj;
lean_object* v_a_454_ = stack[4].m_obj;
lean_object* v_a_455_ = stack[5].m_obj;
lean_object* v_a_456_ = stack[6].m_obj;
lean_object* v_a_457_ = stack[7].m_obj;
lean_object* v_a_458_ = stack[8].m_obj;
lean_object* v_a_459_ = stack[9].m_obj;
lean_object* v_a_460_ = stack[10].m_obj;
lean_object* v_res_462_;
v_res_462_ = lean_grind_cutsat_mk_var(v_e_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
stack->m_obj
 = v_res_462_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVar___boxed(lean_object* v_e_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_00___x40___internal___hyg_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = lean_grind_cutsat_mk_var(v_e_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
return v_res_475_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_476_, v_a_477_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_488_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_488_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_488_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_488_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v_vars_484_; lean_object* v___x_486_; 
v_vars_484_ = lean_ctor_get(v_a_480_, 0);
lean_inc_ref(v_vars_484_);
lean_dec(v_a_480_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v_vars_484_);
v___x_486_ = v___x_482_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_vars_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
v_a_489_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_479_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_479_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_476_ = stack[0].m_obj;
lean_object* v_a_477_ = stack[1].m_obj;
lean_object* v_res_497_;
v_res_497_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_476_, v_a_477_);
stack->m_obj
 = v_res_497_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg___boxed(lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_498_, v_a_499_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
return v_res_501_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars(lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_502_, v_a_510_);
return v___x_513_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_getVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_502_ = stack[0].m_obj;
lean_object* v_a_503_ = stack[1].m_obj;
lean_object* v_a_504_ = stack[2].m_obj;
lean_object* v_a_505_ = stack[3].m_obj;
lean_object* v_a_506_ = stack[4].m_obj;
lean_object* v_a_507_ = stack[5].m_obj;
lean_object* v_a_508_ = stack[6].m_obj;
lean_object* v_a_509_ = stack[7].m_obj;
lean_object* v_a_510_ = stack[8].m_obj;
lean_object* v_a_511_ = stack[9].m_obj;
lean_object* v_res_514_;
v_res_514_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars(v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
stack->m_obj
 = v_res_514_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___boxed(lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars(v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec(v_a_515_);
return v_res_526_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object* v_x_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = l_Lean_instInhabitedExpr;
v___x_532_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_528_, v_a_529_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_548_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_548_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_548_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_548_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v_vars_537_; lean_object* v_size_538_; uint8_t v___x_539_; 
v_vars_537_ = lean_ctor_get(v_a_533_, 0);
lean_inc_ref(v_vars_537_);
lean_dec(v_a_533_);
v_size_538_ = lean_ctor_get(v_vars_537_, 2);
v___x_539_ = lean_nat_dec_lt(v_x_527_, v_size_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_542_; 
lean_dec_ref(v_vars_537_);
v___x_540_ = l_outOfBounds___redArg(v___x_531_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_540_);
v___x_542_ = v___x_535_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = l_Lean_PersistentArray_get_x21___redArg(v___x_531_, v_vars_537_, v_x_527_);
lean_dec_ref(v_vars_537_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_544_);
v___x_546_ = v___x_535_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
v_a_549_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_532_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_532_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_527_ = stack[0].m_obj;
lean_object* v_a_528_ = stack[1].m_obj;
lean_object* v_a_529_ = stack[2].m_obj;
lean_object* v_res_557_;
v_res_557_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_527_, v_a_528_, v_a_529_);
stack->m_obj
 = v_res_557_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg___boxed(lean_object* v_x_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_558_, v_a_559_, v_a_560_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec(v_x_558_);
return v_res_562_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar(lean_object* v_x_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_563_, v_a_564_, v_a_572_);
return v___x_575_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_getVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_563_ = stack[0].m_obj;
lean_object* v_a_564_ = stack[1].m_obj;
lean_object* v_a_565_ = stack[2].m_obj;
lean_object* v_a_566_ = stack[3].m_obj;
lean_object* v_a_567_ = stack[4].m_obj;
lean_object* v_a_568_ = stack[5].m_obj;
lean_object* v_a_569_ = stack[6].m_obj;
lean_object* v_a_570_ = stack[7].m_obj;
lean_object* v_a_571_ = stack[8].m_obj;
lean_object* v_a_572_ = stack[9].m_obj;
lean_object* v_a_573_ = stack[10].m_obj;
lean_object* v_res_576_;
v_res_576_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar(v_x_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
stack->m_obj
 = v_res_576_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___boxed(lean_object* v_x_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar(v_x_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec(v_a_578_);
lean_dec(v_x_577_);
return v_res_589_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_590_, lean_object* v_i_591_, lean_object* v_k_592_){
_start:
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = lean_array_get_size(v_keys_590_);
v___x_594_ = lean_nat_dec_lt(v_i_591_, v___x_593_);
if (v___x_594_ == 0)
{
lean_dec(v_i_591_);
return v___x_594_;
}
else
{
lean_object* v_k_x27_595_; size_t v___x_596_; size_t v___x_597_; uint8_t v___x_598_; 
v_k_x27_595_ = lean_array_fget_borrowed(v_keys_590_, v_i_591_);
v___x_596_ = lean_ptr_addr(v_k_592_);
v___x_597_ = lean_ptr_addr(v_k_x27_595_);
v___x_598_ = lean_usize_dec_eq(v___x_596_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = lean_nat_add(v_i_591_, v___x_599_);
lean_dec(v_i_591_);
v_i_591_ = v___x_600_;
goto _start;
}
else
{
lean_dec(v_i_591_);
return v___x_594_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_590_ = stack[0].m_obj;
lean_object* v_i_591_ = stack[1].m_obj;
lean_object* v_k_592_ = stack[2].m_obj;
uint8_t v_res_602_;
v_res_602_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_590_, v_i_591_, v_k_592_);
stack->m_num = v_res_602_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_603_, lean_object* v_i_604_, lean_object* v_k_605_){
_start:
{
uint8_t v_res_606_; lean_object* v_r_607_; 
v_res_606_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_603_, v_i_604_, v_k_605_);
lean_dec_ref(v_k_605_);
lean_dec_ref(v_keys_603_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(lean_object* v_x_608_, size_t v_x_609_, lean_object* v_x_610_){
_start:
{
if (lean_obj_tag(v_x_608_) == 0)
{
lean_object* v_es_611_; lean_object* v___x_612_; size_t v___x_613_; size_t v___x_614_; lean_object* v_j_615_; lean_object* v___x_616_; 
v_es_611_ = lean_ctor_get(v_x_608_, 0);
v___x_612_ = lean_box(2);
v___x_613_ = ((size_t)31ULL);
v___x_614_ = lean_usize_land(v_x_609_, v___x_613_);
v_j_615_ = lean_usize_to_nat(v___x_614_);
v___x_616_ = lean_array_get_borrowed(v___x_612_, v_es_611_, v_j_615_);
lean_dec(v_j_615_);
switch(lean_obj_tag(v___x_616_))
{
case 0:
{
lean_object* v_key_617_; size_t v___x_618_; size_t v___x_619_; uint8_t v___x_620_; 
v_key_617_ = lean_ctor_get(v___x_616_, 0);
v___x_618_ = lean_ptr_addr(v_x_610_);
v___x_619_ = lean_ptr_addr(v_key_617_);
v___x_620_ = lean_usize_dec_eq(v___x_618_, v___x_619_);
return v___x_620_;
}
case 1:
{
lean_object* v_node_621_; size_t v___x_622_; size_t v___x_623_; 
v_node_621_ = lean_ctor_get(v___x_616_, 0);
v___x_622_ = ((size_t)5ULL);
v___x_623_ = lean_usize_shift_right(v_x_609_, v___x_622_);
v_x_608_ = v_node_621_;
v_x_609_ = v___x_623_;
goto _start;
}
default: 
{
uint8_t v___x_625_; 
v___x_625_ = 0;
return v___x_625_;
}
}
}
else
{
lean_object* v_ks_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v_ks_626_ = lean_ctor_get(v_x_608_, 0);
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_ks_626_, v___x_627_, v_x_610_);
return v___x_628_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_608_ = stack[0].m_obj;
size_t v_x_609_ = stack[1].m_num;
lean_object* v_x_610_ = stack[2].m_obj;
uint8_t v_res_629_;
v_res_629_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_608_, v_x_609_, v_x_610_);
stack->m_num = v_res_629_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___boxed(lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v_x_632_){
_start:
{
size_t v_x_897__boxed_633_; uint8_t v_res_634_; lean_object* v_r_635_; 
v_x_897__boxed_633_ = lean_unbox_usize(v_x_631_);
lean_dec(v_x_631_);
v_res_634_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_630_, v_x_897__boxed_633_, v_x_632_);
lean_dec_ref(v_x_632_);
lean_dec_ref(v_x_630_);
v_r_635_ = lean_box(v_res_634_);
return v_r_635_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
size_t v___x_638_; size_t v___x_639_; size_t v___x_640_; uint64_t v___x_641_; size_t v___x_642_; uint8_t v___x_643_; 
v___x_638_ = lean_ptr_addr(v_x_637_);
v___x_639_ = ((size_t)3ULL);
v___x_640_ = lean_usize_shift_right(v___x_638_, v___x_639_);
v___x_641_ = lean_usize_to_uint64(v___x_640_);
v___x_642_ = lean_uint64_to_usize(v___x_641_);
v___x_643_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_636_, v___x_642_, v_x_637_);
return v___x_643_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_636_ = stack[0].m_obj;
lean_object* v_x_637_ = stack[1].m_obj;
uint8_t v_res_644_;
v_res_644_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_636_, v_x_637_);
stack->m_num = v_res_644_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg___boxed(lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
uint8_t v_res_647_; lean_object* v_r_648_; 
v_res_647_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_645_, v_x_646_);
lean_dec_ref(v_x_646_);
lean_dec_ref(v_x_645_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(lean_object* v_e_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_650_, v_a_651_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_664_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_664_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_664_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_664_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v_varMap_658_; uint8_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
v_varMap_658_ = lean_ctor_get(v_a_654_, 1);
lean_inc_ref(v_varMap_658_);
lean_dec(v_a_654_);
v___x_659_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_varMap_658_, v_e_649_);
lean_dec_ref(v_varMap_658_);
v___x_660_ = lean_box(v___x_659_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_660_);
v___x_662_ = v___x_656_;
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
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
v_a_665_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_653_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_653_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_649_ = stack[0].m_obj;
lean_object* v_a_650_ = stack[1].m_obj;
lean_object* v_a_651_ = stack[2].m_obj;
lean_object* v_res_673_;
v_res_673_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_649_, v_a_650_, v_a_651_);
stack->m_obj
 = v_res_673_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg___boxed(lean_object* v_e_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_674_, v_a_675_, v_a_676_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec_ref(v_e_674_);
return v_res_678_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar(lean_object* v_e_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_679_, v_a_680_, v_a_688_);
return v___x_691_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_hasVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_679_ = stack[0].m_obj;
lean_object* v_a_680_ = stack[1].m_obj;
lean_object* v_a_681_ = stack[2].m_obj;
lean_object* v_a_682_ = stack[3].m_obj;
lean_object* v_a_683_ = stack[4].m_obj;
lean_object* v_a_684_ = stack[5].m_obj;
lean_object* v_a_685_ = stack[6].m_obj;
lean_object* v_a_686_ = stack[7].m_obj;
lean_object* v_a_687_ = stack[8].m_obj;
lean_object* v_a_688_ = stack[9].m_obj;
lean_object* v_a_689_ = stack[10].m_obj;
lean_object* v_res_692_;
v_res_692_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar(v_e_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
stack->m_obj
 = v_res_692_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___boxed(lean_object* v_e_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar(v_e_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_e_693_);
return v_res_705_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(lean_object* v_00_u03b2_706_, lean_object* v_x_707_, lean_object* v_x_708_){
_start:
{
uint8_t v___x_709_; 
v___x_709_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_707_, v_x_708_);
return v___x_709_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_707_ = stack[1].m_obj;
lean_object* v_x_708_ = stack[2].m_obj;
uint8_t v_res_710_;
v_res_710_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(lean_box(0), v_x_707_, v_x_708_);
stack->m_num = v_res_710_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___boxed(lean_object* v_00_u03b2_711_, lean_object* v_x_712_, lean_object* v_x_713_){
_start:
{
uint8_t v_res_714_; lean_object* v_r_715_; 
v_res_714_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(v_00_u03b2_711_, v_x_712_, v_x_713_);
lean_dec_ref(v_x_713_);
lean_dec_ref(v_x_712_);
v_r_715_ = lean_box(v_res_714_);
return v_r_715_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(lean_object* v_00_u03b2_716_, lean_object* v_x_717_, size_t v_x_718_, lean_object* v_x_719_){
_start:
{
uint8_t v___x_720_; 
v___x_720_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_717_, v_x_718_, v_x_719_);
return v___x_720_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_717_ = stack[1].m_obj;
size_t v_x_718_ = stack[2].m_num;
lean_object* v_x_719_ = stack[3].m_obj;
uint8_t v_res_721_;
v_res_721_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(lean_box(0), v_x_717_, v_x_718_, v_x_719_);
stack->m_num = v_res_721_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_722_, lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_x_725_){
_start:
{
size_t v_x_1076__boxed_726_; uint8_t v_res_727_; lean_object* v_r_728_; 
v_x_1076__boxed_726_ = lean_unbox_usize(v_x_724_);
lean_dec(v_x_724_);
v_res_727_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(v_00_u03b2_722_, v_x_723_, v_x_1076__boxed_726_, v_x_725_);
lean_dec_ref(v_x_725_);
lean_dec_ref(v_x_723_);
v_r_728_ = lean_box(v_res_727_);
return v_r_728_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_729_, lean_object* v_keys_730_, lean_object* v_vals_731_, lean_object* v_heq_732_, lean_object* v_i_733_, lean_object* v_k_734_){
_start:
{
uint8_t v___x_735_; 
v___x_735_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_730_, v_i_733_, v_k_734_);
return v___x_735_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_730_ = stack[1].m_obj;
lean_object* v_vals_731_ = stack[2].m_obj;
lean_object* v_i_733_ = stack[4].m_obj;
lean_object* v_k_734_ = stack[5].m_obj;
uint8_t v_res_736_;
v_res_736_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(lean_box(0), v_keys_730_, v_vals_731_, lean_box(0), v_i_733_, v_k_734_);
stack->m_num = v_res_736_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_737_, lean_object* v_keys_738_, lean_object* v_vals_739_, lean_object* v_heq_740_, lean_object* v_i_741_, lean_object* v_k_742_){
_start:
{
uint8_t v_res_743_; lean_object* v_r_744_; 
v_res_743_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(v_00_u03b2_737_, v_keys_738_, v_vals_739_, v_heq_740_, v_i_741_, v_k_742_);
lean_dec_ref(v_k_742_);
lean_dec_ref(v_vals_739_);
lean_dec_ref(v_keys_738_);
v_r_744_ = lean_box(v_res_743_);
return v_r_744_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(lean_object* v_e_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_745_, v_a_746_, v_a_747_);
return v___x_749_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_745_ = stack[0].m_obj;
lean_object* v_a_746_ = stack[1].m_obj;
lean_object* v_a_747_ = stack[2].m_obj;
lean_object* v_res_750_;
v_res_750_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(v_e_745_, v_a_746_, v_a_747_);
stack->m_obj
 = v_res_750_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg___boxed(lean_object* v_e_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(v_e_751_, v_a_752_, v_a_753_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_e_751_);
return v_res_755_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(lean_object* v_e_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_756_, v_a_757_, v_a_765_);
return v___x_768_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_756_ = stack[0].m_obj;
lean_object* v_a_757_ = stack[1].m_obj;
lean_object* v_a_758_ = stack[2].m_obj;
lean_object* v_a_759_ = stack[3].m_obj;
lean_object* v_a_760_ = stack[4].m_obj;
lean_object* v_a_761_ = stack[5].m_obj;
lean_object* v_a_762_ = stack[6].m_obj;
lean_object* v_a_763_ = stack[7].m_obj;
lean_object* v_a_764_ = stack[8].m_obj;
lean_object* v_a_765_ = stack[9].m_obj;
lean_object* v_a_766_ = stack[10].m_obj;
lean_object* v_res_769_;
v_res_769_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(v_e_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
stack->m_obj
 = v_res_769_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___boxed(lean_object* v_e_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(v_e_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec(v_a_771_);
lean_dec_ref(v_e_770_);
return v_res_782_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(lean_object* v_x_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_box(0);
v___x_788_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_784_, v_a_785_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_810_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_810_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_810_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_810_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___y_794_; lean_object* v_elimEqs_805_; lean_object* v_size_806_; uint8_t v___x_807_; 
v_elimEqs_805_ = lean_ctor_get(v_a_789_, 9);
lean_inc_ref(v_elimEqs_805_);
lean_dec(v_a_789_);
v_size_806_ = lean_ctor_get(v_elimEqs_805_, 2);
v___x_807_ = lean_nat_dec_lt(v_x_783_, v_size_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; 
lean_dec_ref(v_elimEqs_805_);
v___x_808_ = l_outOfBounds___redArg(v___x_787_);
v___y_794_ = v___x_808_;
goto v___jp_793_;
}
else
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_PersistentArray_get_x21___redArg(v___x_787_, v_elimEqs_805_, v_x_783_);
lean_dec_ref(v_elimEqs_805_);
v___y_794_ = v___x_809_;
goto v___jp_793_;
}
v___jp_793_:
{
if (lean_obj_tag(v___y_794_) == 0)
{
uint8_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_795_ = 0;
v___x_796_ = lean_box(v___x_795_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_796_);
v___x_798_ = v___x_791_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
else
{
uint8_t v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
lean_dec_ref_known(v___y_794_, 1);
v___x_800_ = 1;
v___x_801_ = lean_box(v___x_800_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_801_);
v___x_803_ = v___x_791_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
v_a_811_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_788_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_788_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_783_ = stack[0].m_obj;
lean_object* v_a_784_ = stack[1].m_obj;
lean_object* v_a_785_ = stack[2].m_obj;
lean_object* v_res_819_;
v_res_819_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_783_, v_a_784_, v_a_785_);
stack->m_obj
 = v_res_819_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg___boxed(lean_object* v_x_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_820_, v_a_821_, v_a_822_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec(v_x_820_);
return v_res_824_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated(lean_object* v_x_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_825_, v_a_826_, v_a_834_);
return v___x_837_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_eliminated_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_825_ = stack[0].m_obj;
lean_object* v_a_826_ = stack[1].m_obj;
lean_object* v_a_827_ = stack[2].m_obj;
lean_object* v_a_828_ = stack[3].m_obj;
lean_object* v_a_829_ = stack[4].m_obj;
lean_object* v_a_830_ = stack[5].m_obj;
lean_object* v_a_831_ = stack[6].m_obj;
lean_object* v_a_832_ = stack[7].m_obj;
lean_object* v_a_833_ = stack[8].m_obj;
lean_object* v_a_834_ = stack[9].m_obj;
lean_object* v_a_835_ = stack[10].m_obj;
lean_object* v_res_838_;
v_res_838_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated(v_x_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
stack->m_obj
 = v_res_838_;
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_assert_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_852_ = stack[0].m_obj;
lean_object* v_a_853_ = stack[1].m_obj;
lean_object* v_a_854_ = stack[2].m_obj;
lean_object* v_a_855_ = stack[3].m_obj;
lean_object* v_a_856_ = stack[4].m_obj;
lean_object* v_a_857_ = stack[5].m_obj;
lean_object* v_a_858_ = stack[6].m_obj;
lean_object* v_a_859_ = stack[7].m_obj;
lean_object* v_a_860_ = stack[8].m_obj;
lean_object* v_a_861_ = stack[9].m_obj;
lean_object* v_a_862_ = stack[10].m_obj;
lean_object* v_res_864_;
v_res_864_ = lean_grind_cutsat_assert_eq(v_c_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
stack->m_obj
 = v_res_864_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_assert___boxed(lean_object* v_c_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_00___x40___internal___hyg_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = lean_grind_cutsat_assert_eq(v_c_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(lean_object* v_x_878_, lean_object* v_s_879_){
_start:
{
lean_object* v_vars_880_; lean_object* v_varMap_881_; lean_object* v_varsHistory_882_; lean_object* v_natToIntMap_883_; lean_object* v_natDef_884_; lean_object* v_dvds_885_; lean_object* v_lowers_886_; lean_object* v_uppers_887_; lean_object* v_diseqs_888_; lean_object* v_elimEqs_889_; lean_object* v_elimStack_890_; lean_object* v_occurs_891_; lean_object* v_assignment_892_; lean_object* v_nextCnstrId_893_; uint8_t v_caseSplits_894_; lean_object* v_steps_895_; lean_object* v_conflict_x3f_896_; lean_object* v_diseqSplits_897_; lean_object* v_divMod_898_; uint8_t v_usedCommRing_899_; lean_object* v_nonlinearOccs_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_908_; 
v_vars_880_ = lean_ctor_get(v_s_879_, 0);
v_varMap_881_ = lean_ctor_get(v_s_879_, 1);
v_varsHistory_882_ = lean_ctor_get(v_s_879_, 2);
v_natToIntMap_883_ = lean_ctor_get(v_s_879_, 3);
v_natDef_884_ = lean_ctor_get(v_s_879_, 4);
v_dvds_885_ = lean_ctor_get(v_s_879_, 5);
v_lowers_886_ = lean_ctor_get(v_s_879_, 6);
v_uppers_887_ = lean_ctor_get(v_s_879_, 7);
v_diseqs_888_ = lean_ctor_get(v_s_879_, 8);
v_elimEqs_889_ = lean_ctor_get(v_s_879_, 9);
v_elimStack_890_ = lean_ctor_get(v_s_879_, 10);
v_occurs_891_ = lean_ctor_get(v_s_879_, 11);
v_assignment_892_ = lean_ctor_get(v_s_879_, 12);
v_nextCnstrId_893_ = lean_ctor_get(v_s_879_, 13);
v_caseSplits_894_ = lean_ctor_get_uint8(v_s_879_, sizeof(void*)*19);
v_steps_895_ = lean_ctor_get(v_s_879_, 14);
v_conflict_x3f_896_ = lean_ctor_get(v_s_879_, 15);
v_diseqSplits_897_ = lean_ctor_get(v_s_879_, 16);
v_divMod_898_ = lean_ctor_get(v_s_879_, 17);
v_usedCommRing_899_ = lean_ctor_get_uint8(v_s_879_, sizeof(void*)*19 + 1);
v_nonlinearOccs_900_ = lean_ctor_get(v_s_879_, 18);
v_isSharedCheck_908_ = !lean_is_exclusive(v_s_879_);
if (v_isSharedCheck_908_ == 0)
{
v___x_902_ = v_s_879_;
v_isShared_903_ = v_isSharedCheck_908_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_nonlinearOccs_900_);
lean_inc(v_divMod_898_);
lean_inc(v_diseqSplits_897_);
lean_inc(v_conflict_x3f_896_);
lean_inc(v_steps_895_);
lean_inc(v_nextCnstrId_893_);
lean_inc(v_assignment_892_);
lean_inc(v_occurs_891_);
lean_inc(v_elimStack_890_);
lean_inc(v_elimEqs_889_);
lean_inc(v_diseqs_888_);
lean_inc(v_uppers_887_);
lean_inc(v_lowers_886_);
lean_inc(v_dvds_885_);
lean_inc(v_natDef_884_);
lean_inc(v_natToIntMap_883_);
lean_inc(v_varsHistory_882_);
lean_inc(v_varMap_881_);
lean_inc(v_vars_880_);
lean_dec(v_s_879_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_908_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_892_, v_x_878_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 12, v___x_904_);
v___x_906_ = v___x_902_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_vars_880_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_varMap_881_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_varsHistory_882_);
lean_ctor_set(v_reuseFailAlloc_907_, 3, v_natToIntMap_883_);
lean_ctor_set(v_reuseFailAlloc_907_, 4, v_natDef_884_);
lean_ctor_set(v_reuseFailAlloc_907_, 5, v_dvds_885_);
lean_ctor_set(v_reuseFailAlloc_907_, 6, v_lowers_886_);
lean_ctor_set(v_reuseFailAlloc_907_, 7, v_uppers_887_);
lean_ctor_set(v_reuseFailAlloc_907_, 8, v_diseqs_888_);
lean_ctor_set(v_reuseFailAlloc_907_, 9, v_elimEqs_889_);
lean_ctor_set(v_reuseFailAlloc_907_, 10, v_elimStack_890_);
lean_ctor_set(v_reuseFailAlloc_907_, 11, v_occurs_891_);
lean_ctor_set(v_reuseFailAlloc_907_, 12, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_907_, 13, v_nextCnstrId_893_);
lean_ctor_set(v_reuseFailAlloc_907_, 14, v_steps_895_);
lean_ctor_set(v_reuseFailAlloc_907_, 15, v_conflict_x3f_896_);
lean_ctor_set(v_reuseFailAlloc_907_, 16, v_diseqSplits_897_);
lean_ctor_set(v_reuseFailAlloc_907_, 17, v_divMod_898_);
lean_ctor_set(v_reuseFailAlloc_907_, 18, v_nonlinearOccs_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_907_, sizeof(void*)*19, v_caseSplits_894_);
lean_ctor_set_uint8(v_reuseFailAlloc_907_, sizeof(void*)*19 + 1, v_usedCommRing_899_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_x_909_, lean_object* v_s_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(v_x_909_, v_s_910_);
lean_dec(v_x_909_);
return v_res_911_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object* v_x_912_, lean_object* v_a_913_){
_start:
{
lean_object* v___f_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___f_915_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_915_, 0, v_x_912_);
v___x_916_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_917_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_916_, v___f_915_, v_a_913_);
return v___x_917_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_912_ = stack[0].m_obj;
lean_object* v_a_913_ = stack[1].m_obj;
lean_object* v_res_918_;
v_res_918_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_912_, v_a_913_);
stack->m_obj
 = v_res_918_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___boxed(lean_object* v_x_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_919_, v_a_920_);
lean_dec(v_a_920_);
return v_res_922_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(lean_object* v_x_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_923_, v_a_924_);
return v___x_935_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_923_ = stack[0].m_obj;
lean_object* v_a_924_ = stack[1].m_obj;
lean_object* v_a_925_ = stack[2].m_obj;
lean_object* v_a_926_ = stack[3].m_obj;
lean_object* v_a_927_ = stack[4].m_obj;
lean_object* v_a_928_ = stack[5].m_obj;
lean_object* v_a_929_ = stack[6].m_obj;
lean_object* v_a_930_ = stack[7].m_obj;
lean_object* v_a_931_ = stack[8].m_obj;
lean_object* v_a_932_ = stack[9].m_obj;
lean_object* v_a_933_ = stack[10].m_obj;
lean_object* v_res_936_;
v_res_936_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(v_x_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
stack->m_obj
 = v_res_936_;
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
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(lean_object* v_r_958_, lean_object* v_p_959_, lean_object* v_a_960_, lean_object* v_a_961_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_958_ = stack[0].m_obj;
lean_object* v_p_959_ = stack[1].m_obj;
lean_object* v_a_960_ = stack[2].m_obj;
lean_object* v_a_961_ = stack[3].m_obj;
lean_object* v_res_1023_;
v_res_1023_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v_r_958_, v_p_959_, v_a_960_, v_a_961_);
stack->m_obj
 = v_res_1023_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___boxed(lean_object* v_r_1024_, lean_object* v_p_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v_r_1024_, v_p_1025_, v_a_1026_, v_a_1027_);
lean_dec_ref(v_a_1027_);
lean_dec(v_a_1026_);
return v_res_1029_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(lean_object* v_r_1030_, lean_object* v_p_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v_r_1030_, v_p_1031_, v_a_1032_, v_a_1040_);
return v___x_1043_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1030_ = stack[0].m_obj;
lean_object* v_p_1031_ = stack[1].m_obj;
lean_object* v_a_1032_ = stack[2].m_obj;
lean_object* v_a_1033_ = stack[3].m_obj;
lean_object* v_a_1034_ = stack[4].m_obj;
lean_object* v_a_1035_ = stack[5].m_obj;
lean_object* v_a_1036_ = stack[6].m_obj;
lean_object* v_a_1037_ = stack[7].m_obj;
lean_object* v_a_1038_ = stack[8].m_obj;
lean_object* v_a_1039_ = stack[9].m_obj;
lean_object* v_a_1040_ = stack[10].m_obj;
lean_object* v_a_1041_ = stack[11].m_obj;
lean_object* v_res_1044_;
v_res_1044_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(v_r_1030_, v_p_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
stack->m_obj
 = v_res_1044_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___boxed(lean_object* v_r_1045_, lean_object* v_p_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(v_r_1045_, v_p_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec(v_a_1047_);
return v_res_1058_;
}
}
lean_object* l_Int_Internal_Linear_Poly_pp___redArg(lean_object* v_p_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
if (lean_obj_tag(v_p_1059_) == 0)
{
lean_object* v_k_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1073_; 
v_k_1063_ = lean_ctor_get(v_p_1059_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_p_1059_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1065_ = v_p_1059_;
v_isShared_1066_ = v_isSharedCheck_1073_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_k_1063_);
lean_dec(v_p_1059_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1073_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1067_ = l_Int_repr(v_k_1063_);
lean_dec(v_k_1063_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set_tag(v___x_1065_, 3);
lean_ctor_set(v___x_1065_, 0, v___x_1067_);
v___x_1069_ = v___x_1065_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = l_Lean_MessageData_ofFormat(v___x_1069_);
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
return v___x_1071_;
}
}
}
else
{
lean_object* v_k_1074_; lean_object* v_v_1075_; lean_object* v_p_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v_k_1074_ = lean_ctor_get(v_p_1059_, 0);
lean_inc(v_k_1074_);
v_v_1075_ = lean_ctor_get(v_p_1059_, 1);
lean_inc(v_v_1075_);
v_p_1076_ = lean_ctor_get(v_p_1059_, 2);
lean_inc_ref(v_p_1076_);
lean_dec_ref_known(v_p_1059_, 3);
v___x_1077_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_1078_ = lean_int_dec_eq(v_k_1074_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_1075_, v_a_1060_, v_a_1061_);
lean_dec(v_v_1075_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v___x_1081_ = l_Int_repr(v_k_1074_);
lean_dec(v_k_1074_);
v___x_1082_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
v___x_1083_ = l_Lean_MessageData_ofFormat(v___x_1082_);
v___x_1084_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_1080_);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v___x_1087_, v_p_1076_, v_a_1060_, v_a_1061_);
return v___x_1088_;
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec_ref(v_p_1076_);
lean_dec(v_k_1074_);
v_a_1089_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1079_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1079_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
lean_object* v___x_1097_; 
lean_dec(v_k_1074_);
v___x_1097_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_1075_, v_a_1060_, v_a_1061_);
lean_dec(v_v_1075_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1097_, 1);
v___x_1099_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_1098_);
v___x_1100_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v___x_1099_, v_p_1076_, v_a_1060_, v_a_1061_);
return v___x_1100_;
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec_ref(v_p_1076_);
v_a_1101_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1097_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1097_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_pp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1059_ = stack[0].m_obj;
lean_object* v_a_1060_ = stack[1].m_obj;
lean_object* v_a_1061_ = stack[2].m_obj;
lean_object* v_res_1109_;
v_res_1109_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1059_, v_a_1060_, v_a_1061_);
stack->m_obj
 = v_res_1109_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___redArg___boxed(lean_object* v_p_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1110_, v_a_1111_, v_a_1112_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
return v_res_1114_;
}
}
lean_object* l_Int_Internal_Linear_Poly_pp(lean_object* v_p_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1115_, v_a_1116_, v_a_1124_);
return v___x_1127_;
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_pp_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1115_ = stack[0].m_obj;
lean_object* v_a_1116_ = stack[1].m_obj;
lean_object* v_a_1117_ = stack[2].m_obj;
lean_object* v_a_1118_ = stack[3].m_obj;
lean_object* v_a_1119_ = stack[4].m_obj;
lean_object* v_a_1120_ = stack[5].m_obj;
lean_object* v_a_1121_ = stack[6].m_obj;
lean_object* v_a_1122_ = stack[7].m_obj;
lean_object* v_a_1123_ = stack[8].m_obj;
lean_object* v_a_1124_ = stack[9].m_obj;
lean_object* v_a_1125_ = stack[10].m_obj;
lean_object* v_res_1128_;
v_res_1128_ = l_Int_Internal_Linear_Poly_pp(v_p_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
stack->m_obj
 = v_res_1128_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___boxed(lean_object* v_p_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Int_Internal_Linear_Poly_pp(v_p_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec(v_a_1130_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0(lean_object* v_a_1142_, lean_object* v___x_1143_, lean_object* v_x_1144_){
_start:
{
lean_object* v_size_1145_; uint8_t v___x_1146_; 
v_size_1145_ = lean_ctor_get(v_a_1142_, 2);
v___x_1146_ = lean_nat_dec_lt(v_x_1144_, v_size_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; 
v___x_1147_ = l_outOfBounds___redArg(v___x_1143_);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1143_, v_a_1142_, v_x_1144_);
return v___x_1148_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed(lean_object* v_a_1149_, lean_object* v___x_1150_, lean_object* v_x_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0(v_a_1149_, v___x_1150_, v_x_1151_);
lean_dec(v_x_1151_);
lean_dec_ref(v___x_1150_);
lean_dec_ref(v_a_1149_);
return v_res_1152_;
}
}
lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(lean_object* v_p_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = l_Lean_instInhabitedExpr;
v___x_1158_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_1154_, v_a_1155_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___f_1160_; lean_object* v___x_1161_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v___f_1160_ = lean_alloc_closure((void*)(l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1160_, 0, v_a_1159_);
lean_closure_set(v___f_1160_, 1, v___x_1157_);
v___x_1161_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_1160_, v_p_1153_);
return v___x_1161_;
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_dec_ref(v_p_1153_);
v_a_1162_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1158_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1158_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1153_ = stack[0].m_obj;
lean_object* v_a_1154_ = stack[1].m_obj;
lean_object* v_a_1155_ = stack[2].m_obj;
lean_object* v_res_1170_;
v_res_1170_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1153_, v_a_1154_, v_a_1155_);
stack->m_obj
 = v_res_1170_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___boxed(lean_object* v_p_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1171_, v_a_1172_, v_a_1173_);
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1172_);
return v_res_1175_;
}
}
lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27(lean_object* v_p_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1176_, v_a_1177_, v_a_1185_);
return v___x_1188_;
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_denoteExpr_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1176_ = stack[0].m_obj;
lean_object* v_a_1177_ = stack[1].m_obj;
lean_object* v_a_1178_ = stack[2].m_obj;
lean_object* v_a_1179_ = stack[3].m_obj;
lean_object* v_a_1180_ = stack[4].m_obj;
lean_object* v_a_1181_ = stack[5].m_obj;
lean_object* v_a_1182_ = stack[6].m_obj;
lean_object* v_a_1183_ = stack[7].m_obj;
lean_object* v_a_1184_ = stack[8].m_obj;
lean_object* v_a_1185_ = stack[9].m_obj;
lean_object* v_a_1186_ = stack[10].m_obj;
lean_object* v_res_1189_;
v_res_1189_ = l_Int_Internal_Linear_Poly_denoteExpr_x27(v_p_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
stack->m_obj
 = v_res_1189_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___boxed(lean_object* v_p_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Int_Internal_Linear_Poly_denoteExpr_x27(v_p_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec(v_a_1198_);
lean_dec_ref(v_a_1197_);
lean_dec(v_a_1196_);
lean_dec_ref(v_a_1195_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec(v_a_1191_);
return v_res_1202_;
}
}
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object* v_c_1203_){
_start:
{
lean_object* v_p_1204_; 
v_p_1204_ = lean_ctor_get(v_c_1203_, 1);
if (lean_obj_tag(v_p_1204_) == 0)
{
lean_object* v_d_1205_; lean_object* v_k_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
v_d_1205_ = lean_ctor_get(v_c_1203_, 0);
v_k_1206_ = lean_ctor_get(v_p_1204_, 0);
v___x_1207_ = lean_int_emod(v_k_1206_, v_d_1205_);
v___x_1208_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1209_ = lean_int_dec_eq(v___x_1207_, v___x_1208_);
lean_dec(v___x_1207_);
return v___x_1209_;
}
else
{
lean_object* v_d_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v_d_1210_ = lean_ctor_get(v_c_1203_, 0);
v___x_1211_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_1212_ = lean_int_dec_eq(v_d_1210_, v___x_1211_);
return v___x_1212_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1203_ = stack[0].m_obj;
uint8_t v_res_1213_;
v_res_1213_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_c_1203_);
stack->m_num = v_res_1213_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial___boxed(lean_object* v_c_1214_){
_start:
{
uint8_t v_res_1215_; lean_object* v_r_1216_; 
v_res_1215_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_c_1214_);
lean_dec_ref(v_c_1214_);
v_r_1216_ = lean_box(v_res_1215_);
return v_r_1216_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0));
v___x_1219_ = l_Lean_stringToMessageData(v___x_1218_);
return v___x_1219_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object* v_c_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_d_1224_; lean_object* v_p_1225_; lean_object* v___x_1226_; 
v_d_1224_ = lean_ctor_get(v_c_1220_, 0);
lean_inc(v_d_1224_);
v_p_1225_ = lean_ctor_get(v_c_1220_, 1);
lean_inc_ref(v_p_1225_);
lean_dec_ref(v_c_1220_);
v___x_1226_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1225_, v_a_1221_, v_a_1222_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1240_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1229_ = v___x_1226_;
v_isShared_1230_ = v_isSharedCheck_1240_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1226_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1240_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1231_ = l_Int_repr(v_d_1224_);
lean_dec(v_d_1224_);
v___x_1232_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
v___x_1233_ = l_Lean_MessageData_ofFormat(v___x_1232_);
v___x_1234_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set(v___x_1236_, 1, v_a_1227_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1236_);
v___x_1238_ = v___x_1229_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
else
{
lean_dec(v_d_1224_);
return v___x_1226_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1220_ = stack[0].m_obj;
lean_object* v_a_1221_ = stack[1].m_obj;
lean_object* v_a_1222_ = stack[2].m_obj;
lean_object* v_res_1241_;
v_res_1241_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1220_, v_a_1221_, v_a_1222_);
stack->m_obj
 = v_res_1241_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___boxed(lean_object* v_c_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1242_, v_a_1243_, v_a_1244_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
return v_res_1246_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(lean_object* v_c_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1247_, v_a_1248_, v_a_1256_);
return v___x_1259_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1247_ = stack[0].m_obj;
lean_object* v_a_1248_ = stack[1].m_obj;
lean_object* v_a_1249_ = stack[2].m_obj;
lean_object* v_a_1250_ = stack[3].m_obj;
lean_object* v_a_1251_ = stack[4].m_obj;
lean_object* v_a_1252_ = stack[5].m_obj;
lean_object* v_a_1253_ = stack[6].m_obj;
lean_object* v_a_1254_ = stack[7].m_obj;
lean_object* v_a_1255_ = stack[8].m_obj;
lean_object* v_a_1256_ = stack[9].m_obj;
lean_object* v_a_1257_ = stack[10].m_obj;
lean_object* v_res_1260_;
v_res_1260_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(v_c_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
stack->m_obj
 = v_res_1260_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___boxed(lean_object* v_c_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(v_c_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec(v_a_1262_);
return v_res_1273_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_unsigned_to_nat(0u);
v___x_1280_ = l_Lean_Level_ofNat(v___x_1279_);
return v___x_1280_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = lean_box(0);
v___x_1282_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3);
v___x_1283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
lean_ctor_set(v___x_1283_, 1, v___x_1281_);
return v___x_1283_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4);
v___x_1285_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2));
v___x_1286_ = l_Lean_Expr_const___override(v___x_1285_, v___x_1284_);
return v___x_1286_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = lean_box(0);
v___x_1291_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7));
v___x_1292_ = l_Lean_Expr_const___override(v___x_1291_, v___x_1290_);
return v___x_1292_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1297_ = lean_box(0);
v___x_1298_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10));
v___x_1299_ = l_Lean_Expr_const___override(v___x_1298_, v___x_1297_);
return v___x_1299_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(lean_object* v_c_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_d_1304_; lean_object* v_p_1305_; lean_object* v___x_1306_; 
v_d_1304_ = lean_ctor_get(v_c_1300_, 0);
lean_inc(v_d_1304_);
v_p_1305_ = lean_ctor_get(v_c_1300_, 1);
lean_inc_ref(v_p_1305_);
lean_dec_ref(v_c_1300_);
v___x_1306_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1305_, v_a_1301_, v_a_1302_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1328_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1328_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1328_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___y_1312_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1318_ = lean_int_dec_le(v___x_1317_, v_d_1304_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1319_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5);
v___x_1320_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8);
v___x_1321_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11);
v___x_1322_ = lean_int_neg(v_d_1304_);
lean_dec(v_d_1304_);
v___x_1323_ = l_Int_toNat(v___x_1322_);
lean_dec(v___x_1322_);
v___x_1324_ = l_Lean_instToExprInt_mkNat(v___x_1323_);
v___x_1325_ = l_Lean_mkApp3(v___x_1319_, v___x_1320_, v___x_1321_, v___x_1324_);
v___y_1312_ = v___x_1325_;
goto v___jp_1311_;
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = l_Int_toNat(v_d_1304_);
lean_dec(v_d_1304_);
v___x_1327_ = l_Lean_instToExprInt_mkNat(v___x_1326_);
v___y_1312_ = v___x_1327_;
goto v___jp_1311_;
}
v___jp_1311_:
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = l_Lean_mkIntDvd(v___y_1312_, v_a_1307_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1313_);
v___x_1315_ = v___x_1309_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
else
{
lean_dec(v_d_1304_);
return v___x_1306_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1300_ = stack[0].m_obj;
lean_object* v_a_1301_ = stack[1].m_obj;
lean_object* v_a_1302_ = stack[2].m_obj;
lean_object* v_res_1329_;
v_res_1329_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1300_, v_a_1301_, v_a_1302_);
stack->m_obj
 = v_res_1329_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1330_, v_a_1331_, v_a_1332_);
lean_dec_ref(v_a_1332_);
lean_dec(v_a_1331_);
return v_res_1334_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(lean_object* v_c_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1335_, v_a_1336_, v_a_1344_);
return v___x_1347_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1335_ = stack[0].m_obj;
lean_object* v_a_1336_ = stack[1].m_obj;
lean_object* v_a_1337_ = stack[2].m_obj;
lean_object* v_a_1338_ = stack[3].m_obj;
lean_object* v_a_1339_ = stack[4].m_obj;
lean_object* v_a_1340_ = stack[5].m_obj;
lean_object* v_a_1341_ = stack[6].m_obj;
lean_object* v_a_1342_ = stack[7].m_obj;
lean_object* v_a_1343_ = stack[8].m_obj;
lean_object* v_a_1344_ = stack[9].m_obj;
lean_object* v_a_1345_ = stack[10].m_obj;
lean_object* v_res_1348_;
v_res_1348_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(v_c_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
stack->m_obj
 = v_res_1348_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___boxed(lean_object* v_c_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(v_c_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
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
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(lean_object* v_msgData_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v___x_1368_; lean_object* v_env_1369_; uint8_t v___x_1370_; lean_object* v_env_1371_; lean_object* v___x_1372_; lean_object* v_toCold_1373_; lean_object* v_mctx_1374_; lean_object* v_lctx_1375_; lean_object* v_options_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1368_ = lean_st_ref_get(v___y_1366_);
v_env_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc_ref(v_env_1369_);
lean_dec(v___x_1368_);
v___x_1370_ = 0;
v_env_1371_ = l_Lean_Environment_setRecordingDeps(v_env_1369_, v___x_1370_);
v___x_1372_ = lean_st_ref_get(v___y_1364_);
v_toCold_1373_ = lean_ctor_get(v___y_1365_, 0);
v_mctx_1374_ = lean_ctor_get(v___x_1372_, 0);
lean_inc_ref(v_mctx_1374_);
lean_dec(v___x_1372_);
v_lctx_1375_ = lean_ctor_get(v___y_1363_, 2);
v_options_1376_ = lean_ctor_get(v_toCold_1373_, 2);
lean_inc_ref(v_options_1376_);
lean_inc_ref(v_lctx_1375_);
v___x_1377_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1377_, 0, v_env_1371_);
lean_ctor_set(v___x_1377_, 1, v_mctx_1374_);
lean_ctor_set(v___x_1377_, 2, v_lctx_1375_);
lean_ctor_set(v___x_1377_, 3, v_options_1376_);
v___x_1378_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
lean_ctor_set(v___x_1378_, 1, v_msgData_1362_);
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1362_ = stack[0].m_obj;
lean_object* v___y_1363_ = stack[1].m_obj;
lean_object* v___y_1364_ = stack[2].m_obj;
lean_object* v___y_1365_ = stack[3].m_obj;
lean_object* v___y_1366_ = stack[4].m_obj;
lean_object* v_res_1380_;
v_res_1380_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msgData_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
stack->m_obj
 = v_res_1380_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object* v_msgData_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msgData_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
return v_res_1387_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(lean_object* v_msg_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_ref_1394_; lean_object* v___x_1395_; lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1404_; 
v_ref_1394_ = lean_ctor_get(v___y_1391_, 2);
v___x_1395_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msg_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
lean_inc(v_ref_1394_);
v___x_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_ref_1394_);
lean_ctor_set(v___x_1400_, 1, v_a_1396_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set_tag(v___x_1398_, 1);
lean_ctor_set(v___x_1398_, 0, v___x_1400_);
v___x_1402_ = v___x_1398_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1388_ = stack[0].m_obj;
lean_object* v___y_1389_ = stack[1].m_obj;
lean_object* v___y_1390_ = stack[2].m_obj;
lean_object* v___y_1391_ = stack[3].m_obj;
lean_object* v___y_1392_ = stack[4].m_obj;
lean_object* v_res_1405_;
v_res_1405_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
stack->m_obj
 = v_res_1405_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg___boxed(lean_object* v_msg_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
return v_res_1412_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0));
v___x_1415_ = l_Lean_stringToMessageData(v___x_1414_);
return v___x_1415_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3(void){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2));
v___x_1418_ = l_Lean_stringToMessageData(v___x_1417_);
return v___x_1418_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object* v_c_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1419_, v_a_1420_, v_a_1428_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1434_ = l_Lean_indentD(v_a_1432_);
v___x_1435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3);
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1437_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
return v___x_1438_;
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_a_1439_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1431_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1431_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1419_ = stack[0].m_obj;
lean_object* v_a_1420_ = stack[1].m_obj;
lean_object* v_a_1421_ = stack[2].m_obj;
lean_object* v_a_1422_ = stack[3].m_obj;
lean_object* v_a_1423_ = stack[4].m_obj;
lean_object* v_a_1424_ = stack[5].m_obj;
lean_object* v_a_1425_ = stack[6].m_obj;
lean_object* v_a_1426_ = stack[7].m_obj;
lean_object* v_a_1427_ = stack[8].m_obj;
lean_object* v_a_1428_ = stack[9].m_obj;
lean_object* v_a_1429_ = stack[10].m_obj;
lean_object* v_res_1447_;
v_res_1447_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
stack->m_obj
 = v_res_1447_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1455_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
lean_dec(v_a_1450_);
lean_dec(v_a_1449_);
return v_res_1460_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(lean_object* v_00_u03b1_1461_, lean_object* v_c_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
return v___x_1474_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1462_ = stack[1].m_obj;
lean_object* v_a_1463_ = stack[2].m_obj;
lean_object* v_a_1464_ = stack[3].m_obj;
lean_object* v_a_1465_ = stack[4].m_obj;
lean_object* v_a_1466_ = stack[5].m_obj;
lean_object* v_a_1467_ = stack[6].m_obj;
lean_object* v_a_1468_ = stack[7].m_obj;
lean_object* v_a_1469_ = stack[8].m_obj;
lean_object* v_a_1470_ = stack[9].m_obj;
lean_object* v_a_1471_ = stack[10].m_obj;
lean_object* v_a_1472_ = stack[11].m_obj;
lean_object* v_res_1475_;
v_res_1475_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(lean_box(0), v_c_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
stack->m_obj
 = v_res_1475_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1476_, lean_object* v_c_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(v_00_u03b1_1476_, v_c_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
lean_dec(v_a_1487_);
lean_dec_ref(v_a_1486_);
lean_dec(v_a_1485_);
lean_dec_ref(v_a_1484_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
lean_dec(v_a_1479_);
lean_dec(v_a_1478_);
return v_res_1489_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(lean_object* v_00_u03b1_1490_, lean_object* v_msg_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1491_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
return v___x_1503_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1491_ = stack[1].m_obj;
lean_object* v___y_1492_ = stack[2].m_obj;
lean_object* v___y_1493_ = stack[3].m_obj;
lean_object* v___y_1494_ = stack[4].m_obj;
lean_object* v___y_1495_ = stack[5].m_obj;
lean_object* v___y_1496_ = stack[6].m_obj;
lean_object* v___y_1497_ = stack[7].m_obj;
lean_object* v___y_1498_ = stack[8].m_obj;
lean_object* v___y_1499_ = stack[9].m_obj;
lean_object* v___y_1500_ = stack[10].m_obj;
lean_object* v___y_1501_ = stack[11].m_obj;
lean_object* v_res_1504_;
v_res_1504_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(lean_box(0), v_msg_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
stack->m_obj
 = v_res_1504_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___boxed(lean_object* v_00_u03b1_1505_, lean_object* v_msg_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(v_00_u03b1_1505_, v_msg_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec(v___y_1507_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial_spec__0(lean_object* v_a_1519_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_nat_to_int(v_a_1519_);
return v___x_1520_;
}
}
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(lean_object* v_c_1521_){
_start:
{
lean_object* v_p_1522_; 
v_p_1522_ = lean_ctor_get(v_c_1521_, 0);
if (lean_obj_tag(v_p_1522_) == 0)
{
lean_object* v_k_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v_k_1523_ = lean_ctor_get(v_p_1522_, 0);
v___x_1524_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1525_ = lean_int_dec_eq(v_k_1523_, v___x_1524_);
if (v___x_1525_ == 0)
{
uint8_t v___x_1526_; 
v___x_1526_ = 1;
return v___x_1526_;
}
else
{
uint8_t v___x_1527_; 
v___x_1527_ = 0;
return v___x_1527_;
}
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; uint8_t v___x_1533_; 
v___x_1528_ = l_Int_Internal_Linear_Poly_getConst(v_p_1522_);
v___x_1529_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v_p_1522_);
v___x_1530_ = lean_nat_to_int(v___x_1529_);
v___x_1531_ = lean_int_emod(v___x_1528_, v___x_1530_);
lean_dec(v___x_1530_);
lean_dec(v___x_1528_);
v___x_1532_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1533_ = lean_int_dec_eq(v___x_1531_, v___x_1532_);
lean_dec(v___x_1531_);
if (v___x_1533_ == 0)
{
uint8_t v___x_1534_; 
v___x_1534_ = 1;
return v___x_1534_;
}
else
{
uint8_t v___x_1535_; 
v___x_1535_ = 0;
return v___x_1535_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1521_ = stack[0].m_obj;
uint8_t v_res_1536_;
v_res_1536_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(v_c_1521_);
stack->m_num = v_res_1536_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial___boxed(lean_object* v_c_1537_){
_start:
{
uint8_t v_res_1538_; lean_object* v_r_1539_; 
v_res_1538_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(v_c_1537_);
lean_dec_ref(v_c_1537_);
v_r_1539_ = lean_box(v_res_1538_);
return v_r_1539_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0));
v___x_1542_ = l_Lean_stringToMessageData(v___x_1541_);
return v___x_1542_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(lean_object* v_c_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v_p_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1564_; 
v_p_1547_ = lean_ctor_get(v_c_1543_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_c_1543_);
if (v_isSharedCheck_1564_ == 0)
{
lean_object* v_unused_1565_; 
v_unused_1565_ = lean_ctor_get(v_c_1543_, 1);
lean_dec(v_unused_1565_);
v___x_1549_ = v_c_1543_;
v_isShared_1550_ = v_isSharedCheck_1564_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_p_1547_);
lean_dec(v_c_1543_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1564_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1547_, v_a_1544_, v_a_1545_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1563_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1554_ = v___x_1551_;
v_isShared_1555_ = v_isSharedCheck_1563_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1563_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1556_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1);
if (v_isShared_1550_ == 0)
{
lean_ctor_set_tag(v___x_1549_, 7);
lean_ctor_set(v___x_1549_, 1, v___x_1556_);
lean_ctor_set(v___x_1549_, 0, v_a_1552_);
v___x_1558_ = v___x_1549_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1552_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1560_; 
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1558_);
v___x_1560_ = v___x_1554_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_del_object(v___x_1549_);
return v___x_1551_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1543_ = stack[0].m_obj;
lean_object* v_a_1544_ = stack[1].m_obj;
lean_object* v_a_1545_ = stack[2].m_obj;
lean_object* v_res_1566_;
v_res_1566_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1543_, v_a_1544_, v_a_1545_);
stack->m_obj
 = v_res_1566_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___boxed(lean_object* v_c_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1567_, v_a_1568_, v_a_1569_);
lean_dec_ref(v_a_1569_);
lean_dec(v_a_1568_);
return v_res_1571_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(lean_object* v_c_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1572_, v_a_1573_, v_a_1581_);
return v___x_1584_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1572_ = stack[0].m_obj;
lean_object* v_a_1573_ = stack[1].m_obj;
lean_object* v_a_1574_ = stack[2].m_obj;
lean_object* v_a_1575_ = stack[3].m_obj;
lean_object* v_a_1576_ = stack[4].m_obj;
lean_object* v_a_1577_ = stack[5].m_obj;
lean_object* v_a_1578_ = stack[6].m_obj;
lean_object* v_a_1579_ = stack[7].m_obj;
lean_object* v_a_1580_ = stack[8].m_obj;
lean_object* v_a_1581_ = stack[9].m_obj;
lean_object* v_a_1582_ = stack[10].m_obj;
lean_object* v_res_1585_;
v_res_1585_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(v_c_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
stack->m_obj
 = v_res_1585_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___boxed(lean_object* v_c_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(v_c_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
lean_dec(v_a_1588_);
lean_dec(v_a_1587_);
return v_res_1598_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(lean_object* v_c_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1599_, v_a_1600_, v_a_1603_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1607_);
lean_dec_ref_known(v___x_1606_, 1);
v___x_1608_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1609_ = l_Lean_indentD(v_a_1607_);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1610_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
return v___x_1611_;
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
v_a_1612_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1606_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1606_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1599_ = stack[0].m_obj;
lean_object* v_a_1600_ = stack[1].m_obj;
lean_object* v_a_1601_ = stack[2].m_obj;
lean_object* v_a_1602_ = stack[3].m_obj;
lean_object* v_a_1603_ = stack[4].m_obj;
lean_object* v_a_1604_ = stack[5].m_obj;
lean_object* v_res_1620_;
v_res_1620_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
stack->m_obj
 = v_res_1620_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec(v_a_1622_);
return v_res_1628_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(lean_object* v_00_u03b1_1629_, lean_object* v_c_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1630_, v_a_1631_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1642_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1630_ = stack[1].m_obj;
lean_object* v_a_1631_ = stack[2].m_obj;
lean_object* v_a_1632_ = stack[3].m_obj;
lean_object* v_a_1633_ = stack[4].m_obj;
lean_object* v_a_1634_ = stack[5].m_obj;
lean_object* v_a_1635_ = stack[6].m_obj;
lean_object* v_a_1636_ = stack[7].m_obj;
lean_object* v_a_1637_ = stack[8].m_obj;
lean_object* v_a_1638_ = stack[9].m_obj;
lean_object* v_a_1639_ = stack[10].m_obj;
lean_object* v_a_1640_ = stack[11].m_obj;
lean_object* v_res_1643_;
v_res_1643_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(lean_box(0), v_c_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
stack->m_obj
 = v_res_1643_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1644_, lean_object* v_c_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(v_00_u03b1_1644_, v_c_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec(v_a_1646_);
return v_res_1657_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1659_ = l_Lean_mkIntLit(v___x_1658_);
return v___x_1659_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(lean_object* v_c_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v_p_1664_; lean_object* v___x_1665_; 
v_p_1664_ = lean_ctor_get(v_c_1660_, 0);
lean_inc_ref(v_p_1664_);
lean_dec_ref(v_c_1660_);
v___x_1665_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1664_, v_a_1661_, v_a_1662_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1676_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1676_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1676_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1670_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1671_ = l_Lean_mkIntEq(v_a_1666_, v___x_1670_);
v___x_1672_ = l_Lean_mkNot(v___x_1671_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1672_);
v___x_1674_ = v___x_1668_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
else
{
return v___x_1665_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1660_ = stack[0].m_obj;
lean_object* v_a_1661_ = stack[1].m_obj;
lean_object* v_a_1662_ = stack[2].m_obj;
lean_object* v_res_1677_;
v_res_1677_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1660_, v_a_1661_, v_a_1662_);
stack->m_obj
 = v_res_1677_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1678_, v_a_1679_, v_a_1680_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
return v_res_1682_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(lean_object* v_c_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1683_, v_a_1684_, v_a_1692_);
return v___x_1695_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1683_ = stack[0].m_obj;
lean_object* v_a_1684_ = stack[1].m_obj;
lean_object* v_a_1685_ = stack[2].m_obj;
lean_object* v_a_1686_ = stack[3].m_obj;
lean_object* v_a_1687_ = stack[4].m_obj;
lean_object* v_a_1688_ = stack[5].m_obj;
lean_object* v_a_1689_ = stack[6].m_obj;
lean_object* v_a_1690_ = stack[7].m_obj;
lean_object* v_a_1691_ = stack[8].m_obj;
lean_object* v_a_1692_ = stack[9].m_obj;
lean_object* v_a_1693_ = stack[10].m_obj;
lean_object* v_res_1696_;
v_res_1696_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(v_c_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_);
stack->m_obj
 = v_res_1696_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___boxed(lean_object* v_c_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(v_c_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
lean_dec_ref(v_a_1704_);
lean_dec(v_a_1703_);
lean_dec_ref(v_a_1702_);
lean_dec(v_a_1701_);
lean_dec_ref(v_a_1700_);
lean_dec(v_a_1699_);
lean_dec(v_a_1698_);
return v_res_1709_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1710_ = stack[0].m_obj;
lean_object* v_a_1711_ = stack[1].m_obj;
lean_object* v_a_1712_ = stack[2].m_obj;
lean_object* v_a_1713_ = stack[3].m_obj;
lean_object* v_a_1714_ = stack[4].m_obj;
lean_object* v_a_1715_ = stack[5].m_obj;
lean_object* v_a_1716_ = stack[6].m_obj;
lean_object* v_a_1717_ = stack[7].m_obj;
lean_object* v_a_1718_ = stack[8].m_obj;
lean_object* v_a_1719_ = stack[9].m_obj;
lean_object* v_a_1720_ = stack[10].m_obj;
lean_object* v_res_1722_;
v_res_1722_ = lean_grind_cutsat_assert_le(v_c_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_);
stack->m_obj
 = v_res_1722_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert___boxed(lean_object* v_c_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_00___x40___internal___hyg_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = lean_grind_cutsat_assert_le(v_c_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
return v_res_1735_;
}
}
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(lean_object* v_c_1736_){
_start:
{
lean_object* v_p_1737_; 
v_p_1737_ = lean_ctor_get(v_c_1736_, 0);
if (lean_obj_tag(v_p_1737_) == 0)
{
lean_object* v_k_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; 
v_k_1738_ = lean_ctor_get(v_p_1737_, 0);
v___x_1739_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1740_ = lean_int_dec_le(v_k_1738_, v___x_1739_);
return v___x_1740_;
}
else
{
uint8_t v___x_1741_; 
v___x_1741_ = 0;
return v___x_1741_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1736_ = stack[0].m_obj;
uint8_t v_res_1742_;
v_res_1742_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_c_1736_);
stack->m_num = v_res_1742_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial___boxed(lean_object* v_c_1743_){
_start:
{
uint8_t v_res_1744_; lean_object* v_r_1745_; 
v_res_1744_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_c_1743_);
lean_dec_ref(v_c_1743_);
v_r_1745_ = lean_box(v_res_1744_);
return v_r_1745_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0));
v___x_1748_ = l_Lean_stringToMessageData(v___x_1747_);
return v___x_1748_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(lean_object* v_c_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v_p_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1770_; 
v_p_1753_ = lean_ctor_get(v_c_1749_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v_c_1749_);
if (v_isSharedCheck_1770_ == 0)
{
lean_object* v_unused_1771_; 
v_unused_1771_ = lean_ctor_get(v_c_1749_, 1);
lean_dec(v_unused_1771_);
v___x_1755_ = v_c_1749_;
v_isShared_1756_ = v_isSharedCheck_1770_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_p_1753_);
lean_dec(v_c_1749_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1770_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1753_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1769_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1769_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1769_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1762_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1);
if (v_isShared_1756_ == 0)
{
lean_ctor_set_tag(v___x_1755_, 7);
lean_ctor_set(v___x_1755_, 1, v___x_1762_);
lean_ctor_set(v___x_1755_, 0, v_a_1758_);
v___x_1764_ = v___x_1755_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1758_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1766_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1764_);
v___x_1766_ = v___x_1760_;
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
lean_del_object(v___x_1755_);
return v___x_1757_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1749_ = stack[0].m_obj;
lean_object* v_a_1750_ = stack[1].m_obj;
lean_object* v_a_1751_ = stack[2].m_obj;
lean_object* v_res_1772_;
v_res_1772_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1749_, v_a_1750_, v_a_1751_);
stack->m_obj
 = v_res_1772_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___boxed(lean_object* v_c_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1773_, v_a_1774_, v_a_1775_);
lean_dec_ref(v_a_1775_);
lean_dec(v_a_1774_);
return v_res_1777_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(lean_object* v_c_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1778_, v_a_1779_, v_a_1787_);
return v___x_1790_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1778_ = stack[0].m_obj;
lean_object* v_a_1779_ = stack[1].m_obj;
lean_object* v_a_1780_ = stack[2].m_obj;
lean_object* v_a_1781_ = stack[3].m_obj;
lean_object* v_a_1782_ = stack[4].m_obj;
lean_object* v_a_1783_ = stack[5].m_obj;
lean_object* v_a_1784_ = stack[6].m_obj;
lean_object* v_a_1785_ = stack[7].m_obj;
lean_object* v_a_1786_ = stack[8].m_obj;
lean_object* v_a_1787_ = stack[9].m_obj;
lean_object* v_a_1788_ = stack[10].m_obj;
lean_object* v_res_1791_;
v_res_1791_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(v_c_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
stack->m_obj
 = v_res_1791_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___boxed(lean_object* v_c_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(v_c_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
lean_dec(v_a_1802_);
lean_dec_ref(v_a_1801_);
lean_dec(v_a_1800_);
lean_dec_ref(v_a_1799_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec(v_a_1793_);
return v_res_1804_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(lean_object* v_c_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v_p_1809_; lean_object* v___x_1810_; 
v_p_1809_ = lean_ctor_get(v_c_1805_, 0);
lean_inc_ref(v_p_1809_);
lean_dec_ref(v_c_1805_);
v___x_1810_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1809_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1820_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1820_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1820_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1815_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1816_ = l_Lean_mkIntLE(v_a_1811_, v___x_1815_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1816_);
v___x_1818_ = v___x_1813_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
else
{
return v___x_1810_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1805_ = stack[0].m_obj;
lean_object* v_a_1806_ = stack[1].m_obj;
lean_object* v_a_1807_ = stack[2].m_obj;
lean_object* v_res_1821_;
v_res_1821_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1805_, v_a_1806_, v_a_1807_);
stack->m_obj
 = v_res_1821_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1822_, v_a_1823_, v_a_1824_);
lean_dec_ref(v_a_1824_);
lean_dec(v_a_1823_);
return v_res_1826_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(lean_object* v_c_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1827_, v_a_1828_, v_a_1836_);
return v___x_1839_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1827_ = stack[0].m_obj;
lean_object* v_a_1828_ = stack[1].m_obj;
lean_object* v_a_1829_ = stack[2].m_obj;
lean_object* v_a_1830_ = stack[3].m_obj;
lean_object* v_a_1831_ = stack[4].m_obj;
lean_object* v_a_1832_ = stack[5].m_obj;
lean_object* v_a_1833_ = stack[6].m_obj;
lean_object* v_a_1834_ = stack[7].m_obj;
lean_object* v_a_1835_ = stack[8].m_obj;
lean_object* v_a_1836_ = stack[9].m_obj;
lean_object* v_a_1837_ = stack[10].m_obj;
lean_object* v_res_1840_;
v_res_1840_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(v_c_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
stack->m_obj
 = v_res_1840_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___boxed(lean_object* v_c_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(v_c_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
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
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(lean_object* v_c_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1854_, v_a_1855_, v_a_1858_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1854_ = stack[0].m_obj;
lean_object* v_a_1855_ = stack[1].m_obj;
lean_object* v_a_1856_ = stack[2].m_obj;
lean_object* v_a_1857_ = stack[3].m_obj;
lean_object* v_a_1858_ = stack[4].m_obj;
lean_object* v_a_1859_ = stack[5].m_obj;
lean_object* v_res_1875_;
v_res_1875_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
stack->m_obj
 = v_res_1875_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
lean_dec(v_a_1877_);
return v_res_1883_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(lean_object* v_00_u03b1_1884_, lean_object* v_c_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1885_, v_a_1886_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
return v___x_1897_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1885_ = stack[1].m_obj;
lean_object* v_a_1886_ = stack[2].m_obj;
lean_object* v_a_1887_ = stack[3].m_obj;
lean_object* v_a_1888_ = stack[4].m_obj;
lean_object* v_a_1889_ = stack[5].m_obj;
lean_object* v_a_1890_ = stack[6].m_obj;
lean_object* v_a_1891_ = stack[7].m_obj;
lean_object* v_a_1892_ = stack[8].m_obj;
lean_object* v_a_1893_ = stack[9].m_obj;
lean_object* v_a_1894_ = stack[10].m_obj;
lean_object* v_a_1895_ = stack[11].m_obj;
lean_object* v_res_1898_;
v_res_1898_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(lean_box(0), v_c_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
stack->m_obj
 = v_res_1898_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1899_, lean_object* v_c_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(v_00_u03b1_1899_, v_c_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
lean_dec(v_a_1910_);
lean_dec_ref(v_a_1909_);
lean_dec(v_a_1908_);
lean_dec_ref(v_a_1907_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec(v_a_1901_);
return v_res_1912_;
}
}
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(lean_object* v_c_1913_){
_start:
{
lean_object* v_p_1914_; 
v_p_1914_ = lean_ctor_get(v_c_1913_, 0);
if (lean_obj_tag(v_p_1914_) == 0)
{
lean_object* v_k_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v_k_1915_ = lean_ctor_get(v_p_1914_, 0);
v___x_1916_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1917_ = lean_int_dec_eq(v_k_1915_, v___x_1916_);
return v___x_1917_;
}
else
{
uint8_t v___x_1918_; 
v___x_1918_ = 0;
return v___x_1918_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1913_ = stack[0].m_obj;
uint8_t v_res_1919_;
v_res_1919_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(v_c_1913_);
stack->m_num = v_res_1919_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial___boxed(lean_object* v_c_1920_){
_start:
{
uint8_t v_res_1921_; lean_object* v_r_1922_; 
v_res_1921_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(v_c_1920_);
lean_dec_ref(v_c_1920_);
v_r_1922_ = lean_box(v_res_1921_);
return v_r_1922_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0));
v___x_1925_ = l_Lean_stringToMessageData(v___x_1924_);
return v___x_1925_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object* v_c_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_){
_start:
{
lean_object* v_p_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1947_; 
v_p_1930_ = lean_ctor_get(v_c_1926_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_c_1926_);
if (v_isSharedCheck_1947_ == 0)
{
lean_object* v_unused_1948_; 
v_unused_1948_ = lean_ctor_get(v_c_1926_, 1);
lean_dec(v_unused_1948_);
v___x_1932_ = v_c_1926_;
v_isShared_1933_ = v_isSharedCheck_1947_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_p_1930_);
lean_dec(v_c_1926_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1947_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1930_, v_a_1927_, v_a_1928_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1946_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1946_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1946_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1939_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1);
if (v_isShared_1933_ == 0)
{
lean_ctor_set_tag(v___x_1932_, 7);
lean_ctor_set(v___x_1932_, 1, v___x_1939_);
lean_ctor_set(v___x_1932_, 0, v_a_1935_);
v___x_1941_ = v___x_1932_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1935_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1943_; 
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v___x_1941_);
v___x_1943_ = v___x_1937_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1941_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
else
{
lean_del_object(v___x_1932_);
return v___x_1934_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1926_ = stack[0].m_obj;
lean_object* v_a_1927_ = stack[1].m_obj;
lean_object* v_a_1928_ = stack[2].m_obj;
lean_object* v_res_1949_;
v_res_1949_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1926_, v_a_1927_, v_a_1928_);
stack->m_obj
 = v_res_1949_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___boxed(lean_object* v_c_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1950_, v_a_1951_, v_a_1952_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
return v_res_1954_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(lean_object* v_c_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1955_, v_a_1956_, v_a_1964_);
return v___x_1967_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1955_ = stack[0].m_obj;
lean_object* v_a_1956_ = stack[1].m_obj;
lean_object* v_a_1957_ = stack[2].m_obj;
lean_object* v_a_1958_ = stack[3].m_obj;
lean_object* v_a_1959_ = stack[4].m_obj;
lean_object* v_a_1960_ = stack[5].m_obj;
lean_object* v_a_1961_ = stack[6].m_obj;
lean_object* v_a_1962_ = stack[7].m_obj;
lean_object* v_a_1963_ = stack[8].m_obj;
lean_object* v_a_1964_ = stack[9].m_obj;
lean_object* v_a_1965_ = stack[10].m_obj;
lean_object* v_res_1968_;
v_res_1968_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(v_c_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
stack->m_obj
 = v_res_1968_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___boxed(lean_object* v_c_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(v_c_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec(v_a_1970_);
return v_res_1981_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(lean_object* v_c_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v_p_1986_; lean_object* v___x_1987_; 
v_p_1986_ = lean_ctor_get(v_c_1982_, 0);
lean_inc_ref(v_p_1986_);
lean_dec_ref(v_c_1982_);
v___x_1987_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1986_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1997_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_1997_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1997_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1992_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1993_ = l_Lean_mkIntEq(v_a_1988_, v___x_1992_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1993_);
v___x_1995_ = v___x_1990_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
else
{
return v___x_1987_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1982_ = stack[0].m_obj;
lean_object* v_a_1983_ = stack[1].m_obj;
lean_object* v_a_1984_ = stack[2].m_obj;
lean_object* v_res_1998_;
v_res_1998_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1982_, v_a_1983_, v_a_1984_);
stack->m_obj
 = v_res_1998_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1999_, v_a_2000_, v_a_2001_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
return v_res_2003_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(lean_object* v_c_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_2004_, v_a_2005_, v_a_2013_);
return v___x_2016_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2004_ = stack[0].m_obj;
lean_object* v_a_2005_ = stack[1].m_obj;
lean_object* v_a_2006_ = stack[2].m_obj;
lean_object* v_a_2007_ = stack[3].m_obj;
lean_object* v_a_2008_ = stack[4].m_obj;
lean_object* v_a_2009_ = stack[5].m_obj;
lean_object* v_a_2010_ = stack[6].m_obj;
lean_object* v_a_2011_ = stack[7].m_obj;
lean_object* v_a_2012_ = stack[8].m_obj;
lean_object* v_a_2013_ = stack[9].m_obj;
lean_object* v_a_2014_ = stack[10].m_obj;
lean_object* v_res_2017_;
v_res_2017_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(v_c_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
stack->m_obj
 = v_res_2017_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___boxed(lean_object* v_c_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(v_c_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
lean_dec(v_a_2028_);
lean_dec_ref(v_a_2027_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec(v_a_2019_);
return v_res_2030_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(lean_object* v_c_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_2031_, v_a_2032_, v_a_2035_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v___x_2040_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_2041_ = l_Lean_indentD(v_a_2039_);
v___x_2042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2040_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2042_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
return v___x_2043_;
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
v_a_2044_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2038_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2038_);
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
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2031_ = stack[0].m_obj;
lean_object* v_a_2032_ = stack[1].m_obj;
lean_object* v_a_2033_ = stack[2].m_obj;
lean_object* v_a_2034_ = stack[3].m_obj;
lean_object* v_a_2035_ = stack[4].m_obj;
lean_object* v_a_2036_ = stack[5].m_obj;
lean_object* v_res_2052_;
v_res_2052_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
stack->m_obj
 = v_res_2052_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
lean_dec(v_a_2058_);
lean_dec_ref(v_a_2057_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
return v_res_2060_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(lean_object* v_00_u03b1_2061_, lean_object* v_c_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_2062_, v_a_2063_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
return v___x_2074_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2062_ = stack[1].m_obj;
lean_object* v_a_2063_ = stack[2].m_obj;
lean_object* v_a_2064_ = stack[3].m_obj;
lean_object* v_a_2065_ = stack[4].m_obj;
lean_object* v_a_2066_ = stack[5].m_obj;
lean_object* v_a_2067_ = stack[6].m_obj;
lean_object* v_a_2068_ = stack[7].m_obj;
lean_object* v_a_2069_ = stack[8].m_obj;
lean_object* v_a_2070_ = stack[9].m_obj;
lean_object* v_a_2071_ = stack[10].m_obj;
lean_object* v_a_2072_ = stack[11].m_obj;
lean_object* v_res_2075_;
v_res_2075_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(lean_box(0), v_c_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
stack->m_obj
 = v_res_2075_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_2076_, lean_object* v_c_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(v_00_u03b1_2076_, v_c_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
lean_dec(v_a_2087_);
lean_dec_ref(v_a_2086_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec(v_a_2078_);
return v_res_2089_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(lean_object* v_x_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2091_, v_a_2092_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2111_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2111_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2111_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v_occurs_2099_; lean_object* v_size_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v_occurs_2099_ = lean_ctor_get(v_a_2095_, 11);
lean_inc_ref(v_occurs_2099_);
lean_dec(v_a_2095_);
v_size_2100_ = lean_ctor_get(v_occurs_2099_, 2);
v___x_2101_ = lean_box(1);
v___x_2102_ = lean_nat_dec_lt(v_x_2090_, v_size_2100_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2105_; 
lean_dec_ref(v_occurs_2099_);
v___x_2103_ = l_outOfBounds___redArg(v___x_2101_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2103_);
v___x_2105_ = v___x_2097_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2107_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2101_, v_occurs_2099_, v_x_2090_);
lean_dec_ref(v_occurs_2099_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2107_);
v___x_2109_ = v___x_2097_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
v_a_2112_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2094_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2094_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2090_ = stack[0].m_obj;
lean_object* v_a_2091_ = stack[1].m_obj;
lean_object* v_a_2092_ = stack[2].m_obj;
lean_object* v_res_2120_;
v_res_2120_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2090_, v_a_2091_, v_a_2092_);
stack->m_obj
 = v_res_2120_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg___boxed(lean_object* v_x_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2121_, v_a_2122_, v_a_2123_);
lean_dec_ref(v_a_2123_);
lean_dec(v_a_2122_);
lean_dec(v_x_2121_);
return v_res_2125_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(lean_object* v_x_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2126_, v_a_2127_, v_a_2135_);
return v___x_2138_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2126_ = stack[0].m_obj;
lean_object* v_a_2127_ = stack[1].m_obj;
lean_object* v_a_2128_ = stack[2].m_obj;
lean_object* v_a_2129_ = stack[3].m_obj;
lean_object* v_a_2130_ = stack[4].m_obj;
lean_object* v_a_2131_ = stack[5].m_obj;
lean_object* v_a_2132_ = stack[6].m_obj;
lean_object* v_a_2133_ = stack[7].m_obj;
lean_object* v_a_2134_ = stack[8].m_obj;
lean_object* v_a_2135_ = stack[9].m_obj;
lean_object* v_a_2136_ = stack[10].m_obj;
lean_object* v_res_2139_;
v_res_2139_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(v_x_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
stack->m_obj
 = v_res_2139_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___boxed(lean_object* v_x_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(v_x_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
lean_dec(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec(v_x_2140_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(lean_object* v_k_2153_, lean_object* v_v_2154_, lean_object* v_t_2155_){
_start:
{
if (lean_obj_tag(v_t_2155_) == 0)
{
lean_object* v_size_2156_; lean_object* v_k_2157_; lean_object* v_v_2158_; lean_object* v_l_2159_; lean_object* v_r_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2441_; 
v_size_2156_ = lean_ctor_get(v_t_2155_, 0);
v_k_2157_ = lean_ctor_get(v_t_2155_, 1);
v_v_2158_ = lean_ctor_get(v_t_2155_, 2);
v_l_2159_ = lean_ctor_get(v_t_2155_, 3);
v_r_2160_ = lean_ctor_get(v_t_2155_, 4);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_t_2155_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2162_ = v_t_2155_;
v_isShared_2163_ = v_isSharedCheck_2441_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_r_2160_);
lean_inc(v_l_2159_);
lean_inc(v_v_2158_);
lean_inc(v_k_2157_);
lean_inc(v_size_2156_);
lean_dec(v_t_2155_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2441_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
uint8_t v___x_2164_; 
v___x_2164_ = lean_nat_dec_lt(v_k_2153_, v_k_2157_);
if (v___x_2164_ == 0)
{
uint8_t v___x_2165_; 
v___x_2165_ = lean_nat_dec_eq(v_k_2153_, v_k_2157_);
if (v___x_2165_ == 0)
{
lean_object* v_impl_2166_; lean_object* v___x_2167_; 
lean_dec(v_size_2156_);
v_impl_2166_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2153_, v_v_2154_, v_r_2160_);
v___x_2167_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2159_) == 0)
{
lean_object* v_size_2168_; lean_object* v_size_2169_; lean_object* v_k_2170_; lean_object* v_v_2171_; lean_object* v_l_2172_; lean_object* v_r_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v_size_2168_ = lean_ctor_get(v_l_2159_, 0);
v_size_2169_ = lean_ctor_get(v_impl_2166_, 0);
v_k_2170_ = lean_ctor_get(v_impl_2166_, 1);
v_v_2171_ = lean_ctor_get(v_impl_2166_, 2);
v_l_2172_ = lean_ctor_get(v_impl_2166_, 3);
lean_inc(v_l_2172_);
v_r_2173_ = lean_ctor_get(v_impl_2166_, 4);
v___x_2174_ = lean_unsigned_to_nat(3u);
v___x_2175_ = lean_nat_mul(v___x_2174_, v_size_2168_);
v___x_2176_ = lean_nat_dec_lt(v___x_2175_, v_size_2169_);
lean_dec(v___x_2175_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2180_; 
lean_dec(v_l_2172_);
v___x_2177_ = lean_nat_add(v___x_2167_, v_size_2168_);
v___x_2178_ = lean_nat_add(v___x_2177_, v_size_2169_);
lean_dec(v___x_2177_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 4, v_impl_2166_);
lean_ctor_set(v___x_2162_, 0, v___x_2178_);
v___x_2180_ = v___x_2162_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_k_2157_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v_v_2158_);
lean_ctor_set(v_reuseFailAlloc_2181_, 3, v_l_2159_);
lean_ctor_set(v_reuseFailAlloc_2181_, 4, v_impl_2166_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
else
{
lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2245_; 
lean_inc(v_r_2173_);
lean_inc(v_v_2171_);
lean_inc(v_k_2170_);
lean_inc(v_size_2169_);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_impl_2166_);
if (v_isSharedCheck_2245_ == 0)
{
lean_object* v_unused_2246_; lean_object* v_unused_2247_; lean_object* v_unused_2248_; lean_object* v_unused_2249_; lean_object* v_unused_2250_; 
v_unused_2246_ = lean_ctor_get(v_impl_2166_, 4);
lean_dec(v_unused_2246_);
v_unused_2247_ = lean_ctor_get(v_impl_2166_, 3);
lean_dec(v_unused_2247_);
v_unused_2248_ = lean_ctor_get(v_impl_2166_, 2);
lean_dec(v_unused_2248_);
v_unused_2249_ = lean_ctor_get(v_impl_2166_, 1);
lean_dec(v_unused_2249_);
v_unused_2250_ = lean_ctor_get(v_impl_2166_, 0);
lean_dec(v_unused_2250_);
v___x_2183_ = v_impl_2166_;
v_isShared_2184_ = v_isSharedCheck_2245_;
goto v_resetjp_2182_;
}
else
{
lean_dec(v_impl_2166_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2245_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v_size_2185_; lean_object* v_k_2186_; lean_object* v_v_2187_; lean_object* v_l_2188_; lean_object* v_r_2189_; lean_object* v_size_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v_size_2185_ = lean_ctor_get(v_l_2172_, 0);
v_k_2186_ = lean_ctor_get(v_l_2172_, 1);
v_v_2187_ = lean_ctor_get(v_l_2172_, 2);
v_l_2188_ = lean_ctor_get(v_l_2172_, 3);
v_r_2189_ = lean_ctor_get(v_l_2172_, 4);
v_size_2190_ = lean_ctor_get(v_r_2173_, 0);
v___x_2191_ = lean_unsigned_to_nat(2u);
v___x_2192_ = lean_nat_mul(v___x_2191_, v_size_2190_);
v___x_2193_ = lean_nat_dec_lt(v_size_2185_, v___x_2192_);
lean_dec(v___x_2192_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2221_; 
lean_inc(v_r_2189_);
lean_inc(v_l_2188_);
lean_inc(v_v_2187_);
lean_inc(v_k_2186_);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_l_2172_);
if (v_isSharedCheck_2221_ == 0)
{
lean_object* v_unused_2222_; lean_object* v_unused_2223_; lean_object* v_unused_2224_; lean_object* v_unused_2225_; lean_object* v_unused_2226_; 
v_unused_2222_ = lean_ctor_get(v_l_2172_, 4);
lean_dec(v_unused_2222_);
v_unused_2223_ = lean_ctor_get(v_l_2172_, 3);
lean_dec(v_unused_2223_);
v_unused_2224_ = lean_ctor_get(v_l_2172_, 2);
lean_dec(v_unused_2224_);
v_unused_2225_ = lean_ctor_get(v_l_2172_, 1);
lean_dec(v_unused_2225_);
v_unused_2226_ = lean_ctor_get(v_l_2172_, 0);
lean_dec(v_unused_2226_);
v___x_2195_ = v_l_2172_;
v_isShared_2196_ = v_isSharedCheck_2221_;
goto v_resetjp_2194_;
}
else
{
lean_dec(v_l_2172_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2221_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2211_; 
v___x_2197_ = lean_nat_add(v___x_2167_, v_size_2168_);
v___x_2198_ = lean_nat_add(v___x_2197_, v_size_2169_);
lean_dec(v_size_2169_);
if (lean_obj_tag(v_l_2188_) == 0)
{
lean_object* v_size_2219_; 
v_size_2219_ = lean_ctor_get(v_l_2188_, 0);
lean_inc(v_size_2219_);
v___y_2211_ = v_size_2219_;
goto v___jp_2210_;
}
else
{
lean_object* v___x_2220_; 
v___x_2220_ = lean_unsigned_to_nat(0u);
v___y_2211_ = v___x_2220_;
goto v___jp_2210_;
}
v___jp_2199_:
{
lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2203_ = lean_nat_add(v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec(v___y_2201_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 4, v_r_2173_);
lean_ctor_set(v___x_2195_, 3, v_r_2189_);
lean_ctor_set(v___x_2195_, 2, v_v_2171_);
lean_ctor_set(v___x_2195_, 1, v_k_2170_);
lean_ctor_set(v___x_2195_, 0, v___x_2203_);
v___x_2205_ = v___x_2195_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_k_2170_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_v_2171_);
lean_ctor_set(v_reuseFailAlloc_2209_, 3, v_r_2189_);
lean_ctor_set(v_reuseFailAlloc_2209_, 4, v_r_2173_);
v___x_2205_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
lean_object* v___x_2207_; 
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 4, v___x_2205_);
lean_ctor_set(v___x_2183_, 3, v___y_2200_);
lean_ctor_set(v___x_2183_, 2, v_v_2187_);
lean_ctor_set(v___x_2183_, 1, v_k_2186_);
lean_ctor_set(v___x_2183_, 0, v___x_2198_);
v___x_2207_ = v___x_2183_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_k_2186_);
lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_v_2187_);
lean_ctor_set(v_reuseFailAlloc_2208_, 3, v___y_2200_);
lean_ctor_set(v_reuseFailAlloc_2208_, 4, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
v___jp_2210_:
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2212_ = lean_nat_add(v___x_2197_, v___y_2211_);
lean_dec(v___y_2211_);
lean_dec(v___x_2197_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 4, v_l_2188_);
lean_ctor_set(v___x_2162_, 0, v___x_2212_);
v___x_2214_ = v___x_2162_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v_k_2157_);
lean_ctor_set(v_reuseFailAlloc_2218_, 2, v_v_2158_);
lean_ctor_set(v_reuseFailAlloc_2218_, 3, v_l_2159_);
lean_ctor_set(v_reuseFailAlloc_2218_, 4, v_l_2188_);
v___x_2214_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; 
v___x_2215_ = lean_nat_add(v___x_2167_, v_size_2190_);
if (lean_obj_tag(v_r_2189_) == 0)
{
lean_object* v_size_2216_; 
v_size_2216_ = lean_ctor_get(v_r_2189_, 0);
lean_inc(v_size_2216_);
v___y_2200_ = v___x_2214_;
v___y_2201_ = v___x_2215_;
v___y_2202_ = v_size_2216_;
goto v___jp_2199_;
}
else
{
lean_object* v___x_2217_; 
v___x_2217_ = lean_unsigned_to_nat(0u);
v___y_2200_ = v___x_2214_;
v___y_2201_ = v___x_2215_;
v___y_2202_ = v___x_2217_;
goto v___jp_2199_;
}
}
}
}
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2231_; 
lean_del_object(v___x_2162_);
v___x_2227_ = lean_nat_add(v___x_2167_, v_size_2168_);
v___x_2228_ = lean_nat_add(v___x_2227_, v_size_2169_);
lean_dec(v_size_2169_);
v___x_2229_ = lean_nat_add(v___x_2227_, v_size_2185_);
lean_dec(v___x_2227_);
lean_inc_ref(v_l_2159_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 4, v_l_2172_);
lean_ctor_set(v___x_2183_, 3, v_l_2159_);
lean_ctor_set(v___x_2183_, 2, v_v_2158_);
lean_ctor_set(v___x_2183_, 1, v_k_2157_);
lean_ctor_set(v___x_2183_, 0, v___x_2229_);
v___x_2231_ = v___x_2183_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_k_2157_);
lean_ctor_set(v_reuseFailAlloc_2244_, 2, v_v_2158_);
lean_ctor_set(v_reuseFailAlloc_2244_, 3, v_l_2159_);
lean_ctor_set(v_reuseFailAlloc_2244_, 4, v_l_2172_);
v___x_2231_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
v_isSharedCheck_2238_ = !lean_is_exclusive(v_l_2159_);
if (v_isSharedCheck_2238_ == 0)
{
lean_object* v_unused_2239_; lean_object* v_unused_2240_; lean_object* v_unused_2241_; lean_object* v_unused_2242_; lean_object* v_unused_2243_; 
v_unused_2239_ = lean_ctor_get(v_l_2159_, 4);
lean_dec(v_unused_2239_);
v_unused_2240_ = lean_ctor_get(v_l_2159_, 3);
lean_dec(v_unused_2240_);
v_unused_2241_ = lean_ctor_get(v_l_2159_, 2);
lean_dec(v_unused_2241_);
v_unused_2242_ = lean_ctor_get(v_l_2159_, 1);
lean_dec(v_unused_2242_);
v_unused_2243_ = lean_ctor_get(v_l_2159_, 0);
lean_dec(v_unused_2243_);
v___x_2233_ = v_l_2159_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_dec(v_l_2159_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 4, v_r_2173_);
lean_ctor_set(v___x_2233_, 3, v___x_2231_);
lean_ctor_set(v___x_2233_, 2, v_v_2171_);
lean_ctor_set(v___x_2233_, 1, v_k_2170_);
lean_ctor_set(v___x_2233_, 0, v___x_2228_);
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_k_2170_);
lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_v_2171_);
lean_ctor_set(v_reuseFailAlloc_2237_, 3, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2237_, 4, v_r_2173_);
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
}
}
}
else
{
lean_object* v_l_2251_; 
v_l_2251_ = lean_ctor_get(v_impl_2166_, 3);
lean_inc(v_l_2251_);
if (lean_obj_tag(v_l_2251_) == 0)
{
lean_object* v_r_2252_; lean_object* v_k_2253_; lean_object* v_v_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2277_; 
v_r_2252_ = lean_ctor_get(v_impl_2166_, 4);
v_k_2253_ = lean_ctor_get(v_impl_2166_, 1);
v_v_2254_ = lean_ctor_get(v_impl_2166_, 2);
v_isSharedCheck_2277_ = !lean_is_exclusive(v_impl_2166_);
if (v_isSharedCheck_2277_ == 0)
{
lean_object* v_unused_2278_; lean_object* v_unused_2279_; 
v_unused_2278_ = lean_ctor_get(v_impl_2166_, 3);
lean_dec(v_unused_2278_);
v_unused_2279_ = lean_ctor_get(v_impl_2166_, 0);
lean_dec(v_unused_2279_);
v___x_2256_ = v_impl_2166_;
v_isShared_2257_ = v_isSharedCheck_2277_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_r_2252_);
lean_inc(v_v_2254_);
lean_inc(v_k_2253_);
lean_dec(v_impl_2166_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2277_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v_k_2258_; lean_object* v_v_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2273_; 
v_k_2258_ = lean_ctor_get(v_l_2251_, 1);
v_v_2259_ = lean_ctor_get(v_l_2251_, 2);
v_isSharedCheck_2273_ = !lean_is_exclusive(v_l_2251_);
if (v_isSharedCheck_2273_ == 0)
{
lean_object* v_unused_2274_; lean_object* v_unused_2275_; lean_object* v_unused_2276_; 
v_unused_2274_ = lean_ctor_get(v_l_2251_, 4);
lean_dec(v_unused_2274_);
v_unused_2275_ = lean_ctor_get(v_l_2251_, 3);
lean_dec(v_unused_2275_);
v_unused_2276_ = lean_ctor_get(v_l_2251_, 0);
lean_dec(v_unused_2276_);
v___x_2261_ = v_l_2251_;
v_isShared_2262_ = v_isSharedCheck_2273_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_v_2259_);
lean_inc(v_k_2258_);
lean_dec(v_l_2251_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2273_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2263_; lean_object* v___x_2265_; 
v___x_2263_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2252_, 2);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v_r_2252_);
lean_ctor_set(v___x_2261_, 3, v_r_2252_);
lean_ctor_set(v___x_2261_, 2, v_v_2158_);
lean_ctor_set(v___x_2261_, 1, v_k_2157_);
lean_ctor_set(v___x_2261_, 0, v___x_2167_);
v___x_2265_ = v___x_2261_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v_k_2157_);
lean_ctor_set(v_reuseFailAlloc_2272_, 2, v_v_2158_);
lean_ctor_set(v_reuseFailAlloc_2272_, 3, v_r_2252_);
lean_ctor_set(v_reuseFailAlloc_2272_, 4, v_r_2252_);
v___x_2265_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
lean_object* v___x_2267_; 
lean_inc(v_r_2252_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 3, v_r_2252_);
lean_ctor_set(v___x_2256_, 0, v___x_2167_);
v___x_2267_ = v___x_2256_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_k_2253_);
lean_ctor_set(v_reuseFailAlloc_2271_, 2, v_v_2254_);
lean_ctor_set(v_reuseFailAlloc_2271_, 3, v_r_2252_);
lean_ctor_set(v_reuseFailAlloc_2271_, 4, v_r_2252_);
v___x_2267_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
lean_object* v___x_2269_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 4, v___x_2267_);
lean_ctor_set(v___x_2162_, 3, v___x_2265_);
lean_ctor_set(v___x_2162_, 2, v_v_2259_);
lean_ctor_set(v___x_2162_, 1, v_k_2258_);
lean_ctor_set(v___x_2162_, 0, v___x_2263_);
v___x_2269_ = v___x_2162_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2263_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_k_2258_);
lean_ctor_set(v_reuseFailAlloc_2270_, 2, v_v_2259_);
lean_ctor_set(v_reuseFailAlloc_2270_, 3, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2270_, 4, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
}
}
else
{
lean_object* v_r_2280_; 
v_r_2280_ = lean_ctor_get(v_impl_2166_, 4);
lean_inc(v_r_2280_);
if (lean_obj_tag(v_r_2280_) == 0)
{
lean_object* v_k_2281_; lean_object* v_v_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2293_; 
v_k_2281_ = lean_ctor_get(v_impl_2166_, 1);
v_v_2282_ = lean_ctor_get(v_impl_2166_, 2);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_impl_2166_);
if (v_isSharedCheck_2293_ == 0)
{
lean_object* v_unused_2294_; lean_object* v_unused_2295_; lean_object* v_unused_2296_; 
v_unused_2294_ = lean_ctor_get(v_impl_2166_, 4);
lean_dec(v_unused_2294_);
v_unused_2295_ = lean_ctor_get(v_impl_2166_, 3);
lean_dec(v_unused_2295_);
v_unused_2296_ = lean_ctor_get(v_impl_2166_, 0);
lean_dec(v_unused_2296_);
v___x_2284_ = v_impl_2166_;
v_isShared_2285_ = v_isSharedCheck_2293_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_v_2282_);
lean_inc(v_k_2281_);
lean_dec(v_impl_2166_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2293_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2286_ = lean_unsigned_to_nat(3u);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 4, v_l_2251_);
lean_ctor_set(v___x_2284_, 2, v_v_2158_);
lean_ctor_set(v___x_2284_, 1, v_k_2157_);
lean_ctor_set(v___x_2284_, 0, v___x_2167_);
v___x_2288_ = v___x_2284_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v_k_2157_);
lean_ctor_set(v_reuseFailAlloc_2292_, 2, v_v_2158_);
lean_ctor_set(v_reuseFailAlloc_2292_, 3, v_l_2251_);
lean_ctor_set(v_reuseFailAlloc_2292_, 4, v_l_2251_);
v___x_2288_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2290_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 4, v_r_2280_);
lean_ctor_set(v___x_2162_, 3, v___x_2288_);
lean_ctor_set(v___x_2162_, 2, v_v_2282_);
lean_ctor_set(v___x_2162_, 1, v_k_2281_);
lean_ctor_set(v___x_2162_, 0, v___x_2286_);
v___x_2290_ = v___x_2162_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v_k_2281_);
lean_ctor_set(v_reuseFailAlloc_2291_, 2, v_v_2282_);
lean_ctor_set(v_reuseFailAlloc_2291_, 3, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2291_, 4, v_r_2280_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
else
{
lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2297_ = lean_unsigned_to_nat(2u);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 4, v_impl_2166_);
lean_ctor_set(v___x_2162_, 3, v_r_2280_);
lean_ctor_set(v___x_2162_, 0, v___x_2297_);
v___x_2299_ = v___x_2162_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_k_2157_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_v_2158_);
lean_ctor_set(v_reuseFailAlloc_2300_, 3, v_r_2280_);
lean_ctor_set(v_reuseFailAlloc_2300_, 4, v_impl_2166_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
else
{
lean_object* v___x_2302_; 
lean_dec(v_v_2158_);
lean_dec(v_k_2157_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 2, v_v_2154_);
lean_ctor_set(v___x_2162_, 1, v_k_2153_);
v___x_2302_ = v___x_2162_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_size_2156_);
lean_ctor_set(v_reuseFailAlloc_2303_, 1, v_k_2153_);
lean_ctor_set(v_reuseFailAlloc_2303_, 2, v_v_2154_);
lean_ctor_set(v_reuseFailAlloc_2303_, 3, v_l_2159_);
lean_ctor_set(v_reuseFailAlloc_2303_, 4, v_r_2160_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
else
{
lean_object* v_impl_2304_; lean_object* v___x_2305_; 
lean_dec(v_size_2156_);
v_impl_2304_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2153_, v_v_2154_, v_l_2159_);
v___x_2305_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2160_) == 0)
{
lean_object* v_size_2306_; lean_object* v_size_2307_; lean_object* v_k_2308_; lean_object* v_v_2309_; lean_object* v_l_2310_; lean_object* v_r_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v_size_2306_ = lean_ctor_get(v_r_2160_, 0);
v_size_2307_ = lean_ctor_get(v_impl_2304_, 0);
v_k_2308_ = lean_ctor_get(v_impl_2304_, 1);
v_v_2309_ = lean_ctor_get(v_impl_2304_, 2);
v_l_2310_ = lean_ctor_get(v_impl_2304_, 3);
v_r_2311_ = lean_ctor_get(v_impl_2304_, 4);
lean_inc(v_r_2311_);
v___x_2312_ = lean_unsigned_to_nat(3u);
v___x_2313_ = lean_nat_mul(v___x_2312_, v_size_2306_);
v___x_2314_ = lean_nat_dec_lt(v___x_2313_, v_size_2307_);
lean_dec(v___x_2313_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
lean_dec(v_r_2311_);
v___x_2315_ = lean_nat_add(v___x_2305_, v_size_2307_);
v___x_2316_ = lean_nat_add(v___x_2315_, v_size_2306_);
lean_dec(v___x_2315_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 3, v_impl_2304_);
lean_ctor_set(v___x_2162_, 0, v___x_2316_);
v___x_2318_ = v___x_2162_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_k_2157_);
lean_ctor_set(v_reuseFailAlloc_2319_, 2, v_v_2158_);
lean_ctor_set(v_reuseFailAlloc_2319_, 3, v_impl_2304_);
lean_ctor_set(v_reuseFailAlloc_2319_, 4, v_r_2160_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
else
{
lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2385_; 
lean_inc(v_l_2310_);
lean_inc(v_v_2309_);
lean_inc(v_k_2308_);
lean_inc(v_size_2307_);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_impl_2304_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; lean_object* v_unused_2387_; lean_object* v_unused_2388_; lean_object* v_unused_2389_; lean_object* v_unused_2390_; 
v_unused_2386_ = lean_ctor_get(v_impl_2304_, 4);
lean_dec(v_unused_2386_);
v_unused_2387_ = lean_ctor_get(v_impl_2304_, 3);
lean_dec(v_unused_2387_);
v_unused_2388_ = lean_ctor_get(v_impl_2304_, 2);
lean_dec(v_unused_2388_);
v_unused_2389_ = lean_ctor_get(v_impl_2304_, 1);
lean_dec(v_unused_2389_);
v_unused_2390_ = lean_ctor_get(v_impl_2304_, 0);
lean_dec(v_unused_2390_);
v___x_2321_ = v_impl_2304_;
v_isShared_2322_ = v_isSharedCheck_2385_;
goto v_resetjp_2320_;
}
else
{
lean_dec(v_impl_2304_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2385_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v_size_2323_; lean_object* v_size_2324_; lean_object* v_k_2325_; lean_object* v_v_2326_; lean_object* v_l_2327_; lean_object* v_r_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v_size_2323_ = lean_ctor_get(v_l_2310_, 0);
v_size_2324_ = lean_ctor_get(v_r_2311_, 0);
v_k_2325_ = lean_ctor_get(v_r_2311_, 1);
v_v_2326_ = lean_ctor_get(v_r_2311_, 2);
v_l_2327_ = lean_ctor_get(v_r_2311_, 3);
v_r_2328_ = lean_ctor_get(v_r_2311_, 4);
v___x_2329_ = lean_unsigned_to_nat(2u);
v___x_2330_ = lean_nat_mul(v___x_2329_, v_size_2323_);
v___x_2331_ = lean_nat_dec_lt(v_size_2324_, v___x_2330_);
lean_dec(v___x_2330_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2360_; 
lean_inc(v_r_2328_);
lean_inc(v_l_2327_);
lean_inc(v_v_2326_);
lean_inc(v_k_2325_);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_r_2311_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; lean_object* v_unused_2362_; lean_object* v_unused_2363_; lean_object* v_unused_2364_; lean_object* v_unused_2365_; 
v_unused_2361_ = lean_ctor_get(v_r_2311_, 4);
lean_dec(v_unused_2361_);
v_unused_2362_ = lean_ctor_get(v_r_2311_, 3);
lean_dec(v_unused_2362_);
v_unused_2363_ = lean_ctor_get(v_r_2311_, 2);
lean_dec(v_unused_2363_);
v_unused_2364_ = lean_ctor_get(v_r_2311_, 1);
lean_dec(v_unused_2364_);
v_unused_2365_ = lean_ctor_get(v_r_2311_, 0);
lean_dec(v_unused_2365_);
v___x_2333_ = v_r_2311_;
v_isShared_2334_ = v_isSharedCheck_2360_;
goto v_resetjp_2332_;
}
else
{
lean_dec(v_r_2311_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2360_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v___y_2340_; lean_object* v___x_2348_; lean_object* v___y_2350_; 
v___x_2335_ = lean_nat_add(v___x_2305_, v_size_2307_);
lean_dec(v_size_2307_);
v___x_2336_ = lean_nat_add(v___x_2335_, v_size_2306_);
lean_dec(v___x_2335_);
v___x_2348_ = lean_nat_add(v___x_2305_, v_size_2323_);
if (lean_obj_tag(v_l_2327_) == 0)
{
lean_object* v_size_2358_; 
v_size_2358_ = lean_ctor_get(v_l_2327_, 0);
lean_inc(v_size_2358_);
v___y_2350_ = v_size_2358_;
goto v___jp_2349_;
}
else
{
lean_object* v___x_2359_; 
v___x_2359_ = lean_unsigned_to_nat(0u);
v___y_2350_ = v___x_2359_;
goto v___jp_2349_;
}
v___jp_2337_:
{
lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2341_ = lean_nat_add(v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec(v___y_2339_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 4, v_r_2160_);
lean_ctor_set(v___x_2333_, 3, v_r_2328_);
lean_ctor_set(v___x_2333_, 2, v_v_2158_);
lean_ctor_set(v___x_2333_, 1, v_k_2157_);
lean_ctor_set(v___x_2333_, 0, v___x_2341_);
v___x_2343_ = v___x_2333_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_k_2157_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_v_2158_);
lean_ctor_set(v_reuseFailAlloc_2347_, 3, v_r_2328_);
lean_ctor_set(v_reuseFailAlloc_2347_, 4, v_r_2160_);
v___x_2343_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2345_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 4, v___x_2343_);
lean_ctor_set(v___x_2321_, 3, v___y_2338_);
lean_ctor_set(v___x_2321_, 2, v_v_2326_);
lean_ctor_set(v___x_2321_, 1, v_k_2325_);
lean_ctor_set(v___x_2321_, 0, v___x_2336_);
v___x_2345_ = v___x_2321_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2336_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_k_2325_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v_v_2326_);
lean_ctor_set(v_reuseFailAlloc_2346_, 3, v___y_2338_);
lean_ctor_set(v_reuseFailAlloc_2346_, 4, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
v___jp_2349_:
{
lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2351_ = lean_nat_add(v___x_2348_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec(v___x_2348_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 4, v_l_2327_);
lean_ctor_set(v___x_2162_, 3, v_l_2310_);
lean_ctor_set(v___x_2162_, 2, v_v_2309_);
lean_ctor_set(v___x_2162_, 1, v_k_2308_);
lean_ctor_set(v___x_2162_, 0, v___x_2351_);
v___x_2353_ = v___x_2162_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2351_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_k_2308_);
lean_ctor_set(v_reuseFailAlloc_2357_, 2, v_v_2309_);
lean_ctor_set(v_reuseFailAlloc_2357_, 3, v_l_2310_);
lean_ctor_set(v_reuseFailAlloc_2357_, 4, v_l_2327_);
v___x_2353_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2354_; 
v___x_2354_ = lean_nat_add(v___x_2305_, v_size_2306_);
if (lean_obj_tag(v_r_2328_) == 0)
{
lean_object* v_size_2355_; 
v_size_2355_ = lean_ctor_get(v_r_2328_, 0);
lean_inc(v_size_2355_);
v___y_2338_ = v___x_2353_;
v___y_2339_ = v___x_2354_;
v___y_2340_ = v_size_2355_;
goto v___jp_2337_;
}
else
{
lean_object* v___x_2356_; 
v___x_2356_ = lean_unsigned_to_nat(0u);
v___y_2338_ = v___x_2353_;
v___y_2339_ = v___x_2354_;
v___y_2340_ = v___x_2356_;
goto v___jp_2337_;
}
}
}
}
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2371_; 
lean_del_object(v___x_2162_);
v___x_2366_ = lean_nat_add(v___x_2305_, v_size_2307_);
lean_dec(v_size_2307_);
v___x_2367_ = lean_nat_add(v___x_2366_, v_size_2306_);
lean_dec(v___x_2366_);
v___x_2368_ = lean_nat_add(v___x_2305_, v_size_2306_);
v___x_2369_ = lean_nat_add(v___x_2368_, v_size_2324_);
lean_dec(v___x_2368_);
lean_inc_ref(v_r_2160_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 4, v_r_2160_);
lean_ctor_set(v___x_2321_, 3, v_r_2311_);
lean_ctor_set(v___x_2321_, 2, v_v_2158_);
lean_ctor_set(v___x_2321_, 1, v_k_2157_);
lean_ctor_set(v___x_2321_, 0, v___x_2369_);
v___x_2371_ = v___x_2321_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_k_2157_);
lean_ctor_set(v_reuseFailAlloc_2384_, 2, v_v_2158_);
lean_ctor_set(v_reuseFailAlloc_2384_, 3, v_r_2311_);
lean_ctor_set(v_reuseFailAlloc_2384_, 4, v_r_2160_);
v___x_2371_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
v_isSharedCheck_2378_ = !lean_is_exclusive(v_r_2160_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; lean_object* v_unused_2380_; lean_object* v_unused_2381_; lean_object* v_unused_2382_; lean_object* v_unused_2383_; 
v_unused_2379_ = lean_ctor_get(v_r_2160_, 4);
lean_dec(v_unused_2379_);
v_unused_2380_ = lean_ctor_get(v_r_2160_, 3);
lean_dec(v_unused_2380_);
v_unused_2381_ = lean_ctor_get(v_r_2160_, 2);
lean_dec(v_unused_2381_);
v_unused_2382_ = lean_ctor_get(v_r_2160_, 1);
lean_dec(v_unused_2382_);
v_unused_2383_ = lean_ctor_get(v_r_2160_, 0);
lean_dec(v_unused_2383_);
v___x_2373_ = v_r_2160_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_dec(v_r_2160_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 4, v___x_2371_);
lean_ctor_set(v___x_2373_, 3, v_l_2310_);
lean_ctor_set(v___x_2373_, 2, v_v_2309_);
lean_ctor_set(v___x_2373_, 1, v_k_2308_);
lean_ctor_set(v___x_2373_, 0, v___x_2367_);
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_k_2308_);
lean_ctor_set(v_reuseFailAlloc_2377_, 2, v_v_2309_);
lean_ctor_set(v_reuseFailAlloc_2377_, 3, v_l_2310_);
lean_ctor_set(v_reuseFailAlloc_2377_, 4, v___x_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2391_; 
v_l_2391_ = lean_ctor_get(v_impl_2304_, 3);
if (lean_obj_tag(v_l_2391_) == 0)
{
lean_object* v_r_2392_; lean_object* v_k_2393_; lean_object* v_v_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2405_; 
lean_inc_ref(v_l_2391_);
v_r_2392_ = lean_ctor_get(v_impl_2304_, 4);
v_k_2393_ = lean_ctor_get(v_impl_2304_, 1);
v_v_2394_ = lean_ctor_get(v_impl_2304_, 2);
v_isSharedCheck_2405_ = !lean_is_exclusive(v_impl_2304_);
if (v_isSharedCheck_2405_ == 0)
{
lean_object* v_unused_2406_; lean_object* v_unused_2407_; 
v_unused_2406_ = lean_ctor_get(v_impl_2304_, 3);
lean_dec(v_unused_2406_);
v_unused_2407_ = lean_ctor_get(v_impl_2304_, 0);
lean_dec(v_unused_2407_);
v___x_2396_ = v_impl_2304_;
v_isShared_2397_ = v_isSharedCheck_2405_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_r_2392_);
lean_inc(v_v_2394_);
lean_inc(v_k_2393_);
lean_dec(v_impl_2304_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2405_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___x_2398_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2392_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 3, v_r_2392_);
lean_ctor_set(v___x_2396_, 2, v_v_2158_);
lean_ctor_set(v___x_2396_, 1, v_k_2157_);
lean_ctor_set(v___x_2396_, 0, v___x_2305_);
v___x_2400_ = v___x_2396_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v_k_2157_);
lean_ctor_set(v_reuseFailAlloc_2404_, 2, v_v_2158_);
lean_ctor_set(v_reuseFailAlloc_2404_, 3, v_r_2392_);
lean_ctor_set(v_reuseFailAlloc_2404_, 4, v_r_2392_);
v___x_2400_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
lean_object* v___x_2402_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 4, v___x_2400_);
lean_ctor_set(v___x_2162_, 3, v_l_2391_);
lean_ctor_set(v___x_2162_, 2, v_v_2394_);
lean_ctor_set(v___x_2162_, 1, v_k_2393_);
lean_ctor_set(v___x_2162_, 0, v___x_2398_);
v___x_2402_ = v___x_2162_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v_k_2393_);
lean_ctor_set(v_reuseFailAlloc_2403_, 2, v_v_2394_);
lean_ctor_set(v_reuseFailAlloc_2403_, 3, v_l_2391_);
lean_ctor_set(v_reuseFailAlloc_2403_, 4, v___x_2400_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
else
{
lean_object* v_r_2408_; 
v_r_2408_ = lean_ctor_get(v_impl_2304_, 4);
lean_inc(v_r_2408_);
if (lean_obj_tag(v_r_2408_) == 0)
{
lean_object* v_k_2409_; lean_object* v_v_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2433_; 
lean_inc(v_l_2391_);
v_k_2409_ = lean_ctor_get(v_impl_2304_, 1);
v_v_2410_ = lean_ctor_get(v_impl_2304_, 2);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_impl_2304_);
if (v_isSharedCheck_2433_ == 0)
{
lean_object* v_unused_2434_; lean_object* v_unused_2435_; lean_object* v_unused_2436_; 
v_unused_2434_ = lean_ctor_get(v_impl_2304_, 4);
lean_dec(v_unused_2434_);
v_unused_2435_ = lean_ctor_get(v_impl_2304_, 3);
lean_dec(v_unused_2435_);
v_unused_2436_ = lean_ctor_get(v_impl_2304_, 0);
lean_dec(v_unused_2436_);
v___x_2412_ = v_impl_2304_;
v_isShared_2413_ = v_isSharedCheck_2433_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_v_2410_);
lean_inc(v_k_2409_);
lean_dec(v_impl_2304_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2433_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v_k_2414_; lean_object* v_v_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2429_; 
v_k_2414_ = lean_ctor_get(v_r_2408_, 1);
v_v_2415_ = lean_ctor_get(v_r_2408_, 2);
v_isSharedCheck_2429_ = !lean_is_exclusive(v_r_2408_);
if (v_isSharedCheck_2429_ == 0)
{
lean_object* v_unused_2430_; lean_object* v_unused_2431_; lean_object* v_unused_2432_; 
v_unused_2430_ = lean_ctor_get(v_r_2408_, 4);
lean_dec(v_unused_2430_);
v_unused_2431_ = lean_ctor_get(v_r_2408_, 3);
lean_dec(v_unused_2431_);
v_unused_2432_ = lean_ctor_get(v_r_2408_, 0);
lean_dec(v_unused_2432_);
v___x_2417_ = v_r_2408_;
v_isShared_2418_ = v_isSharedCheck_2429_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_v_2415_);
lean_inc(v_k_2414_);
lean_dec(v_r_2408_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2429_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2419_ = lean_unsigned_to_nat(3u);
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 4, v_l_2391_);
lean_ctor_set(v___x_2417_, 3, v_l_2391_);
lean_ctor_set(v___x_2417_, 2, v_v_2410_);
lean_ctor_set(v___x_2417_, 1, v_k_2409_);
lean_ctor_set(v___x_2417_, 0, v___x_2305_);
v___x_2421_ = v___x_2417_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_k_2409_);
lean_ctor_set(v_reuseFailAlloc_2428_, 2, v_v_2410_);
lean_ctor_set(v_reuseFailAlloc_2428_, 3, v_l_2391_);
lean_ctor_set(v_reuseFailAlloc_2428_, 4, v_l_2391_);
v___x_2421_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2423_; 
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 4, v_l_2391_);
lean_ctor_set(v___x_2412_, 2, v_v_2158_);
lean_ctor_set(v___x_2412_, 1, v_k_2157_);
lean_ctor_set(v___x_2412_, 0, v___x_2305_);
v___x_2423_ = v___x_2412_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_k_2157_);
lean_ctor_set(v_reuseFailAlloc_2427_, 2, v_v_2158_);
lean_ctor_set(v_reuseFailAlloc_2427_, 3, v_l_2391_);
lean_ctor_set(v_reuseFailAlloc_2427_, 4, v_l_2391_);
v___x_2423_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2425_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 4, v___x_2423_);
lean_ctor_set(v___x_2162_, 3, v___x_2421_);
lean_ctor_set(v___x_2162_, 2, v_v_2415_);
lean_ctor_set(v___x_2162_, 1, v_k_2414_);
lean_ctor_set(v___x_2162_, 0, v___x_2419_);
v___x_2425_ = v___x_2162_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_k_2414_);
lean_ctor_set(v_reuseFailAlloc_2426_, 2, v_v_2415_);
lean_ctor_set(v_reuseFailAlloc_2426_, 3, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2426_, 4, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
}
}
else
{
lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2437_ = lean_unsigned_to_nat(2u);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 4, v_r_2408_);
lean_ctor_set(v___x_2162_, 3, v_impl_2304_);
lean_ctor_set(v___x_2162_, 0, v___x_2437_);
v___x_2439_ = v___x_2162_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_k_2157_);
lean_ctor_set(v_reuseFailAlloc_2440_, 2, v_v_2158_);
lean_ctor_set(v_reuseFailAlloc_2440_, 3, v_impl_2304_);
lean_ctor_set(v_reuseFailAlloc_2440_, 4, v_r_2408_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = lean_unsigned_to_nat(1u);
v___x_2443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
lean_ctor_set(v___x_2443_, 1, v_k_2153_);
lean_ctor_set(v___x_2443_, 2, v_v_2154_);
lean_ctor_set(v___x_2443_, 3, v_t_2155_);
lean_ctor_set(v___x_2443_, 4, v_t_2155_);
return v___x_2443_;
}
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(lean_object* v_k_2444_, lean_object* v_t_2445_){
_start:
{
if (lean_obj_tag(v_t_2445_) == 0)
{
lean_object* v_k_2446_; lean_object* v_l_2447_; lean_object* v_r_2448_; uint8_t v___x_2449_; 
v_k_2446_ = lean_ctor_get(v_t_2445_, 1);
v_l_2447_ = lean_ctor_get(v_t_2445_, 3);
v_r_2448_ = lean_ctor_get(v_t_2445_, 4);
v___x_2449_ = lean_nat_dec_lt(v_k_2444_, v_k_2446_);
if (v___x_2449_ == 0)
{
uint8_t v___x_2450_; 
v___x_2450_ = lean_nat_dec_eq(v_k_2444_, v_k_2446_);
if (v___x_2450_ == 0)
{
v_t_2445_ = v_r_2448_;
goto _start;
}
else
{
return v___x_2450_;
}
}
else
{
v_t_2445_ = v_l_2447_;
goto _start;
}
}
else
{
uint8_t v___x_2453_; 
v___x_2453_ = 0;
return v___x_2453_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2444_ = stack[0].m_obj;
lean_object* v_t_2445_ = stack[1].m_obj;
uint8_t v_res_2454_;
v_res_2454_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2444_, v_t_2445_);
stack->m_num = v_res_2454_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg___boxed(lean_object* v_k_2455_, lean_object* v_t_2456_){
_start:
{
uint8_t v_res_2457_; lean_object* v_r_2458_; 
v_res_2457_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2455_, v_t_2456_);
lean_dec(v_t_2456_);
lean_dec(v_k_2455_);
v_r_2458_ = lean_box(v_res_2457_);
return v_r_2458_;
}
}
lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(lean_object* v_y_2459_, lean_object* v_x_2460_, size_t v_x_2461_, size_t v_x_2462_){
_start:
{
if (lean_obj_tag(v_x_2460_) == 0)
{
lean_object* v_cs_2463_; size_t v_j_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v_cs_2463_ = lean_ctor_get(v_x_2460_, 0);
v_j_2464_ = lean_usize_shift_right(v_x_2461_, v_x_2462_);
v___x_2465_ = lean_usize_to_nat(v_j_2464_);
v___x_2466_ = lean_array_get_size(v_cs_2463_);
v___x_2467_ = lean_nat_dec_lt(v___x_2465_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_dec(v___x_2465_);
lean_dec(v_y_2459_);
return v_x_2460_;
}
else
{
lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2485_; 
lean_inc_ref(v_cs_2463_);
v_isSharedCheck_2485_ = !lean_is_exclusive(v_x_2460_);
if (v_isSharedCheck_2485_ == 0)
{
lean_object* v_unused_2486_; 
v_unused_2486_ = lean_ctor_get(v_x_2460_, 0);
lean_dec(v_unused_2486_);
v___x_2469_ = v_x_2460_;
v_isShared_2470_ = v_isSharedCheck_2485_;
goto v_resetjp_2468_;
}
else
{
lean_dec(v_x_2460_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2485_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
size_t v___x_2471_; size_t v___x_2472_; size_t v___x_2473_; size_t v_i_2474_; size_t v___x_2475_; size_t v_shift_2476_; lean_object* v_v_2477_; lean_object* v___x_2478_; lean_object* v_xs_x27_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2471_ = ((size_t)1ULL);
v___x_2472_ = lean_usize_shift_left(v___x_2471_, v_x_2462_);
v___x_2473_ = lean_usize_sub(v___x_2472_, v___x_2471_);
v_i_2474_ = lean_usize_land(v_x_2461_, v___x_2473_);
v___x_2475_ = ((size_t)5ULL);
v_shift_2476_ = lean_usize_sub(v_x_2462_, v___x_2475_);
v_v_2477_ = lean_array_fget(v_cs_2463_, v___x_2465_);
v___x_2478_ = lean_box(0);
v_xs_x27_2479_ = lean_array_fset(v_cs_2463_, v___x_2465_, v___x_2478_);
v___x_2480_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2459_, v_v_2477_, v_i_2474_, v_shift_2476_);
v___x_2481_ = lean_array_fset(v_xs_x27_2479_, v___x_2465_, v___x_2480_);
lean_dec(v___x_2465_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 0, v___x_2481_);
v___x_2483_ = v___x_2469_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_object* v_vs_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
v_vs_2487_ = lean_ctor_get(v_x_2460_, 0);
v___x_2488_ = lean_usize_to_nat(v_x_2461_);
v___x_2489_ = lean_array_get_size(v_vs_2487_);
v___x_2490_ = lean_nat_dec_lt(v___x_2488_, v___x_2489_);
if (v___x_2490_ == 0)
{
lean_dec(v___x_2488_);
lean_dec(v_y_2459_);
return v_x_2460_;
}
else
{
lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2505_; 
lean_inc_ref(v_vs_2487_);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_x_2460_);
if (v_isSharedCheck_2505_ == 0)
{
lean_object* v_unused_2506_; 
v_unused_2506_ = lean_ctor_get(v_x_2460_, 0);
lean_dec(v_unused_2506_);
v___x_2492_ = v_x_2460_;
v_isShared_2493_ = v_isSharedCheck_2505_;
goto v_resetjp_2491_;
}
else
{
lean_dec(v_x_2460_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2505_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v_v_2494_; lean_object* v___x_2495_; lean_object* v_xs_x27_2496_; lean_object* v___y_2498_; uint8_t v___x_2503_; 
v_v_2494_ = lean_array_fget(v_vs_2487_, v___x_2488_);
v___x_2495_ = lean_box(0);
v_xs_x27_2496_ = lean_array_fset(v_vs_2487_, v___x_2488_, v___x_2495_);
v___x_2503_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2459_, v_v_2494_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2459_, v___x_2495_, v_v_2494_);
v___y_2498_ = v___x_2504_;
goto v___jp_2497_;
}
else
{
lean_dec(v_y_2459_);
v___y_2498_ = v_v_2494_;
goto v___jp_2497_;
}
v___jp_2497_:
{
lean_object* v___x_2499_; lean_object* v___x_2501_; 
v___x_2499_ = lean_array_fset(v_xs_x27_2496_, v___x_2488_, v___y_2498_);
lean_dec(v___x_2488_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v___x_2499_);
v___x_2501_ = v___x_2492_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2499_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_2459_ = stack[0].m_obj;
lean_object* v_x_2460_ = stack[1].m_obj;
size_t v_x_2461_ = stack[2].m_num;
size_t v_x_2462_ = stack[3].m_num;
lean_object* v_res_2507_;
v_res_2507_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2459_, v_x_2460_, v_x_2461_, v_x_2462_);
stack->m_obj
 = v_res_2507_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2508_, lean_object* v_x_2509_, lean_object* v_x_2510_, lean_object* v_x_2511_){
_start:
{
size_t v_x_4192__boxed_2512_; size_t v_x_4193__boxed_2513_; lean_object* v_res_2514_; 
v_x_4192__boxed_2512_ = lean_unbox_usize(v_x_2510_);
lean_dec(v_x_2510_);
v_x_4193__boxed_2513_ = lean_unbox_usize(v_x_2511_);
lean_dec(v_x_2511_);
v_res_2514_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2508_, v_x_2509_, v_x_4192__boxed_2512_, v_x_4193__boxed_2513_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(lean_object* v_y_2515_, lean_object* v_t_2516_, lean_object* v_i_2517_){
_start:
{
lean_object* v_root_2518_; lean_object* v_tail_2519_; lean_object* v_size_2520_; size_t v_shift_2521_; lean_object* v_tailOff_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2549_; 
v_root_2518_ = lean_ctor_get(v_t_2516_, 0);
v_tail_2519_ = lean_ctor_get(v_t_2516_, 1);
v_size_2520_ = lean_ctor_get(v_t_2516_, 2);
v_shift_2521_ = lean_ctor_get_usize(v_t_2516_, 4);
v_tailOff_2522_ = lean_ctor_get(v_t_2516_, 3);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_t_2516_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2524_ = v_t_2516_;
v_isShared_2525_ = v_isSharedCheck_2549_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_tailOff_2522_);
lean_inc(v_size_2520_);
lean_inc(v_tail_2519_);
lean_inc(v_root_2518_);
lean_dec(v_t_2516_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2549_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
uint8_t v___x_2526_; 
v___x_2526_ = lean_nat_dec_le(v_tailOff_2522_, v_i_2517_);
if (v___x_2526_ == 0)
{
size_t v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2527_ = lean_usize_of_nat(v_i_2517_);
v___x_2528_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2515_, v_root_2518_, v___x_2527_, v_shift_2521_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2528_);
v___x_2530_ = v___x_2524_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_tail_2519_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v_size_2520_);
lean_ctor_set(v_reuseFailAlloc_2531_, 3, v_tailOff_2522_);
lean_ctor_set_usize(v_reuseFailAlloc_2531_, 4, v_shift_2521_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
else
{
lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2532_ = lean_nat_sub(v_i_2517_, v_tailOff_2522_);
v___x_2533_ = lean_array_get_size(v_tail_2519_);
v___x_2534_ = lean_nat_dec_lt(v___x_2532_, v___x_2533_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2536_; 
lean_dec(v___x_2532_);
lean_dec(v_y_2515_);
if (v_isShared_2525_ == 0)
{
v___x_2536_ = v___x_2524_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_root_2518_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_tail_2519_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_size_2520_);
lean_ctor_set(v_reuseFailAlloc_2537_, 3, v_tailOff_2522_);
lean_ctor_set_usize(v_reuseFailAlloc_2537_, 4, v_shift_2521_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
else
{
lean_object* v_v_2538_; lean_object* v___x_2539_; lean_object* v_xs_x27_2540_; lean_object* v___y_2542_; uint8_t v___x_2547_; 
v_v_2538_ = lean_array_fget(v_tail_2519_, v___x_2532_);
v___x_2539_ = lean_box(0);
v_xs_x27_2540_ = lean_array_fset(v_tail_2519_, v___x_2532_, v___x_2539_);
v___x_2547_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2515_, v_v_2538_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; 
v___x_2548_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2515_, v___x_2539_, v_v_2538_);
v___y_2542_ = v___x_2548_;
goto v___jp_2541_;
}
else
{
lean_dec(v_y_2515_);
v___y_2542_ = v_v_2538_;
goto v___jp_2541_;
}
v___jp_2541_:
{
lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2543_ = lean_array_fset(v_xs_x27_2540_, v___x_2532_, v___y_2542_);
lean_dec(v___x_2532_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 1, v___x_2543_);
v___x_2545_ = v___x_2524_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_root_2518_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2546_, 2, v_size_2520_);
lean_ctor_set(v_reuseFailAlloc_2546_, 3, v_tailOff_2522_);
lean_ctor_set_usize(v_reuseFailAlloc_2546_, 4, v_shift_2521_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2___boxed(lean_object* v_y_2550_, lean_object* v_t_2551_, lean_object* v_i_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2550_, v_t_2551_, v_i_2552_);
lean_dec(v_i_2552_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(lean_object* v_y_2554_, lean_object* v_x_2555_, lean_object* v_s_2556_){
_start:
{
lean_object* v_vars_2557_; lean_object* v_varMap_2558_; lean_object* v_varsHistory_2559_; lean_object* v_natToIntMap_2560_; lean_object* v_natDef_2561_; lean_object* v_dvds_2562_; lean_object* v_lowers_2563_; lean_object* v_uppers_2564_; lean_object* v_diseqs_2565_; lean_object* v_elimEqs_2566_; lean_object* v_elimStack_2567_; lean_object* v_occurs_2568_; lean_object* v_assignment_2569_; lean_object* v_nextCnstrId_2570_; uint8_t v_caseSplits_2571_; lean_object* v_steps_2572_; lean_object* v_conflict_x3f_2573_; lean_object* v_diseqSplits_2574_; lean_object* v_divMod_2575_; uint8_t v_usedCommRing_2576_; lean_object* v_nonlinearOccs_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2585_; 
v_vars_2557_ = lean_ctor_get(v_s_2556_, 0);
v_varMap_2558_ = lean_ctor_get(v_s_2556_, 1);
v_varsHistory_2559_ = lean_ctor_get(v_s_2556_, 2);
v_natToIntMap_2560_ = lean_ctor_get(v_s_2556_, 3);
v_natDef_2561_ = lean_ctor_get(v_s_2556_, 4);
v_dvds_2562_ = lean_ctor_get(v_s_2556_, 5);
v_lowers_2563_ = lean_ctor_get(v_s_2556_, 6);
v_uppers_2564_ = lean_ctor_get(v_s_2556_, 7);
v_diseqs_2565_ = lean_ctor_get(v_s_2556_, 8);
v_elimEqs_2566_ = lean_ctor_get(v_s_2556_, 9);
v_elimStack_2567_ = lean_ctor_get(v_s_2556_, 10);
v_occurs_2568_ = lean_ctor_get(v_s_2556_, 11);
v_assignment_2569_ = lean_ctor_get(v_s_2556_, 12);
v_nextCnstrId_2570_ = lean_ctor_get(v_s_2556_, 13);
v_caseSplits_2571_ = lean_ctor_get_uint8(v_s_2556_, sizeof(void*)*19);
v_steps_2572_ = lean_ctor_get(v_s_2556_, 14);
v_conflict_x3f_2573_ = lean_ctor_get(v_s_2556_, 15);
v_diseqSplits_2574_ = lean_ctor_get(v_s_2556_, 16);
v_divMod_2575_ = lean_ctor_get(v_s_2556_, 17);
v_usedCommRing_2576_ = lean_ctor_get_uint8(v_s_2556_, sizeof(void*)*19 + 1);
v_nonlinearOccs_2577_ = lean_ctor_get(v_s_2556_, 18);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_s_2556_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2579_ = v_s_2556_;
v_isShared_2580_ = v_isSharedCheck_2585_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_nonlinearOccs_2577_);
lean_inc(v_divMod_2575_);
lean_inc(v_diseqSplits_2574_);
lean_inc(v_conflict_x3f_2573_);
lean_inc(v_steps_2572_);
lean_inc(v_nextCnstrId_2570_);
lean_inc(v_assignment_2569_);
lean_inc(v_occurs_2568_);
lean_inc(v_elimStack_2567_);
lean_inc(v_elimEqs_2566_);
lean_inc(v_diseqs_2565_);
lean_inc(v_uppers_2564_);
lean_inc(v_lowers_2563_);
lean_inc(v_dvds_2562_);
lean_inc(v_natDef_2561_);
lean_inc(v_natToIntMap_2560_);
lean_inc(v_varsHistory_2559_);
lean_inc(v_varMap_2558_);
lean_inc(v_vars_2557_);
lean_dec(v_s_2556_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2585_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2581_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2554_, v_occurs_2568_, v_x_2555_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 11, v___x_2581_);
v___x_2583_ = v___x_2579_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_vars_2557_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_varMap_2558_);
lean_ctor_set(v_reuseFailAlloc_2584_, 2, v_varsHistory_2559_);
lean_ctor_set(v_reuseFailAlloc_2584_, 3, v_natToIntMap_2560_);
lean_ctor_set(v_reuseFailAlloc_2584_, 4, v_natDef_2561_);
lean_ctor_set(v_reuseFailAlloc_2584_, 5, v_dvds_2562_);
lean_ctor_set(v_reuseFailAlloc_2584_, 6, v_lowers_2563_);
lean_ctor_set(v_reuseFailAlloc_2584_, 7, v_uppers_2564_);
lean_ctor_set(v_reuseFailAlloc_2584_, 8, v_diseqs_2565_);
lean_ctor_set(v_reuseFailAlloc_2584_, 9, v_elimEqs_2566_);
lean_ctor_set(v_reuseFailAlloc_2584_, 10, v_elimStack_2567_);
lean_ctor_set(v_reuseFailAlloc_2584_, 11, v___x_2581_);
lean_ctor_set(v_reuseFailAlloc_2584_, 12, v_assignment_2569_);
lean_ctor_set(v_reuseFailAlloc_2584_, 13, v_nextCnstrId_2570_);
lean_ctor_set(v_reuseFailAlloc_2584_, 14, v_steps_2572_);
lean_ctor_set(v_reuseFailAlloc_2584_, 15, v_conflict_x3f_2573_);
lean_ctor_set(v_reuseFailAlloc_2584_, 16, v_diseqSplits_2574_);
lean_ctor_set(v_reuseFailAlloc_2584_, 17, v_divMod_2575_);
lean_ctor_set(v_reuseFailAlloc_2584_, 18, v_nonlinearOccs_2577_);
lean_ctor_set_uint8(v_reuseFailAlloc_2584_, sizeof(void*)*19, v_caseSplits_2571_);
lean_ctor_set_uint8(v_reuseFailAlloc_2584_, sizeof(void*)*19 + 1, v_usedCommRing_2576_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed(lean_object* v_y_2586_, lean_object* v_x_2587_, lean_object* v_s_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(v_y_2586_, v_x_2587_, v_s_2588_);
lean_dec(v_x_2587_);
return v_res_2589_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(lean_object* v_x_2590_, lean_object* v_y_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v___f_2595_; lean_object* v___x_2596_; 
lean_inc(v_x_2590_);
lean_inc(v_y_2591_);
v___f_2595_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2595_, 0, v_y_2591_);
lean_closure_set(v___f_2595_, 1, v_x_2590_);
v___x_2596_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2590_, v_a_2592_, v_a_2593_);
lean_dec(v_x_2590_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2608_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2599_ = v___x_2596_;
v_isShared_2600_ = v_isSharedCheck_2608_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2596_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2608_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
uint8_t v___x_2601_; 
v___x_2601_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2591_, v_a_2597_);
lean_dec(v_a_2597_);
lean_dec(v_y_2591_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
lean_del_object(v___x_2599_);
v___x_2602_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2603_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2602_, v___f_2595_, v_a_2592_);
return v___x_2603_;
}
else
{
lean_object* v___x_2604_; lean_object* v___x_2606_; 
lean_dec_ref(v___f_2595_);
v___x_2604_ = lean_box(0);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 0, v___x_2604_);
v___x_2606_ = v___x_2599_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec_ref(v___f_2595_);
lean_dec(v_y_2591_);
v_a_2609_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2596_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2596_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
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
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2590_ = stack[0].m_obj;
lean_object* v_y_2591_ = stack[1].m_obj;
lean_object* v_a_2592_ = stack[2].m_obj;
lean_object* v_a_2593_ = stack[3].m_obj;
lean_object* v_res_2617_;
v_res_2617_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2590_, v_y_2591_, v_a_2592_, v_a_2593_);
stack->m_obj
 = v_res_2617_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___boxed(lean_object* v_x_2618_, lean_object* v_y_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2618_, v_y_2619_, v_a_2620_, v_a_2621_);
lean_dec_ref(v_a_2621_);
lean_dec(v_a_2620_);
return v_res_2623_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc(lean_object* v_x_2624_, lean_object* v_y_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2624_, v_y_2625_, v_a_2626_, v_a_2634_);
return v___x_2637_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_addOcc_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2624_ = stack[0].m_obj;
lean_object* v_y_2625_ = stack[1].m_obj;
lean_object* v_a_2626_ = stack[2].m_obj;
lean_object* v_a_2627_ = stack[3].m_obj;
lean_object* v_a_2628_ = stack[4].m_obj;
lean_object* v_a_2629_ = stack[5].m_obj;
lean_object* v_a_2630_ = stack[6].m_obj;
lean_object* v_a_2631_ = stack[7].m_obj;
lean_object* v_a_2632_ = stack[8].m_obj;
lean_object* v_a_2633_ = stack[9].m_obj;
lean_object* v_a_2634_ = stack[10].m_obj;
lean_object* v_a_2635_ = stack[11].m_obj;
lean_object* v_res_2638_;
v_res_2638_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc(v_x_2624_, v_y_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_);
stack->m_obj
 = v_res_2638_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___boxed(lean_object* v_x_2639_, lean_object* v_y_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc(v_x_2639_, v_y_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec(v_a_2642_);
lean_dec(v_a_2641_);
return v_res_2652_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(lean_object* v_00_u03b2_2653_, lean_object* v_k_2654_, lean_object* v_t_2655_){
_start:
{
uint8_t v___x_2656_; 
v___x_2656_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2654_, v_t_2655_);
return v___x_2656_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2654_ = stack[1].m_obj;
lean_object* v_t_2655_ = stack[2].m_obj;
uint8_t v_res_2657_;
v_res_2657_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(lean_box(0), v_k_2654_, v_t_2655_);
stack->m_num = v_res_2657_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2658_, lean_object* v_k_2659_, lean_object* v_t_2660_){
_start:
{
uint8_t v_res_2661_; lean_object* v_r_2662_; 
v_res_2661_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(v_00_u03b2_2658_, v_k_2659_, v_t_2660_);
lean_dec(v_t_2660_);
lean_dec(v_k_2659_);
v_r_2662_ = lean_box(v_res_2661_);
return v_r_2662_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1(lean_object* v_00_u03b2_2663_, lean_object* v_k_2664_, lean_object* v_v_2665_, lean_object* v_t_2666_, lean_object* v_hl_2667_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2664_, v_v_2665_, v_t_2666_);
return v___x_2668_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(lean_object* v_y_2669_, lean_object* v_p_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
if (lean_obj_tag(v_p_2670_) == 1)
{
lean_object* v_v_2674_; lean_object* v_p_2675_; lean_object* v___x_2676_; 
v_v_2674_ = lean_ctor_get(v_p_2670_, 1);
lean_inc(v_v_2674_);
v_p_2675_ = lean_ctor_get(v_p_2670_, 2);
lean_inc_ref(v_p_2675_);
lean_dec_ref_known(v_p_2670_, 3);
lean_inc(v_y_2669_);
v___x_2676_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_v_2674_, v_y_2669_, v_a_2671_, v_a_2672_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_dec_ref_known(v___x_2676_, 1);
v_p_2670_ = v_p_2675_;
goto _start;
}
else
{
lean_dec_ref(v_p_2675_);
lean_dec(v_y_2669_);
return v___x_2676_;
}
}
else
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_dec_ref(v_p_2670_);
lean_dec(v_y_2669_);
v___x_2678_ = lean_box(0);
v___x_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
return v___x_2679_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_2669_ = stack[0].m_obj;
lean_object* v_p_2670_ = stack[1].m_obj;
lean_object* v_a_2671_ = stack[2].m_obj;
lean_object* v_a_2672_ = stack[3].m_obj;
lean_object* v_res_2680_;
v_res_2680_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2669_, v_p_2670_, v_a_2671_, v_a_2672_);
stack->m_obj
 = v_res_2680_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg___boxed(lean_object* v_y_2681_, lean_object* v_p_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2681_, v_p_2682_, v_a_2683_, v_a_2684_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
return v_res_2686_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(lean_object* v_y_2687_, lean_object* v_p_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2687_, v_p_2688_, v_a_2689_, v_a_2697_);
return v___x_2700_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_2687_ = stack[0].m_obj;
lean_object* v_p_2688_ = stack[1].m_obj;
lean_object* v_a_2689_ = stack[2].m_obj;
lean_object* v_a_2690_ = stack[3].m_obj;
lean_object* v_a_2691_ = stack[4].m_obj;
lean_object* v_a_2692_ = stack[5].m_obj;
lean_object* v_a_2693_ = stack[6].m_obj;
lean_object* v_a_2694_ = stack[7].m_obj;
lean_object* v_a_2695_ = stack[8].m_obj;
lean_object* v_a_2696_ = stack[9].m_obj;
lean_object* v_a_2697_ = stack[10].m_obj;
lean_object* v_a_2698_ = stack[11].m_obj;
lean_object* v_res_2701_;
v_res_2701_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(v_y_2687_, v_p_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
stack->m_obj
 = v_res_2701_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___boxed(lean_object* v_y_2702_, lean_object* v_p_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(v_y_2702_, v_p_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec(v_a_2707_);
lean_dec_ref(v_a_2706_);
lean_dec(v_a_2705_);
lean_dec(v_a_2704_);
return v_res_2715_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = ((lean_object*)(l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__0));
v___x_2718_ = l_Lean_stringToMessageData(v___x_2717_);
return v___x_2718_;
}
}
lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg(lean_object* v_p_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
if (lean_obj_tag(v_p_2719_) == 1)
{
lean_object* v_v_2726_; lean_object* v_p_2727_; lean_object* v___x_2728_; 
v_v_2726_ = lean_ctor_get(v_p_2719_, 1);
lean_inc(v_v_2726_);
v_p_2727_ = lean_ctor_get(v_p_2719_, 2);
lean_inc_ref(v_p_2727_);
lean_dec_ref_known(v_p_2719_, 3);
v___x_2728_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_v_2726_, v_p_2727_, v_a_2720_, v_a_2723_);
return v___x_2728_;
}
else
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_dec_ref(v_p_2719_);
v___x_2729_ = lean_obj_once(&l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1, &l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1_once, _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1);
v___x_2730_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2729_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_);
return v___x_2730_;
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_updateOccs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2719_ = stack[0].m_obj;
lean_object* v_a_2720_ = stack[1].m_obj;
lean_object* v_a_2721_ = stack[2].m_obj;
lean_object* v_a_2722_ = stack[3].m_obj;
lean_object* v_a_2723_ = stack[4].m_obj;
lean_object* v_a_2724_ = stack[5].m_obj;
lean_object* v_res_2731_;
v_res_2731_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_);
stack->m_obj
 = v_res_2731_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg___boxed(lean_object* v_p_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
lean_dec(v_a_2737_);
lean_dec_ref(v_a_2736_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
lean_dec(v_a_2733_);
return v_res_2739_;
}
}
lean_object* l_Int_Internal_Linear_Poly_updateOccs(lean_object* v_p_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2740_, v_a_2741_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_);
return v___x_2752_;
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_updateOccs_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2740_ = stack[0].m_obj;
lean_object* v_a_2741_ = stack[1].m_obj;
lean_object* v_a_2742_ = stack[2].m_obj;
lean_object* v_a_2743_ = stack[3].m_obj;
lean_object* v_a_2744_ = stack[4].m_obj;
lean_object* v_a_2745_ = stack[5].m_obj;
lean_object* v_a_2746_ = stack[6].m_obj;
lean_object* v_a_2747_ = stack[7].m_obj;
lean_object* v_a_2748_ = stack[8].m_obj;
lean_object* v_a_2749_ = stack[9].m_obj;
lean_object* v_a_2750_ = stack[10].m_obj;
lean_object* v_res_2753_;
v_res_2753_ = l_Int_Internal_Linear_Poly_updateOccs(v_p_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_);
stack->m_obj
 = v_res_2753_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___boxed(lean_object* v_p_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Int_Internal_Linear_Poly_updateOccs(v_p_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec_ref(v_a_2757_);
lean_dec(v_a_2756_);
lean_dec(v_a_2755_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go_spec__0(lean_object* v_a_2767_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Rat_ofInt(v_a_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(lean_object* v_a_2769_, lean_object* v_v_2770_, lean_object* v_a_2771_){
_start:
{
if (lean_obj_tag(v_a_2771_) == 0)
{
lean_object* v_k_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2781_; 
v_k_2772_ = lean_ctor_get(v_a_2771_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_a_2771_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2774_ = v_a_2771_;
v_isShared_2775_ = v_isSharedCheck_2781_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_k_2772_);
lean_dec(v_a_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2781_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2779_; 
v___x_2776_ = l_Rat_ofInt(v_k_2772_);
v___x_2777_ = l_Rat_add(v_v_2770_, v___x_2776_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set_tag(v___x_2774_, 1);
lean_ctor_set(v___x_2774_, 0, v___x_2777_);
v___x_2779_ = v___x_2774_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
else
{
lean_object* v_k_2782_; lean_object* v_v_2783_; lean_object* v_p_2784_; lean_object* v_size_2785_; uint8_t v___x_2786_; 
v_k_2782_ = lean_ctor_get(v_a_2771_, 0);
lean_inc(v_k_2782_);
v_v_2783_ = lean_ctor_get(v_a_2771_, 1);
lean_inc(v_v_2783_);
v_p_2784_ = lean_ctor_get(v_a_2771_, 2);
lean_inc_ref(v_p_2784_);
lean_dec_ref_known(v_a_2771_, 3);
v_size_2785_ = lean_ctor_get(v_a_2769_, 2);
v___x_2786_ = lean_nat_dec_lt(v_v_2783_, v_size_2785_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2787_; 
lean_dec_ref(v_p_2784_);
lean_dec(v_v_2783_);
lean_dec(v_k_2782_);
lean_dec_ref(v_v_2770_);
v___x_2787_ = lean_box(0);
return v___x_2787_;
}
else
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2788_ = l_instInhabitedRat;
v___x_2789_ = l_Rat_ofInt(v_k_2782_);
v___x_2790_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2788_, v_a_2769_, v_v_2783_);
lean_dec(v_v_2783_);
v___x_2791_ = l_Rat_mul(v___x_2789_, v___x_2790_);
lean_dec_ref(v___x_2789_);
v___x_2792_ = l_Rat_add(v_v_2770_, v___x_2791_);
v_v_2770_ = v___x_2792_;
v_a_2771_ = v_p_2784_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go___boxed(lean_object* v_a_2794_, lean_object* v_v_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_a_2794_, v_v_2795_, v_a_2796_);
lean_dec_ref(v_a_2794_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(lean_object* v_a_2798_){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = lean_nat_to_int(v_a_2798_);
v___x_2800_ = l_Rat_ofInt(v___x_2799_);
return v___x_2800_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = lean_unsigned_to_nat(0u);
v___x_2802_ = l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(v___x_2801_);
return v___x_2802_;
}
}
lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg(lean_object* v_p_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2804_, v_a_2805_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2818_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2810_ = v___x_2807_;
v_isShared_2811_ = v_isSharedCheck_2818_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2807_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2818_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v_assignment_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2816_; 
v_assignment_2812_ = lean_ctor_get(v_a_2808_, 12);
lean_inc_ref(v_assignment_2812_);
lean_dec(v_a_2808_);
v___x_2813_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2814_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_assignment_2812_, v___x_2813_, v_p_2803_);
lean_dec_ref(v_assignment_2812_);
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 0, v___x_2814_);
v___x_2816_ = v___x_2810_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2814_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec_ref(v_p_2803_);
v_a_2819_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2807_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2807_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_eval_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2803_ = stack[0].m_obj;
lean_object* v_a_2804_ = stack[1].m_obj;
lean_object* v_a_2805_ = stack[2].m_obj;
lean_object* v_res_2827_;
v_res_2827_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2803_, v_a_2804_, v_a_2805_);
stack->m_obj
 = v_res_2827_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg___boxed(lean_object* v_p_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2828_, v_a_2829_, v_a_2830_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
return v_res_2832_;
}
}
lean_object* l_Int_Internal_Linear_Poly_eval_x3f(lean_object* v_p_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v___x_2845_; 
v___x_2845_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2833_, v_a_2834_, v_a_2842_);
return v___x_2845_;
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_eval_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2833_ = stack[0].m_obj;
lean_object* v_a_2834_ = stack[1].m_obj;
lean_object* v_a_2835_ = stack[2].m_obj;
lean_object* v_a_2836_ = stack[3].m_obj;
lean_object* v_a_2837_ = stack[4].m_obj;
lean_object* v_a_2838_ = stack[5].m_obj;
lean_object* v_a_2839_ = stack[6].m_obj;
lean_object* v_a_2840_ = stack[7].m_obj;
lean_object* v_a_2841_ = stack[8].m_obj;
lean_object* v_a_2842_ = stack[9].m_obj;
lean_object* v_a_2843_ = stack[10].m_obj;
lean_object* v_res_2846_;
v_res_2846_ = l_Int_Internal_Linear_Poly_eval_x3f(v_p_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
stack->m_obj
 = v_res_2846_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___boxed(lean_object* v_p_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Int_Internal_Linear_Poly_eval_x3f(v_p_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
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
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(lean_object* v_c_2860_){
_start:
{
lean_object* v_p_2861_; uint8_t v___x_2862_; 
v_p_2861_ = lean_ctor_get(v_c_2860_, 0);
v___x_2862_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2860_ = stack[0].m_obj;
uint8_t v_res_2863_;
v_res_2863_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(v_c_2860_);
stack->m_num = v_res_2863_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat___boxed(lean_object* v_c_2864_){
_start:
{
uint8_t v_res_2865_; lean_object* v_r_2866_; 
v_res_2865_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(v_c_2864_);
lean_dec_ref(v_c_2864_);
v_r_2866_ = lean_box(v_res_2865_);
return v_r_2866_;
}
}
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(lean_object* v_c_2867_){
_start:
{
lean_object* v_d_2868_; lean_object* v_p_2869_; uint8_t v___x_2870_; 
v_d_2868_ = lean_ctor_get(v_c_2867_, 0);
lean_inc(v_d_2868_);
v_p_2869_ = lean_ctor_get(v_c_2867_, 1);
lean_inc_ref(v_p_2869_);
lean_dec_ref(v_c_2867_);
v___x_2870_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_2868_, v_p_2869_);
lean_dec_ref(v_p_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2867_ = stack[0].m_obj;
uint8_t v_res_2871_;
v_res_2871_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(v_c_2867_);
stack->m_num = v_res_2871_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat___boxed(lean_object* v_c_2872_){
_start:
{
uint8_t v_res_2873_; lean_object* v_r_2874_; 
v_res_2873_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(v_c_2872_);
v_r_2874_ = lean_box(v_res_2873_);
return v_r_2874_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object* v_c_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v_d_2879_; lean_object* v_p_2880_; lean_object* v___x_2881_; 
v_d_2879_ = lean_ctor_get(v_c_2875_, 0);
lean_inc(v_d_2879_);
v_p_2880_ = lean_ctor_get(v_c_2875_, 1);
lean_inc_ref(v_p_2880_);
lean_dec_ref(v_c_2875_);
v___x_2881_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2880_, v_a_2876_, v_a_2877_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2909_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2884_ = v___x_2881_;
v_isShared_2885_ = v_isSharedCheck_2909_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2881_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2909_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
if (lean_obj_tag(v_a_2882_) == 1)
{
lean_object* v_val_2886_; lean_object* v_num_2887_; lean_object* v_den_2888_; lean_object* v___x_2889_; uint8_t v___x_2890_; 
v_val_2886_ = lean_ctor_get(v_a_2882_, 0);
lean_inc(v_val_2886_);
lean_dec_ref_known(v_a_2882_, 1);
v_num_2887_ = lean_ctor_get(v_val_2886_, 0);
lean_inc(v_num_2887_);
v_den_2888_ = lean_ctor_get(v_val_2886_, 1);
lean_inc(v_den_2888_);
lean_dec(v_val_2886_);
v___x_2889_ = lean_unsigned_to_nat(1u);
v___x_2890_ = lean_nat_dec_eq(v_den_2888_, v___x_2889_);
lean_dec(v_den_2888_);
if (v___x_2890_ == 0)
{
uint8_t v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2894_; 
lean_dec(v_num_2887_);
lean_dec(v_d_2879_);
v___x_2891_ = 0;
v___x_2892_ = lean_box(v___x_2891_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2892_);
v___x_2894_ = v___x_2884_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2892_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2897_; uint8_t v___x_2898_; uint8_t v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2902_; 
v___x_2896_ = lean_int_emod(v_num_2887_, v_d_2879_);
lean_dec(v_d_2879_);
lean_dec(v_num_2887_);
v___x_2897_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_2898_ = lean_int_dec_eq(v___x_2896_, v___x_2897_);
lean_dec(v___x_2896_);
v___x_2899_ = l_Lean_Bool_toLBool(v___x_2898_);
v___x_2900_ = lean_box(v___x_2899_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2900_);
v___x_2902_ = v___x_2884_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
else
{
uint8_t v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2907_; 
lean_dec(v_a_2882_);
lean_dec(v_d_2879_);
v___x_2904_ = 2;
v___x_2905_ = lean_box(v___x_2904_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2905_);
v___x_2907_ = v___x_2884_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec(v_d_2879_);
v_a_2910_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2881_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2881_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2875_ = stack[0].m_obj;
lean_object* v_a_2876_ = stack[1].m_obj;
lean_object* v_a_2877_ = stack[2].m_obj;
lean_object* v_res_2918_;
v_res_2918_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2875_, v_a_2876_, v_a_2877_);
stack->m_obj
 = v_res_2918_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg___boxed(lean_object* v_c_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2919_, v_a_2920_, v_a_2921_);
lean_dec_ref(v_a_2921_);
lean_dec(v_a_2920_);
return v_res_2923_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(lean_object* v_c_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2924_, v_a_2925_, v_a_2933_);
return v___x_2936_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2924_ = stack[0].m_obj;
lean_object* v_a_2925_ = stack[1].m_obj;
lean_object* v_a_2926_ = stack[2].m_obj;
lean_object* v_a_2927_ = stack[3].m_obj;
lean_object* v_a_2928_ = stack[4].m_obj;
lean_object* v_a_2929_ = stack[5].m_obj;
lean_object* v_a_2930_ = stack[6].m_obj;
lean_object* v_a_2931_ = stack[7].m_obj;
lean_object* v_a_2932_ = stack[8].m_obj;
lean_object* v_a_2933_ = stack[9].m_obj;
lean_object* v_a_2934_ = stack[10].m_obj;
lean_object* v_res_2937_;
v_res_2937_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(v_c_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_);
stack->m_obj
 = v_res_2937_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___boxed(lean_object* v_c_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(v_c_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_a_2940_);
lean_dec(v_a_2939_);
return v_res_2950_;
}
}
lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg(lean_object* v_p_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2951_, v_a_2952_, v_a_2953_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2973_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2958_ = v___x_2955_;
v_isShared_2959_ = v_isSharedCheck_2973_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2955_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2973_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
if (lean_obj_tag(v_a_2956_) == 1)
{
lean_object* v_val_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; uint8_t v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2966_; 
v_val_2960_ = lean_ctor_get(v_a_2956_, 0);
lean_inc(v_val_2960_);
lean_dec_ref_known(v_a_2956_, 1);
v___x_2961_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2962_ = l_Rat_instDecidableLe(v_val_2960_, v___x_2961_);
v___x_2963_ = l_Lean_Bool_toLBool(v___x_2962_);
v___x_2964_ = lean_box(v___x_2963_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v___x_2964_);
v___x_2966_ = v___x_2958_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
else
{
uint8_t v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2971_; 
lean_dec(v_a_2956_);
v___x_2968_ = 2;
v___x_2969_ = lean_box(v___x_2968_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v___x_2969_);
v___x_2971_ = v___x_2958_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2969_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
v_a_2974_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2955_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2955_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_satisfiedLe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2951_ = stack[0].m_obj;
lean_object* v_a_2952_ = stack[1].m_obj;
lean_object* v_a_2953_ = stack[2].m_obj;
lean_object* v_res_2982_;
v_res_2982_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2951_, v_a_2952_, v_a_2953_);
stack->m_obj
 = v_res_2982_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg___boxed(lean_object* v_p_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2983_, v_a_2984_, v_a_2985_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
return v_res_2987_;
}
}
lean_object* l_Int_Internal_Linear_Poly_satisfiedLe(lean_object* v_p_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2988_, v_a_2989_, v_a_2997_);
return v___x_3000_;
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_satisfiedLe_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2988_ = stack[0].m_obj;
lean_object* v_a_2989_ = stack[1].m_obj;
lean_object* v_a_2990_ = stack[2].m_obj;
lean_object* v_a_2991_ = stack[3].m_obj;
lean_object* v_a_2992_ = stack[4].m_obj;
lean_object* v_a_2993_ = stack[5].m_obj;
lean_object* v_a_2994_ = stack[6].m_obj;
lean_object* v_a_2995_ = stack[7].m_obj;
lean_object* v_a_2996_ = stack[8].m_obj;
lean_object* v_a_2997_ = stack[9].m_obj;
lean_object* v_a_2998_ = stack[10].m_obj;
lean_object* v_res_3001_;
v_res_3001_ = l_Int_Internal_Linear_Poly_satisfiedLe(v_p_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
stack->m_obj
 = v_res_3001_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___boxed(lean_object* v_p_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Int_Internal_Linear_Poly_satisfiedLe(v_p_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
lean_dec(v_a_3004_);
lean_dec(v_a_3003_);
return v_res_3014_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(lean_object* v_c_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v_p_3019_; lean_object* v___x_3020_; 
v_p_3019_ = lean_ctor_get(v_c_3015_, 0);
lean_inc_ref(v_p_3019_);
lean_dec_ref(v_c_3015_);
v___x_3020_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_3019_, v_a_3016_, v_a_3017_);
return v___x_3020_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3015_ = stack[0].m_obj;
lean_object* v_a_3016_ = stack[1].m_obj;
lean_object* v_a_3017_ = stack[2].m_obj;
lean_object* v_res_3021_;
v_res_3021_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_3015_, v_a_3016_, v_a_3017_);
stack->m_obj
 = v_res_3021_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg___boxed(lean_object* v_c_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_3022_, v_a_3023_, v_a_3024_);
lean_dec_ref(v_a_3024_);
lean_dec(v_a_3023_);
return v_res_3026_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(lean_object* v_c_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_3027_, v_a_3028_, v_a_3036_);
return v___x_3039_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3027_ = stack[0].m_obj;
lean_object* v_a_3028_ = stack[1].m_obj;
lean_object* v_a_3029_ = stack[2].m_obj;
lean_object* v_a_3030_ = stack[3].m_obj;
lean_object* v_a_3031_ = stack[4].m_obj;
lean_object* v_a_3032_ = stack[5].m_obj;
lean_object* v_a_3033_ = stack[6].m_obj;
lean_object* v_a_3034_ = stack[7].m_obj;
lean_object* v_a_3035_ = stack[8].m_obj;
lean_object* v_a_3036_ = stack[9].m_obj;
lean_object* v_a_3037_ = stack[10].m_obj;
lean_object* v_res_3040_;
v_res_3040_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(v_c_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
stack->m_obj
 = v_res_3040_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___boxed(lean_object* v_c_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(v_c_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_);
lean_dec(v_a_3051_);
lean_dec_ref(v_a_3050_);
lean_dec(v_a_3049_);
lean_dec_ref(v_a_3048_);
lean_dec(v_a_3047_);
lean_dec_ref(v_a_3046_);
lean_dec(v_a_3045_);
lean_dec_ref(v_a_3044_);
lean_dec(v_a_3043_);
lean_dec(v_a_3042_);
return v_res_3053_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(lean_object* v_c_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v_p_3058_; lean_object* v___x_3059_; 
v_p_3058_ = lean_ctor_get(v_c_3054_, 0);
lean_inc_ref(v_p_3058_);
lean_dec_ref(v_c_3054_);
v___x_3059_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3058_, v_a_3055_, v_a_3056_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3079_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3062_ = v___x_3059_;
v_isShared_3063_ = v_isSharedCheck_3079_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3059_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3079_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
uint8_t v___y_3065_; 
if (lean_obj_tag(v_a_3060_) == 1)
{
lean_object* v_val_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; 
v_val_3071_ = lean_ctor_get(v_a_3060_, 0);
lean_inc(v_val_3071_);
lean_dec_ref_known(v_a_3060_, 1);
v___x_3072_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_3073_ = l_instDecidableEqRat_decEq(v_val_3071_, v___x_3072_);
lean_dec(v_val_3071_);
if (v___x_3073_ == 0)
{
uint8_t v___x_3074_; 
v___x_3074_ = 1;
v___y_3065_ = v___x_3074_;
goto v___jp_3064_;
}
else
{
uint8_t v___x_3075_; 
v___x_3075_ = 0;
v___y_3065_ = v___x_3075_;
goto v___jp_3064_;
}
}
else
{
uint8_t v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
lean_del_object(v___x_3062_);
lean_dec(v_a_3060_);
v___x_3076_ = 2;
v___x_3077_ = lean_box(v___x_3076_);
v___x_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
return v___x_3078_;
}
v___jp_3064_:
{
uint8_t v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3069_; 
v___x_3066_ = l_Lean_Bool_toLBool(v___y_3065_);
v___x_3067_ = lean_box(v___x_3066_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 0, v___x_3067_);
v___x_3069_ = v___x_3062_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3067_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
v_a_3080_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3059_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3059_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3054_ = stack[0].m_obj;
lean_object* v_a_3055_ = stack[1].m_obj;
lean_object* v_a_3056_ = stack[2].m_obj;
lean_object* v_res_3088_;
v_res_3088_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_3054_, v_a_3055_, v_a_3056_);
stack->m_obj
 = v_res_3088_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg___boxed(lean_object* v_c_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_3089_, v_a_3090_, v_a_3091_);
lean_dec_ref(v_a_3091_);
lean_dec(v_a_3090_);
return v_res_3093_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(lean_object* v_c_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_3094_, v_a_3095_, v_a_3103_);
return v___x_3106_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3094_ = stack[0].m_obj;
lean_object* v_a_3095_ = stack[1].m_obj;
lean_object* v_a_3096_ = stack[2].m_obj;
lean_object* v_a_3097_ = stack[3].m_obj;
lean_object* v_a_3098_ = stack[4].m_obj;
lean_object* v_a_3099_ = stack[5].m_obj;
lean_object* v_a_3100_ = stack[6].m_obj;
lean_object* v_a_3101_ = stack[7].m_obj;
lean_object* v_a_3102_ = stack[8].m_obj;
lean_object* v_a_3103_ = stack[9].m_obj;
lean_object* v_a_3104_ = stack[10].m_obj;
lean_object* v_res_3107_;
v_res_3107_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(v_c_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_);
stack->m_obj
 = v_res_3107_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___boxed(lean_object* v_c_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(v_c_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_);
lean_dec(v_a_3118_);
lean_dec_ref(v_a_3117_);
lean_dec(v_a_3116_);
lean_dec_ref(v_a_3115_);
lean_dec(v_a_3114_);
lean_dec_ref(v_a_3113_);
lean_dec(v_a_3112_);
lean_dec_ref(v_a_3111_);
lean_dec(v_a_3110_);
lean_dec(v_a_3109_);
return v_res_3120_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(lean_object* v_c_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_){
_start:
{
lean_object* v_p_3125_; lean_object* v___x_3126_; 
v_p_3125_ = lean_ctor_get(v_c_3121_, 0);
lean_inc_ref(v_p_3125_);
lean_dec_ref(v_c_3121_);
v___x_3126_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3125_, v_a_3122_, v_a_3123_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3144_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3129_ = v___x_3126_;
v_isShared_3130_ = v_isSharedCheck_3144_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3126_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3144_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
if (lean_obj_tag(v_a_3127_) == 1)
{
lean_object* v_val_3131_; lean_object* v___x_3132_; uint8_t v___x_3133_; uint8_t v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3137_; 
v_val_3131_ = lean_ctor_get(v_a_3127_, 0);
lean_inc(v_val_3131_);
lean_dec_ref_known(v_a_3127_, 1);
v___x_3132_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_3133_ = l_instDecidableEqRat_decEq(v_val_3131_, v___x_3132_);
lean_dec(v_val_3131_);
v___x_3134_ = l_Lean_Bool_toLBool(v___x_3133_);
v___x_3135_ = lean_box(v___x_3134_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3135_);
v___x_3137_ = v___x_3129_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
else
{
uint8_t v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3142_; 
lean_dec(v_a_3127_);
v___x_3139_ = 2;
v___x_3140_ = lean_box(v___x_3139_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set(v___x_3129_, 0, v___x_3140_);
v___x_3142_ = v___x_3129_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3140_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
v_a_3145_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3126_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3126_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3121_ = stack[0].m_obj;
lean_object* v_a_3122_ = stack[1].m_obj;
lean_object* v_a_3123_ = stack[2].m_obj;
lean_object* v_res_3153_;
v_res_3153_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_3121_, v_a_3122_, v_a_3123_);
stack->m_obj
 = v_res_3153_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg___boxed(lean_object* v_c_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_3154_, v_a_3155_, v_a_3156_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
return v_res_3158_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(lean_object* v_c_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_3159_, v_a_3160_, v_a_3168_);
return v___x_3171_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3159_ = stack[0].m_obj;
lean_object* v_a_3160_ = stack[1].m_obj;
lean_object* v_a_3161_ = stack[2].m_obj;
lean_object* v_a_3162_ = stack[3].m_obj;
lean_object* v_a_3163_ = stack[4].m_obj;
lean_object* v_a_3164_ = stack[5].m_obj;
lean_object* v_a_3165_ = stack[6].m_obj;
lean_object* v_a_3166_ = stack[7].m_obj;
lean_object* v_a_3167_ = stack[8].m_obj;
lean_object* v_a_3168_ = stack[9].m_obj;
lean_object* v_a_3169_ = stack[10].m_obj;
lean_object* v_res_3172_;
v_res_3172_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(v_c_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_);
stack->m_obj
 = v_res_3172_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___boxed(lean_object* v_c_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(v_c_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_);
lean_dec(v_a_3183_);
lean_dec_ref(v_a_3182_);
lean_dec(v_a_3181_);
lean_dec_ref(v_a_3180_);
lean_dec(v_a_3179_);
lean_dec_ref(v_a_3178_);
lean_dec(v_a_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_a_3175_);
lean_dec(v_a_3174_);
return v_res_3185_;
}
}
lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg(lean_object* v_p_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_){
_start:
{
if (lean_obj_tag(v_p_3186_) == 0)
{
lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3197_; 
v_isSharedCheck_3197_ = !lean_is_exclusive(v_p_3186_);
if (v_isSharedCheck_3197_ == 0)
{
lean_object* v_unused_3198_; 
v_unused_3198_ = lean_ctor_get(v_p_3186_, 0);
lean_dec(v_unused_3198_);
v___x_3191_ = v_p_3186_;
v_isShared_3192_ = v_isSharedCheck_3197_;
goto v_resetjp_3190_;
}
else
{
lean_dec(v_p_3186_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3197_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; lean_object* v___x_3195_; 
v___x_3193_ = lean_box(0);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 0, v___x_3193_);
v___x_3195_ = v___x_3191_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3193_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
else
{
lean_object* v_k_3199_; lean_object* v_v_3200_; lean_object* v_p_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v_k_3199_ = lean_ctor_get(v_p_3186_, 0);
lean_inc(v_k_3199_);
v_v_3200_ = lean_ctor_get(v_p_3186_, 1);
lean_inc(v_v_3200_);
v_p_3201_ = lean_ctor_get(v_p_3186_, 2);
lean_inc_ref(v_p_3201_);
lean_dec_ref_known(v_p_3186_, 3);
v___x_3202_ = lean_box(0);
v___x_3203_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3187_, v_a_3188_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3229_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3206_ = v___x_3203_;
v_isShared_3207_ = v_isSharedCheck_3229_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3229_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___y_3209_; lean_object* v_elimEqs_3224_; lean_object* v_size_3225_; uint8_t v___x_3226_; 
v_elimEqs_3224_ = lean_ctor_get(v_a_3204_, 9);
lean_inc_ref(v_elimEqs_3224_);
lean_dec(v_a_3204_);
v_size_3225_ = lean_ctor_get(v_elimEqs_3224_, 2);
v___x_3226_ = lean_nat_dec_lt(v_v_3200_, v_size_3225_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; 
lean_dec_ref(v_elimEqs_3224_);
v___x_3227_ = l_outOfBounds___redArg(v___x_3202_);
v___y_3209_ = v___x_3227_;
goto v___jp_3208_;
}
else
{
lean_object* v___x_3228_; 
v___x_3228_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3202_, v_elimEqs_3224_, v_v_3200_);
lean_dec_ref(v_elimEqs_3224_);
v___y_3209_ = v___x_3228_;
goto v___jp_3208_;
}
v___jp_3208_:
{
if (lean_obj_tag(v___y_3209_) == 1)
{
lean_object* v_val_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3222_; 
lean_dec_ref(v_p_3201_);
v_val_3210_ = lean_ctor_get(v___y_3209_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___y_3209_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3212_ = v___y_3209_;
v_isShared_3213_ = v_isSharedCheck_3222_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_val_3210_);
lean_dec(v___y_3209_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3222_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3217_; 
v___x_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3214_, 0, v_v_3200_);
lean_ctor_set(v___x_3214_, 1, v_val_3210_);
v___x_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3215_, 0, v_k_3199_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v___x_3215_);
v___x_3217_ = v___x_3212_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3215_);
v___x_3217_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
lean_object* v___x_3219_; 
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3217_);
v___x_3219_ = v___x_3206_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
else
{
lean_dec(v___y_3209_);
lean_del_object(v___x_3206_);
lean_dec(v_v_3200_);
lean_dec(v_k_3199_);
v_p_3186_ = v_p_3201_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec_ref(v_p_3201_);
lean_dec(v_v_3200_);
lean_dec(v_k_3199_);
v_a_3230_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3203_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3203_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_findVarToSubst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3186_ = stack[0].m_obj;
lean_object* v_a_3187_ = stack[1].m_obj;
lean_object* v_a_3188_ = stack[2].m_obj;
lean_object* v_res_3238_;
v_res_3238_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_3186_, v_a_3187_, v_a_3188_);
stack->m_obj
 = v_res_3238_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg___boxed(lean_object* v_p_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_3239_, v_a_3240_, v_a_3241_);
lean_dec_ref(v_a_3241_);
lean_dec(v_a_3240_);
return v_res_3243_;
}
}
lean_object* l_Int_Internal_Linear_Poly_findVarToSubst(lean_object* v_p_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_){
_start:
{
lean_object* v___x_3256_; 
v___x_3256_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_3244_, v_a_3245_, v_a_3253_);
return v___x_3256_;
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_findVarToSubst_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3244_ = stack[0].m_obj;
lean_object* v_a_3245_ = stack[1].m_obj;
lean_object* v_a_3246_ = stack[2].m_obj;
lean_object* v_a_3247_ = stack[3].m_obj;
lean_object* v_a_3248_ = stack[4].m_obj;
lean_object* v_a_3249_ = stack[5].m_obj;
lean_object* v_a_3250_ = stack[6].m_obj;
lean_object* v_a_3251_ = stack[7].m_obj;
lean_object* v_a_3252_ = stack[8].m_obj;
lean_object* v_a_3253_ = stack[9].m_obj;
lean_object* v_a_3254_ = stack[10].m_obj;
lean_object* v_res_3257_;
v_res_3257_ = l_Int_Internal_Linear_Poly_findVarToSubst(v_p_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_);
stack->m_obj
 = v_res_3257_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___boxed(lean_object* v_p_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Int_Internal_Linear_Poly_findVarToSubst(v_p_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_);
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
lean_dec(v_a_3264_);
lean_dec_ref(v_a_3263_);
lean_dec(v_a_3262_);
lean_dec_ref(v_a_3261_);
lean_dec(v_a_3260_);
lean_dec(v_a_3259_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(lean_object* v_pred_3271_){
_start:
{
lean_object* v_c_u2081_3272_; lean_object* v_c_u2082_3273_; uint8_t v_left_3274_; lean_object* v_c_u2083_x3f_3275_; lean_object* v_p_3276_; lean_object* v_p_3277_; lean_object* v_a_3278_; lean_object* v_b_3279_; 
v_c_u2081_3272_ = lean_ctor_get(v_pred_3271_, 0);
v_c_u2082_3273_ = lean_ctor_get(v_pred_3271_, 1);
v_left_3274_ = lean_ctor_get_uint8(v_pred_3271_, sizeof(void*)*3);
v_c_u2083_x3f_3275_ = lean_ctor_get(v_pred_3271_, 2);
v_p_3276_ = lean_ctor_get(v_c_u2081_3272_, 0);
v_p_3277_ = lean_ctor_get(v_c_u2082_3273_, 0);
v_a_3278_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3276_);
v_b_3279_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3277_);
if (lean_obj_tag(v_c_u2083_x3f_3275_) == 0)
{
if (v_left_3274_ == 0)
{
lean_object* v___x_3280_; 
lean_dec(v_a_3278_);
v___x_3280_ = lean_nat_abs(v_b_3279_);
lean_dec(v_b_3279_);
return v___x_3280_;
}
else
{
lean_object* v___x_3281_; 
lean_dec(v_b_3279_);
v___x_3281_ = lean_nat_abs(v_a_3278_);
lean_dec(v_a_3278_);
return v___x_3281_;
}
}
else
{
lean_object* v_val_3282_; lean_object* v_d_3283_; lean_object* v_p_3284_; lean_object* v_c_3285_; 
v_val_3282_ = lean_ctor_get(v_c_u2083_x3f_3275_, 0);
v_d_3283_ = lean_ctor_get(v_val_3282_, 0);
v_p_3284_ = lean_ctor_get(v_val_3282_, 1);
v_c_3285_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3284_);
if (v_left_3274_ == 0)
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_dec(v_a_3278_);
v___x_3286_ = lean_int_mul(v_b_3279_, v_d_3283_);
v___x_3287_ = l_Int_gcd(v___x_3286_, v_c_3285_);
lean_dec(v_c_3285_);
v___x_3288_ = lean_nat_to_int(v___x_3287_);
v___x_3289_ = lean_int_ediv(v___x_3286_, v___x_3288_);
lean_dec(v___x_3288_);
lean_dec(v___x_3286_);
v___x_3290_ = l_Int_lcm(v_b_3279_, v___x_3289_);
lean_dec(v___x_3289_);
lean_dec(v_b_3279_);
return v___x_3290_;
}
else
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
lean_dec(v_b_3279_);
v___x_3291_ = lean_int_mul(v_a_3278_, v_d_3283_);
v___x_3292_ = l_Int_gcd(v___x_3291_, v_c_3285_);
lean_dec(v_c_3285_);
v___x_3293_ = lean_nat_to_int(v___x_3292_);
v___x_3294_ = lean_int_ediv(v___x_3291_, v___x_3293_);
lean_dec(v___x_3293_);
lean_dec(v___x_3291_);
v___x_3295_ = l_Int_lcm(v_a_3278_, v___x_3294_);
lean_dec(v___x_3294_);
lean_dec(v_a_3278_);
return v___x_3295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases___boxed(lean_object* v_pred_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(v_pred_3296_);
lean_dec_ref(v_pred_3296_);
return v_res_3297_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0));
v___x_3300_ = l_Lean_stringToMessageData(v___x_3299_);
return v___x_3300_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4(void){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3));
v___x_3305_ = l_Lean_MessageData_ofFormat(v___x_3304_);
return v___x_3305_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(lean_object* v_pred_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
lean_object* v_c_u2081_3310_; lean_object* v_c_u2082_3311_; lean_object* v_c_u2083_x3f_3312_; lean_object* v___x_3313_; 
v_c_u2081_3310_ = lean_ctor_get(v_pred_3306_, 0);
lean_inc_ref(v_c_u2081_3310_);
v_c_u2082_3311_ = lean_ctor_get(v_pred_3306_, 1);
lean_inc_ref(v_c_u2082_3311_);
v_c_u2083_x3f_3312_ = lean_ctor_get(v_pred_3306_, 2);
lean_inc(v_c_u2083_x3f_3312_);
lean_dec_ref(v_pred_3306_);
v___x_3313_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3310_, v_a_3307_, v_a_3308_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3315_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3314_);
lean_dec_ref_known(v___x_3313_, 1);
v___x_3315_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3311_, v_a_3307_, v_a_3308_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3334_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3318_ = v___x_3315_;
v_isShared_3319_ = v_isSharedCheck_3334_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3315_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3334_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v_____do__lift_3321_; 
if (lean_obj_tag(v_c_u2083_x3f_3312_) == 1)
{
lean_object* v_val_3330_; lean_object* v___x_3331_; 
v_val_3330_ = lean_ctor_get(v_c_u2083_x3f_3312_, 0);
lean_inc(v_val_3330_);
lean_dec_ref_known(v_c_u2083_x3f_3312_, 1);
v___x_3331_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_val_3330_, v_a_3307_, v_a_3308_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v_a_3332_; 
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
lean_inc(v_a_3332_);
lean_dec_ref_known(v___x_3331_, 1);
v_____do__lift_3321_ = v_a_3332_;
goto v___jp_3320_;
}
else
{
lean_del_object(v___x_3318_);
lean_dec(v_a_3316_);
lean_dec(v_a_3314_);
return v___x_3331_;
}
}
else
{
lean_object* v___x_3333_; 
lean_dec(v_c_u2083_x3f_3312_);
v___x_3333_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4);
v_____do__lift_3321_ = v___x_3333_;
goto v___jp_3320_;
}
v___jp_3320_:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3328_; 
v___x_3322_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3323_, 0, v_a_3314_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
v___x_3324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
lean_ctor_set(v___x_3324_, 1, v_a_3316_);
v___x_3325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
lean_ctor_set(v___x_3325_, 1, v___x_3322_);
v___x_3326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
lean_ctor_set(v___x_3326_, 1, v_____do__lift_3321_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 0, v___x_3326_);
v___x_3328_ = v___x_3318_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3326_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
else
{
lean_dec(v_a_3314_);
lean_dec(v_c_u2083_x3f_3312_);
return v___x_3315_;
}
}
else
{
lean_dec(v_c_u2083_x3f_3312_);
lean_dec_ref(v_c_u2082_3311_);
return v___x_3313_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_pred_3306_ = stack[0].m_obj;
lean_object* v_a_3307_ = stack[1].m_obj;
lean_object* v_a_3308_ = stack[2].m_obj;
lean_object* v_res_3335_;
v_res_3335_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_3306_, v_a_3307_, v_a_3308_);
stack->m_obj
 = v_res_3335_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___boxed(lean_object* v_pred_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_3336_, v_a_3337_, v_a_3338_);
lean_dec_ref(v_a_3338_);
lean_dec(v_a_3337_);
return v_res_3340_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(lean_object* v_pred_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
lean_object* v___x_3353_; 
v___x_3353_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_3341_, v_a_3342_, v_a_3350_);
return v___x_3353_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp_0interp(lean_interpreter_value* stack)
{
lean_object* v_pred_3341_ = stack[0].m_obj;
lean_object* v_a_3342_ = stack[1].m_obj;
lean_object* v_a_3343_ = stack[2].m_obj;
lean_object* v_a_3344_ = stack[3].m_obj;
lean_object* v_a_3345_ = stack[4].m_obj;
lean_object* v_a_3346_ = stack[5].m_obj;
lean_object* v_a_3347_ = stack[6].m_obj;
lean_object* v_a_3348_ = stack[7].m_obj;
lean_object* v_a_3349_ = stack[8].m_obj;
lean_object* v_a_3350_ = stack[9].m_obj;
lean_object* v_a_3351_ = stack[10].m_obj;
lean_object* v_res_3354_;
v_res_3354_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(v_pred_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
stack->m_obj
 = v_res_3354_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___boxed(lean_object* v_pred_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(v_pred_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_);
lean_dec(v_a_3365_);
lean_dec_ref(v_a_3364_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
lean_dec(v_a_3361_);
lean_dec_ref(v_a_3360_);
lean_dec(v_a_3359_);
lean_dec_ref(v_a_3358_);
lean_dec(v_a_3357_);
lean_dec(v_a_3356_);
return v_res_3367_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(lean_object* v_h_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
switch(lean_obj_tag(v_h_3368_))
{
case 0:
{
lean_object* v_c_3372_; lean_object* v___x_3373_; 
v_c_3372_ = lean_ctor_get(v_h_3368_, 0);
lean_inc_ref(v_c_3372_);
lean_dec_ref_known(v_h_3368_, 1);
v___x_3373_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_3372_, v_a_3369_, v_a_3370_);
return v___x_3373_;
}
case 1:
{
lean_object* v_c_3374_; lean_object* v___x_3375_; 
v_c_3374_ = lean_ctor_get(v_h_3368_, 0);
lean_inc_ref(v_c_3374_);
lean_dec_ref_known(v_h_3368_, 1);
v___x_3375_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3374_, v_a_3369_, v_a_3370_);
return v___x_3375_;
}
case 2:
{
lean_object* v_c_3376_; lean_object* v___x_3377_; 
v_c_3376_ = lean_ctor_get(v_h_3368_, 0);
lean_inc_ref(v_c_3376_);
lean_dec_ref_known(v_h_3368_, 1);
v___x_3377_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_3376_, v_a_3369_, v_a_3370_);
return v___x_3377_;
}
case 3:
{
lean_object* v_c_3378_; lean_object* v___x_3379_; 
v_c_3378_ = lean_ctor_get(v_h_3368_, 0);
lean_inc_ref(v_c_3378_);
lean_dec_ref_known(v_h_3368_, 1);
v___x_3379_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_3378_, v_a_3369_, v_a_3370_);
return v___x_3379_;
}
default: 
{
lean_object* v_c_u2081_3380_; lean_object* v_c_u2082_3381_; lean_object* v_c_u2083_3382_; lean_object* v___x_3383_; 
v_c_u2081_3380_ = lean_ctor_get(v_h_3368_, 0);
lean_inc_ref(v_c_u2081_3380_);
v_c_u2082_3381_ = lean_ctor_get(v_h_3368_, 1);
lean_inc_ref(v_c_u2082_3381_);
v_c_u2083_3382_ = lean_ctor_get(v_h_3368_, 2);
lean_inc_ref(v_c_u2083_3382_);
lean_dec_ref_known(v_h_3368_, 3);
v___x_3383_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3380_, v_a_3369_, v_a_3370_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; lean_object* v___x_3385_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_a_3384_);
lean_dec_ref_known(v___x_3383_, 1);
v___x_3385_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3381_, v_a_3369_, v_a_3370_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3387_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3386_);
lean_dec_ref_known(v___x_3385_, 1);
v___x_3387_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2083_3382_, v_a_3369_, v_a_3370_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3400_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3390_ = v___x_3387_;
v_isShared_3391_ = v_isSharedCheck_3400_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3387_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3400_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3398_; 
v___x_3392_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3393_, 0, v_a_3384_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
v___x_3394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
lean_ctor_set(v___x_3394_, 1, v_a_3386_);
v___x_3395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
lean_ctor_set(v___x_3395_, 1, v___x_3392_);
v___x_3396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
lean_ctor_set(v___x_3396_, 1, v_a_3388_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 0, v___x_3396_);
v___x_3398_ = v___x_3390_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3396_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
else
{
lean_dec(v_a_3386_);
lean_dec(v_a_3384_);
return v___x_3387_;
}
}
else
{
lean_dec(v_a_3384_);
lean_dec_ref(v_c_u2083_3382_);
return v___x_3385_;
}
}
else
{
lean_dec_ref(v_c_u2083_3382_);
lean_dec_ref(v_c_u2082_3381_);
return v___x_3383_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3368_ = stack[0].m_obj;
lean_object* v_a_3369_ = stack[1].m_obj;
lean_object* v_a_3370_ = stack[2].m_obj;
lean_object* v_res_3401_;
v_res_3401_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3368_, v_a_3369_, v_a_3370_);
stack->m_obj
 = v_res_3401_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg___boxed(lean_object* v_h_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3402_, v_a_3403_, v_a_3404_);
lean_dec_ref(v_a_3404_);
lean_dec(v_a_3403_);
return v_res_3406_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(lean_object* v_h_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_){
_start:
{
lean_object* v___x_3419_; 
v___x_3419_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3407_, v_a_3408_, v_a_3416_);
return v___x_3419_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_3407_ = stack[0].m_obj;
lean_object* v_a_3408_ = stack[1].m_obj;
lean_object* v_a_3409_ = stack[2].m_obj;
lean_object* v_a_3410_ = stack[3].m_obj;
lean_object* v_a_3411_ = stack[4].m_obj;
lean_object* v_a_3412_ = stack[5].m_obj;
lean_object* v_a_3413_ = stack[6].m_obj;
lean_object* v_a_3414_ = stack[7].m_obj;
lean_object* v_a_3415_ = stack[8].m_obj;
lean_object* v_a_3416_ = stack[9].m_obj;
lean_object* v_a_3417_ = stack[10].m_obj;
lean_object* v_res_3420_;
v_res_3420_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(v_h_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
stack->m_obj
 = v_res_3420_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___boxed(lean_object* v_h_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(v_h_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec(v_a_3427_);
lean_dec_ref(v_a_3426_);
lean_dec(v_a_3425_);
lean_dec_ref(v_a_3424_);
lean_dec(v_a_3423_);
lean_dec(v_a_3422_);
return v_res_3433_;
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
