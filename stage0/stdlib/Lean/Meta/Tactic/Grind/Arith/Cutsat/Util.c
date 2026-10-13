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
uint8_t v___y_149_; uint8_t v___x_250_; 
v___x_250_ = l_Lean_Meta_Grind_Arith_isNatType(v_type_145_);
if (v___x_250_ == 0)
{
uint8_t v___x_251_; 
v___x_251_ = l_Lean_Meta_Grind_Arith_isIntType(v_type_145_);
v___y_149_ = v___x_251_;
goto v___jp_148_;
}
else
{
v___y_149_ = v___x_250_;
goto v___jp_148_;
}
v___jp_148_:
{
uint8_t v___x_150_; 
v___x_150_ = 1;
if (v___y_149_ == 0)
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_type_145_, v_a_146_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_239_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_239_ == 0)
{
v___x_154_ = v___x_151_;
v_isShared_155_ = v_isSharedCheck_239_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_239_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_156_ = l_Lean_Expr_cleanupAnnotations(v_a_152_);
v___x_157_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__1));
v___x_158_ = l_Lean_Expr_isConstOf(v___x_156_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__3));
v___x_160_ = l_Lean_Expr_isConstOf(v___x_156_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__5));
v___x_162_ = l_Lean_Expr_isConstOf(v___x_156_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__7));
v___x_164_ = l_Lean_Expr_isConstOf(v___x_156_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__9));
v___x_166_ = l_Lean_Expr_isConstOf(v___x_156_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__11));
v___x_168_ = l_Lean_Expr_isConstOf(v___x_156_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__13));
v___x_170_ = l_Lean_Expr_isConstOf(v___x_156_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__15));
v___x_172_ = l_Lean_Expr_isConstOf(v___x_156_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__17));
v___x_174_ = l_Lean_Expr_isConstOf(v___x_156_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__19));
v___x_176_ = l_Lean_Expr_isConstOf(v___x_156_, v___x_175_);
if (v___x_176_ == 0)
{
uint8_t v___x_177_; 
v___x_177_ = l_Lean_Expr_isApp(v___x_156_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; lean_object* v___x_180_; 
lean_dec_ref(v___x_156_);
v___x_178_ = lean_box(v___y_149_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_178_);
v___x_180_ = v___x_154_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_182_ = l_Lean_Expr_appFnCleanup___redArg(v___x_156_);
v___x_183_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__21));
v___x_184_ = l_Lean_Expr_isConstOf(v___x_182_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_185_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__23));
v___x_186_ = l_Lean_Expr_isConstOf(v___x_182_, v___x_185_);
lean_dec_ref(v___x_182_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = lean_box(v___y_149_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_187_);
v___x_189_ = v___x_154_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
else
{
lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_191_ = lean_box(v___x_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_191_);
v___x_193_ = v___x_154_;
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
}
else
{
lean_object* v___x_195_; lean_object* v___x_197_; 
lean_dec_ref(v___x_182_);
v___x_195_ = lean_box(v___x_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_195_);
v___x_197_ = v___x_154_;
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
}
else
{
lean_object* v___x_199_; lean_object* v___x_201_; 
lean_dec_ref(v___x_156_);
v___x_199_ = lean_box(v___x_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_199_);
v___x_201_ = v___x_154_;
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
else
{
lean_object* v___x_203_; lean_object* v___x_205_; 
lean_dec_ref(v___x_156_);
v___x_203_ = lean_box(v___x_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_203_);
v___x_205_ = v___x_154_;
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
lean_dec_ref(v___x_156_);
v___x_207_ = lean_box(v___x_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_207_);
v___x_209_ = v___x_154_;
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
lean_dec_ref(v___x_156_);
v___x_211_ = lean_box(v___x_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_211_);
v___x_213_ = v___x_154_;
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
lean_dec_ref(v___x_156_);
v___x_215_ = lean_box(v___x_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_215_);
v___x_217_ = v___x_154_;
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
lean_dec_ref(v___x_156_);
v___x_219_ = lean_box(v___x_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_219_);
v___x_221_ = v___x_154_;
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
lean_dec_ref(v___x_156_);
v___x_223_ = lean_box(v___x_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_223_);
v___x_225_ = v___x_154_;
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
lean_dec_ref(v___x_156_);
v___x_227_ = lean_box(v___x_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_227_);
v___x_229_ = v___x_154_;
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
lean_dec_ref(v___x_156_);
v___x_231_ = lean_box(v___x_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_231_);
v___x_233_ = v___x_154_;
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
lean_dec_ref(v___x_156_);
v___x_235_ = lean_box(v___x_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_235_);
v___x_237_ = v___x_154_;
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
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
v_a_240_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_151_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_151_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec_ref(v_type_145_);
v___x_248_ = lean_box(v___x_150_);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg(lean_object* v_00_u03b1_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_292_ = l_Lean_Expr_cleanupAnnotations(v_00_u03b1_282_);
v___x_293_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__3));
v___x_294_ = l_Lean_Expr_isConstOf(v___x_292_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__5));
v___x_296_ = l_Lean_Expr_isConstOf(v___x_292_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__7));
v___x_298_ = l_Lean_Expr_isConstOf(v___x_292_, v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__9));
v___x_300_ = l_Lean_Expr_isConstOf(v___x_292_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__13));
v___x_302_ = l_Lean_Expr_isConstOf(v___x_292_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__15));
v___x_304_ = l_Lean_Expr_isConstOf(v___x_292_, v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__17));
v___x_306_ = l_Lean_Expr_isConstOf(v___x_292_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__19));
v___x_308_ = l_Lean_Expr_isConstOf(v___x_292_, v___x_307_);
if (v___x_308_ == 0)
{
uint8_t v___x_309_; 
v___x_309_ = l_Lean_Expr_isApp(v___x_292_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec_ref(v___x_292_);
v___x_310_ = lean_box(v___x_308_);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
else
{
lean_object* v_arg_312_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_arg_312_ = lean_ctor_get(v___x_292_, 1);
lean_inc_ref(v_arg_312_);
v___x_340_ = l_Lean_Expr_appFnCleanup___redArg(v___x_292_);
v___x_341_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__21));
v___x_342_ = l_Lean_Expr_isConstOf(v___x_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isSupportedType___redArg___closed__23));
v___x_344_ = l_Lean_Expr_isConstOf(v___x_340_, v___x_343_);
lean_dec_ref(v___x_340_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec_ref(v_arg_312_);
v___x_345_ = lean_box(v___x_308_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
else
{
v___y_314_ = v_a_283_;
v___y_315_ = v_a_284_;
v___y_316_ = v_a_285_;
v___y_317_ = v_a_286_;
goto v___jp_313_;
}
}
else
{
lean_dec_ref(v___x_340_);
v___y_314_ = v_a_283_;
v___y_315_ = v_a_284_;
v___y_316_ = v_a_285_;
v___y_317_ = v_a_286_;
goto v___jp_313_;
}
v___jp_313_:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Meta_getNatValue_x3f(v_arg_312_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec_ref(v_arg_312_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_331_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_331_ == 0)
{
v___x_321_ = v___x_318_;
v_isShared_322_ = v_isSharedCheck_331_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_318_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_331_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
if (lean_obj_tag(v_a_319_) == 0)
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = lean_box(v___x_308_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_323_);
v___x_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
else
{
lean_object* v___x_327_; lean_object* v___x_329_; 
lean_dec_ref_known(v_a_319_, 1);
v___x_327_ = lean_box(v___x_309_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_327_);
v___x_329_ = v___x_321_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
v_a_332_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_318_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_318_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_292_);
goto v___jp_288_;
}
}
else
{
lean_dec_ref(v___x_292_);
goto v___jp_288_;
}
}
else
{
lean_dec_ref(v___x_292_);
goto v___jp_288_;
}
}
else
{
lean_dec_ref(v___x_292_);
goto v___jp_288_;
}
}
else
{
lean_dec_ref(v___x_292_);
goto v___jp_288_;
}
}
else
{
lean_dec_ref(v___x_292_);
goto v___jp_288_;
}
}
else
{
lean_dec_ref(v___x_292_);
goto v___jp_288_;
}
}
else
{
lean_dec_ref(v___x_292_);
goto v___jp_288_;
}
v___jp_288_:
{
uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = 1;
v___x_290_ = lean_box(v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg___boxed(lean_object* v_00_u03b1_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg(v_00_u03b1_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated(lean_object* v_00_u03b1_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___redArg(v_00_u03b1_354_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated___boxed(lean_object* v_00_u03b1_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Meta_Grind_Arith_Cutsat_canBeEvaluated(v_00_u03b1_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec(v_a_368_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_380_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; uint8_t v___x_385_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
v___x_385_ = lean_unbox(v_a_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
lean_inc(v_a_384_);
lean_dec_ref_known(v___x_383_, 1);
v___x_386_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_380_, v_a_381_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_400_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_400_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_400_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_400_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v_conflict_x3f_391_; 
v_conflict_x3f_391_ = lean_ctor_get(v_a_387_, 15);
lean_inc(v_conflict_x3f_391_);
lean_dec(v_a_387_);
if (lean_obj_tag(v_conflict_x3f_391_) == 0)
{
lean_object* v___x_393_; 
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v_a_384_);
v___x_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_384_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
else
{
uint8_t v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
lean_dec_ref_known(v_conflict_x3f_391_, 1);
lean_dec(v_a_384_);
v___x_395_ = 1;
v___x_396_ = lean_box(v___x_395_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_396_);
v___x_398_ = v___x_389_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
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
lean_dec(v_a_384_);
v_a_401_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_386_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_386_);
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
return v___x_383_;
}
}
else
{
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg___boxed(lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_409_, v_a_410_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_413_, v_a_421_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___boxed(lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec(v_a_426_);
lean_dec(v_a_425_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVar___boxed(lean_object* v_e_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_00___x40___internal___hyg_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = lean_grind_cutsat_mk_var(v_e_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(lean_object* v_a_462_, lean_object* v_a_463_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_462_, v_a_463_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_474_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_474_ == 0)
{
v___x_468_ = v___x_465_;
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_465_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v_vars_470_; lean_object* v___x_472_; 
v_vars_470_ = lean_ctor_get(v_a_466_, 0);
lean_inc_ref(v_vars_470_);
lean_dec(v_a_466_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v_vars_470_);
v___x_472_ = v___x_468_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_vars_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
v_a_475_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_465_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_465_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg___boxed(lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_483_, v_a_484_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars(lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_487_, v_a_495_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___boxed(lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars(v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec(v_a_499_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object* v_x_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = l_Lean_instInhabitedExpr;
v___x_516_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_512_, v_a_513_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_532_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_532_ == 0)
{
v___x_519_ = v___x_516_;
v_isShared_520_ = v_isSharedCheck_532_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_532_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_vars_521_; lean_object* v_size_522_; uint8_t v___x_523_; 
v_vars_521_ = lean_ctor_get(v_a_517_, 0);
lean_inc_ref(v_vars_521_);
lean_dec(v_a_517_);
v_size_522_ = lean_ctor_get(v_vars_521_, 2);
v___x_523_ = lean_nat_dec_lt(v_x_511_, v_size_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_526_; 
lean_dec_ref(v_vars_521_);
v___x_524_ = l_outOfBounds___redArg(v___x_515_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_524_);
v___x_526_ = v___x_519_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
else
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = l_Lean_PersistentArray_get_x21___redArg(v___x_515_, v_vars_521_, v_x_511_);
lean_dec_ref(v_vars_521_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_528_);
v___x_530_ = v___x_519_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
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
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
v_a_533_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_516_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_516_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg___boxed(lean_object* v_x_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_541_, v_a_542_, v_a_543_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec(v_x_541_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar(lean_object* v_x_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_546_, v_a_547_, v_a_555_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___boxed(lean_object* v_x_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar(v_x_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec(v_a_560_);
lean_dec(v_x_559_);
return v_res_571_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_572_, lean_object* v_i_573_, lean_object* v_k_574_){
_start:
{
lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_575_ = lean_array_get_size(v_keys_572_);
v___x_576_ = lean_nat_dec_lt(v_i_573_, v___x_575_);
if (v___x_576_ == 0)
{
lean_dec(v_i_573_);
return v___x_576_;
}
else
{
lean_object* v_k_x27_577_; size_t v___x_578_; size_t v___x_579_; uint8_t v___x_580_; 
v_k_x27_577_ = lean_array_fget_borrowed(v_keys_572_, v_i_573_);
v___x_578_ = lean_ptr_addr(v_k_574_);
v___x_579_ = lean_ptr_addr(v_k_x27_577_);
v___x_580_ = lean_usize_dec_eq(v___x_578_, v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = lean_nat_add(v_i_573_, v___x_581_);
lean_dec(v_i_573_);
v_i_573_ = v___x_582_;
goto _start;
}
else
{
lean_dec(v_i_573_);
return v___x_576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_584_, lean_object* v_i_585_, lean_object* v_k_586_){
_start:
{
uint8_t v_res_587_; lean_object* v_r_588_; 
v_res_587_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_584_, v_i_585_, v_k_586_);
lean_dec_ref(v_k_586_);
lean_dec_ref(v_keys_584_);
v_r_588_ = lean_box(v_res_587_);
return v_r_588_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(lean_object* v_x_589_, size_t v_x_590_, lean_object* v_x_591_){
_start:
{
if (lean_obj_tag(v_x_589_) == 0)
{
lean_object* v_es_592_; lean_object* v___x_593_; size_t v___x_594_; size_t v___x_595_; lean_object* v_j_596_; lean_object* v___x_597_; 
v_es_592_ = lean_ctor_get(v_x_589_, 0);
v___x_593_ = lean_box(2);
v___x_594_ = ((size_t)31ULL);
v___x_595_ = lean_usize_land(v_x_590_, v___x_594_);
v_j_596_ = lean_usize_to_nat(v___x_595_);
v___x_597_ = lean_array_get_borrowed(v___x_593_, v_es_592_, v_j_596_);
lean_dec(v_j_596_);
switch(lean_obj_tag(v___x_597_))
{
case 0:
{
lean_object* v_key_598_; size_t v___x_599_; size_t v___x_600_; uint8_t v___x_601_; 
v_key_598_ = lean_ctor_get(v___x_597_, 0);
v___x_599_ = lean_ptr_addr(v_x_591_);
v___x_600_ = lean_ptr_addr(v_key_598_);
v___x_601_ = lean_usize_dec_eq(v___x_599_, v___x_600_);
return v___x_601_;
}
case 1:
{
lean_object* v_node_602_; size_t v___x_603_; size_t v___x_604_; 
v_node_602_ = lean_ctor_get(v___x_597_, 0);
v___x_603_ = ((size_t)5ULL);
v___x_604_ = lean_usize_shift_right(v_x_590_, v___x_603_);
v_x_589_ = v_node_602_;
v_x_590_ = v___x_604_;
goto _start;
}
default: 
{
uint8_t v___x_606_; 
v___x_606_ = 0;
return v___x_606_;
}
}
}
else
{
lean_object* v_ks_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v_ks_607_ = lean_ctor_get(v_x_589_, 0);
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_ks_607_, v___x_608_, v_x_591_);
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___boxed(lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
size_t v_x_889__boxed_613_; uint8_t v_res_614_; lean_object* v_r_615_; 
v_x_889__boxed_613_ = lean_unbox_usize(v_x_611_);
lean_dec(v_x_611_);
v_res_614_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_610_, v_x_889__boxed_613_, v_x_612_);
lean_dec_ref(v_x_612_);
lean_dec_ref(v_x_610_);
v_r_615_ = lean_box(v_res_614_);
return v_r_615_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(lean_object* v_x_616_, lean_object* v_x_617_){
_start:
{
size_t v___x_618_; size_t v___x_619_; size_t v___x_620_; uint64_t v___x_621_; size_t v___x_622_; uint8_t v___x_623_; 
v___x_618_ = lean_ptr_addr(v_x_617_);
v___x_619_ = ((size_t)3ULL);
v___x_620_ = lean_usize_shift_right(v___x_618_, v___x_619_);
v___x_621_ = lean_usize_to_uint64(v___x_620_);
v___x_622_ = lean_uint64_to_usize(v___x_621_);
v___x_623_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_616_, v___x_622_, v_x_617_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg___boxed(lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
uint8_t v_res_626_; lean_object* v_r_627_; 
v_res_626_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_624_, v_x_625_);
lean_dec_ref(v_x_625_);
lean_dec_ref(v_x_624_);
v_r_627_ = lean_box(v_res_626_);
return v_r_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(lean_object* v_e_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_629_, v_a_630_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_643_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_643_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_643_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_643_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v_varMap_637_; uint8_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v_varMap_637_ = lean_ctor_get(v_a_633_, 1);
lean_inc_ref(v_varMap_637_);
lean_dec(v_a_633_);
v___x_638_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_varMap_637_, v_e_628_);
lean_dec_ref(v_varMap_637_);
v___x_639_ = lean_box(v___x_638_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_639_);
v___x_641_ = v___x_635_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
v_a_644_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_632_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_632_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg___boxed(lean_object* v_e_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_652_, v_a_653_, v_a_654_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_e_652_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar(lean_object* v_e_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_657_, v_a_658_, v_a_666_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___boxed(lean_object* v_e_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar(v_e_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_e_670_);
return v_res_682_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(lean_object* v_00_u03b2_683_, lean_object* v_x_684_, lean_object* v_x_685_){
_start:
{
uint8_t v___x_686_; 
v___x_686_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_684_, v_x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___boxed(lean_object* v_00_u03b2_687_, lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
uint8_t v_res_690_; lean_object* v_r_691_; 
v_res_690_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(v_00_u03b2_687_, v_x_688_, v_x_689_);
lean_dec_ref(v_x_689_);
lean_dec_ref(v_x_688_);
v_r_691_ = lean_box(v_res_690_);
return v_r_691_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(lean_object* v_00_u03b2_692_, lean_object* v_x_693_, size_t v_x_694_, lean_object* v_x_695_){
_start:
{
uint8_t v___x_696_; 
v___x_696_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_693_, v_x_694_, v_x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_697_, lean_object* v_x_698_, lean_object* v_x_699_, lean_object* v_x_700_){
_start:
{
size_t v_x_1006__boxed_701_; uint8_t v_res_702_; lean_object* v_r_703_; 
v_x_1006__boxed_701_ = lean_unbox_usize(v_x_699_);
lean_dec(v_x_699_);
v_res_702_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(v_00_u03b2_697_, v_x_698_, v_x_1006__boxed_701_, v_x_700_);
lean_dec_ref(v_x_700_);
lean_dec_ref(v_x_698_);
v_r_703_ = lean_box(v_res_702_);
return v_r_703_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_704_, lean_object* v_keys_705_, lean_object* v_vals_706_, lean_object* v_heq_707_, lean_object* v_i_708_, lean_object* v_k_709_){
_start:
{
uint8_t v___x_710_; 
v___x_710_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_705_, v_i_708_, v_k_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_711_, lean_object* v_keys_712_, lean_object* v_vals_713_, lean_object* v_heq_714_, lean_object* v_i_715_, lean_object* v_k_716_){
_start:
{
uint8_t v_res_717_; lean_object* v_r_718_; 
v_res_717_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(v_00_u03b2_711_, v_keys_712_, v_vals_713_, v_heq_714_, v_i_715_, v_k_716_);
lean_dec_ref(v_k_716_);
lean_dec_ref(v_vals_713_);
lean_dec_ref(v_keys_712_);
v_r_718_ = lean_box(v_res_717_);
return v_r_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(lean_object* v_e_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_719_, v_a_720_, v_a_721_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg___boxed(lean_object* v_e_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(v_e_724_, v_a_725_, v_a_726_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec_ref(v_e_724_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(lean_object* v_e_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_729_, v_a_730_, v_a_738_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___boxed(lean_object* v_e_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(v_e_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
lean_dec(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_e_742_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(lean_object* v_x_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_box(0);
v___x_760_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_756_, v_a_757_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_782_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_782_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_782_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_782_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___y_766_; lean_object* v_elimEqs_777_; lean_object* v_size_778_; uint8_t v___x_779_; 
v_elimEqs_777_ = lean_ctor_get(v_a_761_, 9);
lean_inc_ref(v_elimEqs_777_);
lean_dec(v_a_761_);
v_size_778_ = lean_ctor_get(v_elimEqs_777_, 2);
v___x_779_ = lean_nat_dec_lt(v_x_755_, v_size_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; 
lean_dec_ref(v_elimEqs_777_);
v___x_780_ = l_outOfBounds___redArg(v___x_759_);
v___y_766_ = v___x_780_;
goto v___jp_765_;
}
else
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_PersistentArray_get_x21___redArg(v___x_759_, v_elimEqs_777_, v_x_755_);
lean_dec_ref(v_elimEqs_777_);
v___y_766_ = v___x_781_;
goto v___jp_765_;
}
v___jp_765_:
{
if (lean_obj_tag(v___y_766_) == 0)
{
uint8_t v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_767_ = 0;
v___x_768_ = lean_box(v___x_767_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_768_);
v___x_770_ = v___x_763_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
else
{
uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
lean_dec_ref_known(v___y_766_, 1);
v___x_772_ = 1;
v___x_773_ = lean_box(v___x_772_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_773_);
v___x_775_ = v___x_763_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
v_a_783_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_760_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_760_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg___boxed(lean_object* v_x_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_791_, v_a_792_, v_a_793_);
lean_dec_ref(v_a_793_);
lean_dec(v_a_792_);
lean_dec(v_x_791_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated(lean_object* v_x_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_796_, v_a_797_, v_a_805_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___boxed(lean_object* v_x_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated(v_x_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec(v_a_810_);
lean_dec(v_x_809_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_assert___boxed(lean_object* v_c_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_00___x40___internal___hyg_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = lean_grind_cutsat_assert_eq(v_c_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(lean_object* v_x_847_, lean_object* v_s_848_){
_start:
{
lean_object* v_vars_849_; lean_object* v_varMap_850_; lean_object* v_varsHistory_851_; lean_object* v_natToIntMap_852_; lean_object* v_natDef_853_; lean_object* v_dvds_854_; lean_object* v_lowers_855_; lean_object* v_uppers_856_; lean_object* v_diseqs_857_; lean_object* v_elimEqs_858_; lean_object* v_elimStack_859_; lean_object* v_occurs_860_; lean_object* v_assignment_861_; lean_object* v_nextCnstrId_862_; uint8_t v_caseSplits_863_; lean_object* v_steps_864_; lean_object* v_conflict_x3f_865_; lean_object* v_diseqSplits_866_; lean_object* v_divMod_867_; uint8_t v_usedCommRing_868_; lean_object* v_nonlinearOccs_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_877_; 
v_vars_849_ = lean_ctor_get(v_s_848_, 0);
v_varMap_850_ = lean_ctor_get(v_s_848_, 1);
v_varsHistory_851_ = lean_ctor_get(v_s_848_, 2);
v_natToIntMap_852_ = lean_ctor_get(v_s_848_, 3);
v_natDef_853_ = lean_ctor_get(v_s_848_, 4);
v_dvds_854_ = lean_ctor_get(v_s_848_, 5);
v_lowers_855_ = lean_ctor_get(v_s_848_, 6);
v_uppers_856_ = lean_ctor_get(v_s_848_, 7);
v_diseqs_857_ = lean_ctor_get(v_s_848_, 8);
v_elimEqs_858_ = lean_ctor_get(v_s_848_, 9);
v_elimStack_859_ = lean_ctor_get(v_s_848_, 10);
v_occurs_860_ = lean_ctor_get(v_s_848_, 11);
v_assignment_861_ = lean_ctor_get(v_s_848_, 12);
v_nextCnstrId_862_ = lean_ctor_get(v_s_848_, 13);
v_caseSplits_863_ = lean_ctor_get_uint8(v_s_848_, sizeof(void*)*19);
v_steps_864_ = lean_ctor_get(v_s_848_, 14);
v_conflict_x3f_865_ = lean_ctor_get(v_s_848_, 15);
v_diseqSplits_866_ = lean_ctor_get(v_s_848_, 16);
v_divMod_867_ = lean_ctor_get(v_s_848_, 17);
v_usedCommRing_868_ = lean_ctor_get_uint8(v_s_848_, sizeof(void*)*19 + 1);
v_nonlinearOccs_869_ = lean_ctor_get(v_s_848_, 18);
v_isSharedCheck_877_ = !lean_is_exclusive(v_s_848_);
if (v_isSharedCheck_877_ == 0)
{
v___x_871_ = v_s_848_;
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_nonlinearOccs_869_);
lean_inc(v_divMod_867_);
lean_inc(v_diseqSplits_866_);
lean_inc(v_conflict_x3f_865_);
lean_inc(v_steps_864_);
lean_inc(v_nextCnstrId_862_);
lean_inc(v_assignment_861_);
lean_inc(v_occurs_860_);
lean_inc(v_elimStack_859_);
lean_inc(v_elimEqs_858_);
lean_inc(v_diseqs_857_);
lean_inc(v_uppers_856_);
lean_inc(v_lowers_855_);
lean_inc(v_dvds_854_);
lean_inc(v_natDef_853_);
lean_inc(v_natToIntMap_852_);
lean_inc(v_varsHistory_851_);
lean_inc(v_varMap_850_);
lean_inc(v_vars_849_);
lean_dec(v_s_848_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_877_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_861_, v_x_847_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 12, v___x_873_);
v___x_875_ = v___x_871_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_vars_849_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_varMap_850_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v_varsHistory_851_);
lean_ctor_set(v_reuseFailAlloc_876_, 3, v_natToIntMap_852_);
lean_ctor_set(v_reuseFailAlloc_876_, 4, v_natDef_853_);
lean_ctor_set(v_reuseFailAlloc_876_, 5, v_dvds_854_);
lean_ctor_set(v_reuseFailAlloc_876_, 6, v_lowers_855_);
lean_ctor_set(v_reuseFailAlloc_876_, 7, v_uppers_856_);
lean_ctor_set(v_reuseFailAlloc_876_, 8, v_diseqs_857_);
lean_ctor_set(v_reuseFailAlloc_876_, 9, v_elimEqs_858_);
lean_ctor_set(v_reuseFailAlloc_876_, 10, v_elimStack_859_);
lean_ctor_set(v_reuseFailAlloc_876_, 11, v_occurs_860_);
lean_ctor_set(v_reuseFailAlloc_876_, 12, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_876_, 13, v_nextCnstrId_862_);
lean_ctor_set(v_reuseFailAlloc_876_, 14, v_steps_864_);
lean_ctor_set(v_reuseFailAlloc_876_, 15, v_conflict_x3f_865_);
lean_ctor_set(v_reuseFailAlloc_876_, 16, v_diseqSplits_866_);
lean_ctor_set(v_reuseFailAlloc_876_, 17, v_divMod_867_);
lean_ctor_set(v_reuseFailAlloc_876_, 18, v_nonlinearOccs_869_);
lean_ctor_set_uint8(v_reuseFailAlloc_876_, sizeof(void*)*19, v_caseSplits_863_);
lean_ctor_set_uint8(v_reuseFailAlloc_876_, sizeof(void*)*19 + 1, v_usedCommRing_868_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_x_878_, lean_object* v_s_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(v_x_878_, v_s_879_);
lean_dec(v_x_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object* v_x_881_, lean_object* v_a_882_){
_start:
{
lean_object* v___f_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___f_884_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_884_, 0, v_x_881_);
v___x_885_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_886_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_885_, v___f_884_, v_a_882_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___boxed(lean_object* v_x_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_887_, v_a_888_);
lean_dec(v_a_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(lean_object* v_x_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_891_, v_a_892_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___boxed(lean_object* v_x_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(v_x_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec(v_a_905_);
return v_res_916_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__0));
v___x_919_ = l_Lean_stringToMessageData(v___x_918_);
return v___x_919_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_unsigned_to_nat(1u);
v___x_921_ = lean_nat_to_int(v___x_920_);
return v___x_921_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__3));
v___x_924_ = l_Lean_stringToMessageData(v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(lean_object* v_r_925_, lean_object* v_p_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
if (lean_obj_tag(v_p_926_) == 0)
{
lean_object* v_k_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_948_; 
v_k_930_ = lean_ctor_get(v_p_926_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v_p_926_);
if (v_isSharedCheck_948_ == 0)
{
v___x_932_ = v_p_926_;
v_isShared_933_ = v_isSharedCheck_948_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_k_930_);
lean_dec(v_p_926_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_948_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_934_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_935_ = lean_int_dec_eq(v_k_930_, v___x_934_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_936_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v_r_925_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Int_repr(v_k_930_);
lean_dec(v_k_930_);
if (v_isShared_933_ == 0)
{
lean_ctor_set_tag(v___x_932_, 3);
lean_ctor_set(v___x_932_, 0, v___x_938_);
v___x_940_ = v___x_932_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_944_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = l_Lean_MessageData_ofFormat(v___x_940_);
v___x_942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_937_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
}
else
{
lean_object* v___x_946_; 
lean_dec(v_k_930_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v_r_925_);
v___x_946_ = v___x_932_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_r_925_);
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
else
{
lean_object* v_k_949_; lean_object* v_v_950_; lean_object* v_p_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v_k_949_ = lean_ctor_get(v_p_926_, 0);
lean_inc(v_k_949_);
v_v_950_ = lean_ctor_get(v_p_926_, 1);
lean_inc(v_v_950_);
v_p_951_ = lean_ctor_get(v_p_926_, 2);
lean_inc_ref(v_p_951_);
lean_dec_ref_known(v_p_926_, 3);
v___x_952_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_953_ = lean_int_dec_eq(v_k_949_, v___x_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_950_, v_a_927_, v_a_928_);
lean_dec(v_v_950_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_954_, 1);
v___x_956_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v_r_925_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = l_Int_repr(v_k_949_);
lean_dec(v_k_949_);
v___x_959_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
v___x_960_ = l_Lean_MessageData_ofFormat(v___x_959_);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_957_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_955_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v_r_925_ = v___x_965_;
v_p_926_ = v_p_951_;
goto _start;
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec_ref(v_p_951_);
lean_dec(v_k_949_);
lean_dec_ref(v_r_925_);
v_a_967_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_954_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_954_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
else
{
lean_object* v___x_975_; 
lean_dec(v_k_949_);
v___x_975_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_950_, v_a_927_, v_a_928_);
lean_dec(v_v_950_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 1);
v___x_977_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_978_, 0, v_r_925_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_976_);
v___x_980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v_r_925_ = v___x_980_;
v_p_926_ = v_p_951_;
goto _start;
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec_ref(v_p_951_);
lean_dec_ref(v_r_925_);
v_a_982_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_975_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_975_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___boxed(lean_object* v_r_990_, lean_object* v_p_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v_r_990_, v_p_991_, v_a_992_, v_a_993_);
lean_dec_ref(v_a_993_);
lean_dec(v_a_992_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(lean_object* v_r_996_, lean_object* v_p_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v_r_996_, v_p_997_, v_a_998_, v_a_1006_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___boxed(lean_object* v_r_1010_, lean_object* v_p_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(v_r_1010_, v_p_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec(v_a_1012_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___redArg(lean_object* v_p_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
if (lean_obj_tag(v_p_1024_) == 0)
{
lean_object* v_k_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1038_; 
v_k_1028_ = lean_ctor_get(v_p_1024_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_p_1024_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1030_ = v_p_1024_;
v_isShared_1031_ = v_isSharedCheck_1038_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_k_1028_);
lean_dec(v_p_1024_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1038_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1032_ = l_Int_repr(v_k_1028_);
lean_dec(v_k_1028_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 3);
lean_ctor_set(v___x_1030_, 0, v___x_1032_);
v___x_1034_ = v___x_1030_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = l_Lean_MessageData_ofFormat(v___x_1034_);
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
return v___x_1036_;
}
}
}
else
{
lean_object* v_k_1039_; lean_object* v_v_1040_; lean_object* v_p_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v_k_1039_ = lean_ctor_get(v_p_1024_, 0);
lean_inc(v_k_1039_);
v_v_1040_ = lean_ctor_get(v_p_1024_, 1);
lean_inc(v_v_1040_);
v_p_1041_ = lean_ctor_get(v_p_1024_, 2);
lean_inc_ref(v_p_1041_);
lean_dec_ref_known(v_p_1024_, 3);
v___x_1042_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_1043_ = lean_int_dec_eq(v_k_1039_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_1040_, v_a_1025_, v_a_1026_);
lean_dec(v_v_1040_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___x_1044_, 1);
v___x_1046_ = l_Int_repr(v_k_1039_);
lean_dec(v_k_1039_);
v___x_1047_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
v___x_1048_ = l_Lean_MessageData_ofFormat(v___x_1047_);
v___x_1049_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4);
v___x_1050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1048_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_1045_);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v___x_1052_, v_p_1041_, v_a_1025_, v_a_1026_);
return v___x_1053_;
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec_ref(v_p_1041_);
lean_dec(v_k_1039_);
v_a_1054_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1044_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1044_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v___x_1062_; 
lean_dec(v_k_1039_);
v___x_1062_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_1040_, v_a_1025_, v_a_1026_);
lean_dec(v_v_1040_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1062_, 1);
v___x_1064_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_1063_);
v___x_1065_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v___x_1064_, v_p_1041_, v_a_1025_, v_a_1026_);
return v___x_1065_;
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec_ref(v_p_1041_);
v_a_1066_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1062_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1062_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___redArg___boxed(lean_object* v_p_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1074_, v_a_1075_, v_a_1076_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp(lean_object* v_p_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1079_, v_a_1080_, v_a_1088_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___boxed(lean_object* v_p_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Int_Internal_Linear_Poly_pp(v_p_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec(v_a_1093_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0(lean_object* v_a_1105_, lean_object* v___x_1106_, lean_object* v_x_1107_){
_start:
{
lean_object* v_size_1108_; uint8_t v___x_1109_; 
v_size_1108_ = lean_ctor_get(v_a_1105_, 2);
v___x_1109_ = lean_nat_dec_lt(v_x_1107_, v_size_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; 
v___x_1110_ = l_outOfBounds___redArg(v___x_1106_);
return v___x_1110_;
}
else
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1106_, v_a_1105_, v_x_1107_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed(lean_object* v_a_1112_, lean_object* v___x_1113_, lean_object* v_x_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0(v_a_1112_, v___x_1113_, v_x_1114_);
lean_dec(v_x_1114_);
lean_dec_ref(v___x_1113_);
lean_dec_ref(v_a_1112_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(lean_object* v_p_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = l_Lean_instInhabitedExpr;
v___x_1121_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_1117_, v_a_1118_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___f_1123_; lean_object* v___x_1124_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v___f_1123_ = lean_alloc_closure((void*)(l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1123_, 0, v_a_1122_);
lean_closure_set(v___f_1123_, 1, v___x_1120_);
v___x_1124_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_1123_, v_p_1116_);
return v___x_1124_;
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec_ref(v_p_1116_);
v_a_1125_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1121_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1121_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___boxed(lean_object* v_p_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1133_, v_a_1134_, v_a_1135_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27(lean_object* v_p_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1138_, v_a_1139_, v_a_1147_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___boxed(lean_object* v_p_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Int_Internal_Linear_Poly_denoteExpr_x27(v_p_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec(v_a_1152_);
return v_res_1163_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object* v_c_1164_){
_start:
{
lean_object* v_p_1165_; 
v_p_1165_ = lean_ctor_get(v_c_1164_, 1);
if (lean_obj_tag(v_p_1165_) == 0)
{
lean_object* v_d_1166_; lean_object* v_k_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v_d_1166_ = lean_ctor_get(v_c_1164_, 0);
v_k_1167_ = lean_ctor_get(v_p_1165_, 0);
v___x_1168_ = lean_int_emod(v_k_1167_, v_d_1166_);
v___x_1169_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1170_ = lean_int_dec_eq(v___x_1168_, v___x_1169_);
lean_dec(v___x_1168_);
return v___x_1170_;
}
else
{
lean_object* v_d_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v_d_1171_ = lean_ctor_get(v_c_1164_, 0);
v___x_1172_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_1173_ = lean_int_dec_eq(v_d_1171_, v___x_1172_);
return v___x_1173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial___boxed(lean_object* v_c_1174_){
_start:
{
uint8_t v_res_1175_; lean_object* v_r_1176_; 
v_res_1175_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_c_1174_);
lean_dec_ref(v_c_1174_);
v_r_1176_ = lean_box(v_res_1175_);
return v_r_1176_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0));
v___x_1179_ = l_Lean_stringToMessageData(v___x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object* v_c_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v_d_1184_; lean_object* v_p_1185_; lean_object* v___x_1186_; 
v_d_1184_ = lean_ctor_get(v_c_1180_, 0);
lean_inc(v_d_1184_);
v_p_1185_ = lean_ctor_get(v_c_1180_, 1);
lean_inc_ref(v_p_1185_);
lean_dec_ref(v_c_1180_);
v___x_1186_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1185_, v_a_1181_, v_a_1182_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1200_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1200_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1200_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1191_ = l_Int_repr(v_d_1184_);
lean_dec(v_d_1184_);
v___x_1192_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
v___x_1193_ = l_Lean_MessageData_ofFormat(v___x_1192_);
v___x_1194_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1);
v___x_1195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v_a_1187_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1196_);
v___x_1198_ = v___x_1189_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
lean_dec(v_d_1184_);
return v___x_1186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___boxed(lean_object* v_c_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1201_, v_a_1202_, v_a_1203_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(lean_object* v_c_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1206_, v_a_1207_, v_a_1215_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___boxed(lean_object* v_c_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(v_c_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec(v_a_1220_);
return v_res_1231_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1238_ = l_Lean_Level_ofNat(v___x_1237_);
return v___x_1238_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = lean_box(0);
v___x_1240_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3);
v___x_1241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set(v___x_1241_, 1, v___x_1239_);
return v___x_1241_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4);
v___x_1243_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2));
v___x_1244_ = l_Lean_Expr_const___override(v___x_1243_, v___x_1242_);
return v___x_1244_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = lean_box(0);
v___x_1249_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7));
v___x_1250_ = l_Lean_Expr_const___override(v___x_1249_, v___x_1248_);
return v___x_1250_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_box(0);
v___x_1256_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10));
v___x_1257_ = l_Lean_Expr_const___override(v___x_1256_, v___x_1255_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(lean_object* v_c_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v_d_1262_; lean_object* v_p_1263_; lean_object* v___x_1264_; 
v_d_1262_ = lean_ctor_get(v_c_1258_, 0);
lean_inc(v_d_1262_);
v_p_1263_ = lean_ctor_get(v_c_1258_, 1);
lean_inc_ref(v_p_1263_);
lean_dec_ref(v_c_1258_);
v___x_1264_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1263_, v_a_1259_, v_a_1260_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1286_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1267_ = v___x_1264_;
v_isShared_1268_ = v_isSharedCheck_1286_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1286_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___y_1270_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1276_ = lean_int_dec_le(v___x_1275_, v_d_1262_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1277_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5);
v___x_1278_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8);
v___x_1279_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11);
v___x_1280_ = lean_int_neg(v_d_1262_);
lean_dec(v_d_1262_);
v___x_1281_ = l_Int_toNat(v___x_1280_);
lean_dec(v___x_1280_);
v___x_1282_ = l_Lean_instToExprInt_mkNat(v___x_1281_);
v___x_1283_ = l_Lean_mkApp3(v___x_1277_, v___x_1278_, v___x_1279_, v___x_1282_);
v___y_1270_ = v___x_1283_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = l_Int_toNat(v_d_1262_);
lean_dec(v_d_1262_);
v___x_1285_ = l_Lean_instToExprInt_mkNat(v___x_1284_);
v___y_1270_ = v___x_1285_;
goto v___jp_1269_;
}
v___jp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1271_ = l_Lean_mkIntDvd(v___y_1270_, v_a_1265_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1271_);
v___x_1273_ = v___x_1267_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
else
{
lean_dec(v_d_1262_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1287_, v_a_1288_, v_a_1289_);
lean_dec_ref(v_a_1289_);
lean_dec(v_a_1288_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(lean_object* v_c_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1292_, v_a_1293_, v_a_1301_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___boxed(lean_object* v_c_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(v_c_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec(v_a_1306_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(lean_object* v_msgData_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v___x_1324_; lean_object* v_env_1325_; uint8_t v___x_1326_; lean_object* v_env_1327_; lean_object* v___x_1328_; lean_object* v_toCold_1329_; lean_object* v_mctx_1330_; lean_object* v_lctx_1331_; lean_object* v_options_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1324_ = lean_st_ref_get(v___y_1322_);
v_env_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc_ref(v_env_1325_);
lean_dec(v___x_1324_);
v___x_1326_ = 0;
v_env_1327_ = l_Lean_Environment_setRecordingDeps(v_env_1325_, v___x_1326_);
v___x_1328_ = lean_st_ref_get(v___y_1320_);
v_toCold_1329_ = lean_ctor_get(v___y_1321_, 0);
v_mctx_1330_ = lean_ctor_get(v___x_1328_, 0);
lean_inc_ref(v_mctx_1330_);
lean_dec(v___x_1328_);
v_lctx_1331_ = lean_ctor_get(v___y_1319_, 2);
v_options_1332_ = lean_ctor_get(v_toCold_1329_, 2);
lean_inc_ref(v_options_1332_);
lean_inc_ref(v_lctx_1331_);
v___x_1333_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1333_, 0, v_env_1327_);
lean_ctor_set(v___x_1333_, 1, v_mctx_1330_);
lean_ctor_set(v___x_1333_, 2, v_lctx_1331_);
lean_ctor_set(v___x_1333_, 3, v_options_1332_);
v___x_1334_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v_msgData_1318_);
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object* v_msgData_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msgData_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(lean_object* v_msg_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_ref_1349_; lean_object* v___x_1350_; lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1359_; 
v_ref_1349_ = lean_ctor_get(v___y_1346_, 2);
v___x_1350_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msg_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1359_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1359_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
lean_inc(v_ref_1349_);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_ref_1349_);
lean_ctor_set(v___x_1355_, 1, v_a_1351_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set_tag(v___x_1353_, 1);
lean_ctor_set(v___x_1353_, 0, v___x_1355_);
v___x_1357_ = v___x_1353_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg___boxed(lean_object* v_msg_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
return v_res_1366_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0));
v___x_1369_ = l_Lean_stringToMessageData(v___x_1368_);
return v___x_1369_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2));
v___x_1372_ = l_Lean_stringToMessageData(v___x_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object* v_c_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1373_, v_a_1374_, v_a_1382_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref_known(v___x_1385_, 1);
v___x_1387_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1388_ = l_Lean_indentD(v_a_1386_);
v___x_1389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1387_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
v___x_1390_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3);
v___x_1391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1389_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
v___x_1392_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1391_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
return v___x_1392_;
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
v_a_1393_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1385_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1385_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
lean_dec(v_a_1403_);
lean_dec(v_a_1402_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(lean_object* v_00_u03b1_1414_, lean_object* v_c_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1428_, lean_object* v_c_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(v_00_u03b1_1428_, v_c_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_a_1435_);
lean_dec_ref(v_a_1434_);
lean_dec(v_a_1433_);
lean_dec_ref(v_a_1432_);
lean_dec(v_a_1431_);
lean_dec(v_a_1430_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(lean_object* v_00_u03b1_1442_, lean_object* v_msg_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1443_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___boxed(lean_object* v_00_u03b1_1456_, lean_object* v_msg_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(v_00_u03b1_1456_, v_msg_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec(v___y_1458_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial_spec__0(lean_object* v_a_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_nat_to_int(v_a_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(lean_object* v_c_1472_){
_start:
{
lean_object* v_p_1473_; 
v_p_1473_ = lean_ctor_get(v_c_1472_, 0);
if (lean_obj_tag(v_p_1473_) == 0)
{
lean_object* v_k_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
v_k_1474_ = lean_ctor_get(v_p_1473_, 0);
v___x_1475_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1476_ = lean_int_dec_eq(v_k_1474_, v___x_1475_);
if (v___x_1476_ == 0)
{
uint8_t v___x_1477_; 
v___x_1477_ = 1;
return v___x_1477_;
}
else
{
uint8_t v___x_1478_; 
v___x_1478_ = 0;
return v___x_1478_;
}
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1479_ = l_Int_Internal_Linear_Poly_getConst(v_p_1473_);
v___x_1480_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v_p_1473_);
v___x_1481_ = lean_nat_to_int(v___x_1480_);
v___x_1482_ = lean_int_emod(v___x_1479_, v___x_1481_);
lean_dec(v___x_1481_);
lean_dec(v___x_1479_);
v___x_1483_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1484_ = lean_int_dec_eq(v___x_1482_, v___x_1483_);
lean_dec(v___x_1482_);
if (v___x_1484_ == 0)
{
uint8_t v___x_1485_; 
v___x_1485_ = 1;
return v___x_1485_;
}
else
{
uint8_t v___x_1486_; 
v___x_1486_ = 0;
return v___x_1486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial___boxed(lean_object* v_c_1487_){
_start:
{
uint8_t v_res_1488_; lean_object* v_r_1489_; 
v_res_1488_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(v_c_1487_);
lean_dec_ref(v_c_1487_);
v_r_1489_ = lean_box(v_res_1488_);
return v_r_1489_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0));
v___x_1492_ = l_Lean_stringToMessageData(v___x_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(lean_object* v_c_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v_p_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1514_; 
v_p_1497_ = lean_ctor_get(v_c_1493_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_c_1493_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; 
v_unused_1515_ = lean_ctor_get(v_c_1493_, 1);
lean_dec(v_unused_1515_);
v___x_1499_ = v_c_1493_;
v_isShared_1500_ = v_isSharedCheck_1514_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_p_1497_);
lean_dec(v_c_1493_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1514_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1497_, v_a_1494_, v_a_1495_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1513_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1513_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1513_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1506_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1);
if (v_isShared_1500_ == 0)
{
lean_ctor_set_tag(v___x_1499_, 7);
lean_ctor_set(v___x_1499_, 1, v___x_1506_);
lean_ctor_set(v___x_1499_, 0, v_a_1502_);
v___x_1508_ = v___x_1499_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1502_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1510_; 
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1508_);
v___x_1510_ = v___x_1504_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
else
{
lean_del_object(v___x_1499_);
return v___x_1501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___boxed(lean_object* v_c_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1516_, v_a_1517_, v_a_1518_);
lean_dec_ref(v_a_1518_);
lean_dec(v_a_1517_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(lean_object* v_c_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1521_, v_a_1522_, v_a_1530_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___boxed(lean_object* v_c_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(v_c_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
lean_dec(v_a_1544_);
lean_dec_ref(v_a_1543_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
lean_dec(v_a_1538_);
lean_dec_ref(v_a_1537_);
lean_dec(v_a_1536_);
lean_dec(v_a_1535_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(lean_object* v_c_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1547_, v_a_1548_, v_a_1551_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1556_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1557_ = l_Lean_indentD(v_a_1555_);
v___x_1558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1558_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
return v___x_1559_;
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
v_a_1560_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1554_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1554_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_);
lean_dec(v_a_1573_);
lean_dec_ref(v_a_1572_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
lean_dec(v_a_1569_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(lean_object* v_00_u03b1_1576_, lean_object* v_c_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1577_, v_a_1578_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1590_, lean_object* v_c_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(v_00_u03b1_1590_, v_c_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
lean_dec(v_a_1593_);
lean_dec(v_a_1592_);
return v_res_1603_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1605_ = l_Lean_mkIntLit(v___x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(lean_object* v_c_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v_p_1610_; lean_object* v___x_1611_; 
v_p_1610_ = lean_ctor_get(v_c_1606_, 0);
lean_inc_ref(v_p_1610_);
lean_dec_ref(v_c_1606_);
v___x_1611_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1610_, v_a_1607_, v_a_1608_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1622_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1622_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1622_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1616_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1617_ = l_Lean_mkIntEq(v_a_1612_, v___x_1616_);
v___x_1618_ = l_Lean_mkNot(v___x_1617_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v___x_1618_);
v___x_1620_ = v___x_1614_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
else
{
return v___x_1611_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1623_, v_a_1624_, v_a_1625_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(lean_object* v_c_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1628_, v_a_1629_, v_a_1637_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___boxed(lean_object* v_c_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(v_c_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec(v_a_1642_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert___boxed(lean_object* v_c_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_00___x40___internal___hyg_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = lean_grind_cutsat_assert_le(v_c_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
return v_res_1678_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(lean_object* v_c_1679_){
_start:
{
lean_object* v_p_1680_; 
v_p_1680_ = lean_ctor_get(v_c_1679_, 0);
if (lean_obj_tag(v_p_1680_) == 0)
{
lean_object* v_k_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v_k_1681_ = lean_ctor_get(v_p_1680_, 0);
v___x_1682_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1683_ = lean_int_dec_le(v_k_1681_, v___x_1682_);
return v___x_1683_;
}
else
{
uint8_t v___x_1684_; 
v___x_1684_ = 0;
return v___x_1684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial___boxed(lean_object* v_c_1685_){
_start:
{
uint8_t v_res_1686_; lean_object* v_r_1687_; 
v_res_1686_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_c_1685_);
lean_dec_ref(v_c_1685_);
v_r_1687_ = lean_box(v_res_1686_);
return v_r_1687_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0));
v___x_1690_ = l_Lean_stringToMessageData(v___x_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(lean_object* v_c_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_p_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1712_; 
v_p_1695_ = lean_ctor_get(v_c_1691_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_c_1691_);
if (v_isSharedCheck_1712_ == 0)
{
lean_object* v_unused_1713_; 
v_unused_1713_ = lean_ctor_get(v_c_1691_, 1);
lean_dec(v_unused_1713_);
v___x_1697_ = v_c_1691_;
v_isShared_1698_ = v_isSharedCheck_1712_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_p_1695_);
lean_dec(v_c_1691_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1712_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1695_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1711_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1711_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1711_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1704_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1);
if (v_isShared_1698_ == 0)
{
lean_ctor_set_tag(v___x_1697_, 7);
lean_ctor_set(v___x_1697_, 1, v___x_1704_);
lean_ctor_set(v___x_1697_, 0, v_a_1700_);
v___x_1706_ = v___x_1697_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1700_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1708_; 
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1706_);
v___x_1708_ = v___x_1702_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_del_object(v___x_1697_);
return v___x_1699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___boxed(lean_object* v_c_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1714_, v_a_1715_, v_a_1716_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(lean_object* v_c_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1719_, v_a_1720_, v_a_1728_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___boxed(lean_object* v_c_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(v_c_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
lean_dec(v_a_1733_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(lean_object* v_c_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_p_1749_; lean_object* v___x_1750_; 
v_p_1749_ = lean_ctor_get(v_c_1745_, 0);
lean_inc_ref(v_p_1749_);
lean_dec_ref(v_c_1745_);
v___x_1750_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1749_, v_a_1746_, v_a_1747_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1760_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1760_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1760_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1755_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1756_ = l_Lean_mkIntLE(v_a_1751_, v___x_1755_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1756_);
v___x_1758_ = v___x_1753_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
else
{
return v___x_1750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1761_, v_a_1762_, v_a_1763_);
lean_dec_ref(v_a_1763_);
lean_dec(v_a_1762_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(lean_object* v_c_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1766_, v_a_1767_, v_a_1775_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___boxed(lean_object* v_c_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(v_c_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec(v_a_1780_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(lean_object* v_c_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1792_, v_a_1793_, v_a_1796_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref_known(v___x_1799_, 1);
v___x_1801_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1802_ = l_Lean_indentD(v_a_1800_);
v___x_1803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1801_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1803_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
return v___x_1804_;
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
v_a_1805_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1799_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1799_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec(v_a_1814_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(lean_object* v_00_u03b1_1821_, lean_object* v_c_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1822_, v_a_1823_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1835_, lean_object* v_c_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(v_00_u03b1_1835_, v_c_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
lean_dec(v_a_1846_);
lean_dec_ref(v_a_1845_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec(v_a_1837_);
return v_res_1848_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(lean_object* v_c_1849_){
_start:
{
lean_object* v_p_1850_; 
v_p_1850_ = lean_ctor_get(v_c_1849_, 0);
if (lean_obj_tag(v_p_1850_) == 0)
{
lean_object* v_k_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v_k_1851_ = lean_ctor_get(v_p_1850_, 0);
v___x_1852_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1853_ = lean_int_dec_eq(v_k_1851_, v___x_1852_);
return v___x_1853_;
}
else
{
uint8_t v___x_1854_; 
v___x_1854_ = 0;
return v___x_1854_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial___boxed(lean_object* v_c_1855_){
_start:
{
uint8_t v_res_1856_; lean_object* v_r_1857_; 
v_res_1856_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(v_c_1855_);
lean_dec_ref(v_c_1855_);
v_r_1857_ = lean_box(v_res_1856_);
return v_r_1857_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0));
v___x_1860_ = l_Lean_stringToMessageData(v___x_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object* v_c_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v_p_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1882_; 
v_p_1865_ = lean_ctor_get(v_c_1861_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_c_1861_);
if (v_isSharedCheck_1882_ == 0)
{
lean_object* v_unused_1883_; 
v_unused_1883_ = lean_ctor_get(v_c_1861_, 1);
lean_dec(v_unused_1883_);
v___x_1867_ = v_c_1861_;
v_isShared_1868_ = v_isSharedCheck_1882_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_p_1865_);
lean_dec(v_c_1861_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1882_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1865_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1881_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1881_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1881_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1874_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1);
if (v_isShared_1868_ == 0)
{
lean_ctor_set_tag(v___x_1867_, 7);
lean_ctor_set(v___x_1867_, 1, v___x_1874_);
lean_ctor_set(v___x_1867_, 0, v_a_1870_);
v___x_1876_ = v___x_1867_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1870_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1878_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1876_);
v___x_1878_ = v___x_1872_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
else
{
lean_del_object(v___x_1867_);
return v___x_1869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___boxed(lean_object* v_c_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1884_, v_a_1885_, v_a_1886_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(lean_object* v_c_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1889_, v_a_1890_, v_a_1898_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___boxed(lean_object* v_c_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(v_c_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
lean_dec(v_a_1912_);
lean_dec_ref(v_a_1911_);
lean_dec(v_a_1910_);
lean_dec_ref(v_a_1909_);
lean_dec(v_a_1908_);
lean_dec_ref(v_a_1907_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec(v_a_1903_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(lean_object* v_c_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v_p_1919_; lean_object* v___x_1920_; 
v_p_1919_ = lean_ctor_get(v_c_1915_, 0);
lean_inc_ref(v_p_1919_);
lean_dec_ref(v_c_1915_);
v___x_1920_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1919_, v_a_1916_, v_a_1917_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1930_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1930_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1930_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1925_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1926_ = l_Lean_mkIntEq(v_a_1921_, v___x_1925_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1926_);
v___x_1928_ = v___x_1923_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
else
{
return v___x_1920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1931_, v_a_1932_, v_a_1933_);
lean_dec_ref(v_a_1933_);
lean_dec(v_a_1932_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(lean_object* v_c_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1936_, v_a_1937_, v_a_1945_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___boxed(lean_object* v_c_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(v_c_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(lean_object* v_c_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1962_, v_a_1963_, v_a_1966_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v___x_1969_, 1);
v___x_1971_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1972_ = l_Lean_indentD(v_a_1970_);
v___x_1973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1971_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1973_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
return v___x_1974_;
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
v_a_1975_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1969_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1969_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
lean_dec(v_a_1988_);
lean_dec_ref(v_a_1987_);
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(lean_object* v_00_u03b1_1991_, lean_object* v_c_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_1992_, v_a_1993_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_2005_, lean_object* v_c_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(v_00_u03b1_2005_, v_c_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
lean_dec(v_a_2016_);
lean_dec_ref(v_a_2015_);
lean_dec(v_a_2014_);
lean_dec_ref(v_a_2013_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec(v_a_2007_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(lean_object* v_x_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2020_, v_a_2021_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2040_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2040_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2040_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v_occurs_2028_; lean_object* v_size_2029_; lean_object* v___x_2030_; uint8_t v___x_2031_; 
v_occurs_2028_ = lean_ctor_get(v_a_2024_, 11);
lean_inc_ref(v_occurs_2028_);
lean_dec(v_a_2024_);
v_size_2029_ = lean_ctor_get(v_occurs_2028_, 2);
v___x_2030_ = lean_box(1);
v___x_2031_ = lean_nat_dec_lt(v_x_2019_, v_size_2029_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2034_; 
lean_dec_ref(v_occurs_2028_);
v___x_2032_ = l_outOfBounds___redArg(v___x_2030_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2032_);
v___x_2034_ = v___x_2026_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2036_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2030_, v_occurs_2028_, v_x_2019_);
lean_dec_ref(v_occurs_2028_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2036_);
v___x_2038_ = v___x_2026_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
v_a_2041_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2023_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2023_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg___boxed(lean_object* v_x_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2049_, v_a_2050_, v_a_2051_);
lean_dec_ref(v_a_2051_);
lean_dec(v_a_2050_);
lean_dec(v_x_2049_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(lean_object* v_x_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2054_, v_a_2055_, v_a_2063_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___boxed(lean_object* v_x_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(v_x_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
lean_dec(v_a_2068_);
lean_dec(v_x_2067_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(lean_object* v_k_2080_, lean_object* v_v_2081_, lean_object* v_t_2082_){
_start:
{
if (lean_obj_tag(v_t_2082_) == 0)
{
lean_object* v_size_2083_; lean_object* v_k_2084_; lean_object* v_v_2085_; lean_object* v_l_2086_; lean_object* v_r_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2368_; 
v_size_2083_ = lean_ctor_get(v_t_2082_, 0);
v_k_2084_ = lean_ctor_get(v_t_2082_, 1);
v_v_2085_ = lean_ctor_get(v_t_2082_, 2);
v_l_2086_ = lean_ctor_get(v_t_2082_, 3);
v_r_2087_ = lean_ctor_get(v_t_2082_, 4);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_t_2082_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2089_ = v_t_2082_;
v_isShared_2090_ = v_isSharedCheck_2368_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_r_2087_);
lean_inc(v_l_2086_);
lean_inc(v_v_2085_);
lean_inc(v_k_2084_);
lean_inc(v_size_2083_);
lean_dec(v_t_2082_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2368_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
uint8_t v___x_2091_; 
v___x_2091_ = lean_nat_dec_lt(v_k_2080_, v_k_2084_);
if (v___x_2091_ == 0)
{
uint8_t v___x_2092_; 
v___x_2092_ = lean_nat_dec_eq(v_k_2080_, v_k_2084_);
if (v___x_2092_ == 0)
{
lean_object* v_impl_2093_; lean_object* v___x_2094_; 
lean_dec(v_size_2083_);
v_impl_2093_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2080_, v_v_2081_, v_r_2087_);
v___x_2094_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2086_) == 0)
{
lean_object* v_size_2095_; lean_object* v_size_2096_; lean_object* v_k_2097_; lean_object* v_v_2098_; lean_object* v_l_2099_; lean_object* v_r_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; 
v_size_2095_ = lean_ctor_get(v_l_2086_, 0);
v_size_2096_ = lean_ctor_get(v_impl_2093_, 0);
v_k_2097_ = lean_ctor_get(v_impl_2093_, 1);
v_v_2098_ = lean_ctor_get(v_impl_2093_, 2);
v_l_2099_ = lean_ctor_get(v_impl_2093_, 3);
lean_inc(v_l_2099_);
v_r_2100_ = lean_ctor_get(v_impl_2093_, 4);
v___x_2101_ = lean_unsigned_to_nat(3u);
v___x_2102_ = lean_nat_mul(v___x_2101_, v_size_2095_);
v___x_2103_ = lean_nat_dec_lt(v___x_2102_, v_size_2096_);
lean_dec(v___x_2102_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2107_; 
lean_dec(v_l_2099_);
v___x_2104_ = lean_nat_add(v___x_2094_, v_size_2095_);
v___x_2105_ = lean_nat_add(v___x_2104_, v_size_2096_);
lean_dec(v___x_2104_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 4, v_impl_2093_);
lean_ctor_set(v___x_2089_, 0, v___x_2105_);
v___x_2107_ = v___x_2089_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2108_, 3, v_l_2086_);
lean_ctor_set(v_reuseFailAlloc_2108_, 4, v_impl_2093_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
else
{
lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2172_; 
lean_inc(v_r_2100_);
lean_inc(v_v_2098_);
lean_inc(v_k_2097_);
lean_inc(v_size_2096_);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_impl_2093_);
if (v_isSharedCheck_2172_ == 0)
{
lean_object* v_unused_2173_; lean_object* v_unused_2174_; lean_object* v_unused_2175_; lean_object* v_unused_2176_; lean_object* v_unused_2177_; 
v_unused_2173_ = lean_ctor_get(v_impl_2093_, 4);
lean_dec(v_unused_2173_);
v_unused_2174_ = lean_ctor_get(v_impl_2093_, 3);
lean_dec(v_unused_2174_);
v_unused_2175_ = lean_ctor_get(v_impl_2093_, 2);
lean_dec(v_unused_2175_);
v_unused_2176_ = lean_ctor_get(v_impl_2093_, 1);
lean_dec(v_unused_2176_);
v_unused_2177_ = lean_ctor_get(v_impl_2093_, 0);
lean_dec(v_unused_2177_);
v___x_2110_ = v_impl_2093_;
v_isShared_2111_ = v_isSharedCheck_2172_;
goto v_resetjp_2109_;
}
else
{
lean_dec(v_impl_2093_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2172_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v_size_2112_; lean_object* v_k_2113_; lean_object* v_v_2114_; lean_object* v_l_2115_; lean_object* v_r_2116_; lean_object* v_size_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
v_size_2112_ = lean_ctor_get(v_l_2099_, 0);
v_k_2113_ = lean_ctor_get(v_l_2099_, 1);
v_v_2114_ = lean_ctor_get(v_l_2099_, 2);
v_l_2115_ = lean_ctor_get(v_l_2099_, 3);
v_r_2116_ = lean_ctor_get(v_l_2099_, 4);
v_size_2117_ = lean_ctor_get(v_r_2100_, 0);
v___x_2118_ = lean_unsigned_to_nat(2u);
v___x_2119_ = lean_nat_mul(v___x_2118_, v_size_2117_);
v___x_2120_ = lean_nat_dec_lt(v_size_2112_, v___x_2119_);
lean_dec(v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2148_; 
lean_inc(v_r_2116_);
lean_inc(v_l_2115_);
lean_inc(v_v_2114_);
lean_inc(v_k_2113_);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_l_2099_);
if (v_isSharedCheck_2148_ == 0)
{
lean_object* v_unused_2149_; lean_object* v_unused_2150_; lean_object* v_unused_2151_; lean_object* v_unused_2152_; lean_object* v_unused_2153_; 
v_unused_2149_ = lean_ctor_get(v_l_2099_, 4);
lean_dec(v_unused_2149_);
v_unused_2150_ = lean_ctor_get(v_l_2099_, 3);
lean_dec(v_unused_2150_);
v_unused_2151_ = lean_ctor_get(v_l_2099_, 2);
lean_dec(v_unused_2151_);
v_unused_2152_ = lean_ctor_get(v_l_2099_, 1);
lean_dec(v_unused_2152_);
v_unused_2153_ = lean_ctor_get(v_l_2099_, 0);
lean_dec(v_unused_2153_);
v___x_2122_ = v_l_2099_;
v_isShared_2123_ = v_isSharedCheck_2148_;
goto v_resetjp_2121_;
}
else
{
lean_dec(v_l_2099_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2148_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2138_; 
v___x_2124_ = lean_nat_add(v___x_2094_, v_size_2095_);
v___x_2125_ = lean_nat_add(v___x_2124_, v_size_2096_);
lean_dec(v_size_2096_);
if (lean_obj_tag(v_l_2115_) == 0)
{
lean_object* v_size_2146_; 
v_size_2146_ = lean_ctor_get(v_l_2115_, 0);
lean_inc(v_size_2146_);
v___y_2138_ = v_size_2146_;
goto v___jp_2137_;
}
else
{
lean_object* v___x_2147_; 
v___x_2147_ = lean_unsigned_to_nat(0u);
v___y_2138_ = v___x_2147_;
goto v___jp_2137_;
}
v___jp_2126_:
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = lean_nat_add(v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec(v___y_2128_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 4, v_r_2100_);
lean_ctor_set(v___x_2122_, 3, v_r_2116_);
lean_ctor_set(v___x_2122_, 2, v_v_2098_);
lean_ctor_set(v___x_2122_, 1, v_k_2097_);
lean_ctor_set(v___x_2122_, 0, v___x_2130_);
v___x_2132_ = v___x_2122_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2130_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_k_2097_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_v_2098_);
lean_ctor_set(v_reuseFailAlloc_2136_, 3, v_r_2116_);
lean_ctor_set(v_reuseFailAlloc_2136_, 4, v_r_2100_);
v___x_2132_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2134_; 
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 4, v___x_2132_);
lean_ctor_set(v___x_2110_, 3, v___y_2127_);
lean_ctor_set(v___x_2110_, 2, v_v_2114_);
lean_ctor_set(v___x_2110_, 1, v_k_2113_);
lean_ctor_set(v___x_2110_, 0, v___x_2125_);
v___x_2134_ = v___x_2110_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2125_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_k_2113_);
lean_ctor_set(v_reuseFailAlloc_2135_, 2, v_v_2114_);
lean_ctor_set(v_reuseFailAlloc_2135_, 3, v___y_2127_);
lean_ctor_set(v_reuseFailAlloc_2135_, 4, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
v___jp_2137_:
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2139_ = lean_nat_add(v___x_2124_, v___y_2138_);
lean_dec(v___y_2138_);
lean_dec(v___x_2124_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 4, v_l_2115_);
lean_ctor_set(v___x_2089_, 0, v___x_2139_);
v___x_2141_ = v___x_2089_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2145_, 3, v_l_2086_);
lean_ctor_set(v_reuseFailAlloc_2145_, 4, v_l_2115_);
v___x_2141_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2142_; 
v___x_2142_ = lean_nat_add(v___x_2094_, v_size_2117_);
if (lean_obj_tag(v_r_2116_) == 0)
{
lean_object* v_size_2143_; 
v_size_2143_ = lean_ctor_get(v_r_2116_, 0);
lean_inc(v_size_2143_);
v___y_2127_ = v___x_2141_;
v___y_2128_ = v___x_2142_;
v___y_2129_ = v_size_2143_;
goto v___jp_2126_;
}
else
{
lean_object* v___x_2144_; 
v___x_2144_ = lean_unsigned_to_nat(0u);
v___y_2127_ = v___x_2141_;
v___y_2128_ = v___x_2142_;
v___y_2129_ = v___x_2144_;
goto v___jp_2126_;
}
}
}
}
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
lean_del_object(v___x_2089_);
v___x_2154_ = lean_nat_add(v___x_2094_, v_size_2095_);
v___x_2155_ = lean_nat_add(v___x_2154_, v_size_2096_);
lean_dec(v_size_2096_);
v___x_2156_ = lean_nat_add(v___x_2154_, v_size_2112_);
lean_dec(v___x_2154_);
lean_inc_ref(v_l_2086_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 4, v_l_2099_);
lean_ctor_set(v___x_2110_, 3, v_l_2086_);
lean_ctor_set(v___x_2110_, 2, v_v_2085_);
lean_ctor_set(v___x_2110_, 1, v_k_2084_);
lean_ctor_set(v___x_2110_, 0, v___x_2156_);
v___x_2158_ = v___x_2110_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2171_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2171_, 3, v_l_2086_);
lean_ctor_set(v_reuseFailAlloc_2171_, 4, v_l_2099_);
v___x_2158_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
v_isSharedCheck_2165_ = !lean_is_exclusive(v_l_2086_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; lean_object* v_unused_2167_; lean_object* v_unused_2168_; lean_object* v_unused_2169_; lean_object* v_unused_2170_; 
v_unused_2166_ = lean_ctor_get(v_l_2086_, 4);
lean_dec(v_unused_2166_);
v_unused_2167_ = lean_ctor_get(v_l_2086_, 3);
lean_dec(v_unused_2167_);
v_unused_2168_ = lean_ctor_get(v_l_2086_, 2);
lean_dec(v_unused_2168_);
v_unused_2169_ = lean_ctor_get(v_l_2086_, 1);
lean_dec(v_unused_2169_);
v_unused_2170_ = lean_ctor_get(v_l_2086_, 0);
lean_dec(v_unused_2170_);
v___x_2160_ = v_l_2086_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_dec(v_l_2086_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 4, v_r_2100_);
lean_ctor_set(v___x_2160_, 3, v___x_2158_);
lean_ctor_set(v___x_2160_, 2, v_v_2098_);
lean_ctor_set(v___x_2160_, 1, v_k_2097_);
lean_ctor_set(v___x_2160_, 0, v___x_2155_);
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2155_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_k_2097_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_v_2098_);
lean_ctor_set(v_reuseFailAlloc_2164_, 3, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2164_, 4, v_r_2100_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2178_; 
v_l_2178_ = lean_ctor_get(v_impl_2093_, 3);
lean_inc(v_l_2178_);
if (lean_obj_tag(v_l_2178_) == 0)
{
lean_object* v_r_2179_; lean_object* v_k_2180_; lean_object* v_v_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2204_; 
v_r_2179_ = lean_ctor_get(v_impl_2093_, 4);
v_k_2180_ = lean_ctor_get(v_impl_2093_, 1);
v_v_2181_ = lean_ctor_get(v_impl_2093_, 2);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_impl_2093_);
if (v_isSharedCheck_2204_ == 0)
{
lean_object* v_unused_2205_; lean_object* v_unused_2206_; 
v_unused_2205_ = lean_ctor_get(v_impl_2093_, 3);
lean_dec(v_unused_2205_);
v_unused_2206_ = lean_ctor_get(v_impl_2093_, 0);
lean_dec(v_unused_2206_);
v___x_2183_ = v_impl_2093_;
v_isShared_2184_ = v_isSharedCheck_2204_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_r_2179_);
lean_inc(v_v_2181_);
lean_inc(v_k_2180_);
lean_dec(v_impl_2093_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2204_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v_k_2185_; lean_object* v_v_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2200_; 
v_k_2185_ = lean_ctor_get(v_l_2178_, 1);
v_v_2186_ = lean_ctor_get(v_l_2178_, 2);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_l_2178_);
if (v_isSharedCheck_2200_ == 0)
{
lean_object* v_unused_2201_; lean_object* v_unused_2202_; lean_object* v_unused_2203_; 
v_unused_2201_ = lean_ctor_get(v_l_2178_, 4);
lean_dec(v_unused_2201_);
v_unused_2202_ = lean_ctor_get(v_l_2178_, 3);
lean_dec(v_unused_2202_);
v_unused_2203_ = lean_ctor_get(v_l_2178_, 0);
lean_dec(v_unused_2203_);
v___x_2188_ = v_l_2178_;
v_isShared_2189_ = v_isSharedCheck_2200_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_v_2186_);
lean_inc(v_k_2185_);
lean_dec(v_l_2178_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2200_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2190_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2179_, 2);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 4, v_r_2179_);
lean_ctor_set(v___x_2188_, 3, v_r_2179_);
lean_ctor_set(v___x_2188_, 2, v_v_2085_);
lean_ctor_set(v___x_2188_, 1, v_k_2084_);
lean_ctor_set(v___x_2188_, 0, v___x_2094_);
v___x_2192_ = v___x_2188_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2199_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2199_, 3, v_r_2179_);
lean_ctor_set(v_reuseFailAlloc_2199_, 4, v_r_2179_);
v___x_2192_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2194_; 
lean_inc(v_r_2179_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 3, v_r_2179_);
lean_ctor_set(v___x_2183_, 0, v___x_2094_);
v___x_2194_ = v___x_2183_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_k_2180_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_v_2181_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_r_2179_);
lean_ctor_set(v_reuseFailAlloc_2198_, 4, v_r_2179_);
v___x_2194_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2196_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 4, v___x_2194_);
lean_ctor_set(v___x_2089_, 3, v___x_2192_);
lean_ctor_set(v___x_2089_, 2, v_v_2186_);
lean_ctor_set(v___x_2089_, 1, v_k_2185_);
lean_ctor_set(v___x_2089_, 0, v___x_2190_);
v___x_2196_ = v___x_2089_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_k_2185_);
lean_ctor_set(v_reuseFailAlloc_2197_, 2, v_v_2186_);
lean_ctor_set(v_reuseFailAlloc_2197_, 3, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2197_, 4, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
}
}
else
{
lean_object* v_r_2207_; 
v_r_2207_ = lean_ctor_get(v_impl_2093_, 4);
lean_inc(v_r_2207_);
if (lean_obj_tag(v_r_2207_) == 0)
{
lean_object* v_k_2208_; lean_object* v_v_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2220_; 
v_k_2208_ = lean_ctor_get(v_impl_2093_, 1);
v_v_2209_ = lean_ctor_get(v_impl_2093_, 2);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_impl_2093_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; lean_object* v_unused_2222_; lean_object* v_unused_2223_; 
v_unused_2221_ = lean_ctor_get(v_impl_2093_, 4);
lean_dec(v_unused_2221_);
v_unused_2222_ = lean_ctor_get(v_impl_2093_, 3);
lean_dec(v_unused_2222_);
v_unused_2223_ = lean_ctor_get(v_impl_2093_, 0);
lean_dec(v_unused_2223_);
v___x_2211_ = v_impl_2093_;
v_isShared_2212_ = v_isSharedCheck_2220_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_v_2209_);
lean_inc(v_k_2208_);
lean_dec(v_impl_2093_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2220_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2213_ = lean_unsigned_to_nat(3u);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 4, v_l_2178_);
lean_ctor_set(v___x_2211_, 2, v_v_2085_);
lean_ctor_set(v___x_2211_, 1, v_k_2084_);
lean_ctor_set(v___x_2211_, 0, v___x_2094_);
v___x_2215_ = v___x_2211_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2219_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2219_, 3, v_l_2178_);
lean_ctor_set(v_reuseFailAlloc_2219_, 4, v_l_2178_);
v___x_2215_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
lean_object* v___x_2217_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 4, v_r_2207_);
lean_ctor_set(v___x_2089_, 3, v___x_2215_);
lean_ctor_set(v___x_2089_, 2, v_v_2209_);
lean_ctor_set(v___x_2089_, 1, v_k_2208_);
lean_ctor_set(v___x_2089_, 0, v___x_2213_);
v___x_2217_ = v___x_2089_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v_k_2208_);
lean_ctor_set(v_reuseFailAlloc_2218_, 2, v_v_2209_);
lean_ctor_set(v_reuseFailAlloc_2218_, 3, v___x_2215_);
lean_ctor_set(v_reuseFailAlloc_2218_, 4, v_r_2207_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2224_ = lean_unsigned_to_nat(2u);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 4, v_impl_2093_);
lean_ctor_set(v___x_2089_, 3, v_r_2207_);
lean_ctor_set(v___x_2089_, 0, v___x_2224_);
v___x_2226_ = v___x_2089_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_r_2207_);
lean_ctor_set(v_reuseFailAlloc_2227_, 4, v_impl_2093_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
else
{
lean_object* v___x_2229_; 
lean_dec(v_v_2085_);
lean_dec(v_k_2084_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 2, v_v_2081_);
lean_ctor_set(v___x_2089_, 1, v_k_2080_);
v___x_2229_ = v___x_2089_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_size_2083_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_k_2080_);
lean_ctor_set(v_reuseFailAlloc_2230_, 2, v_v_2081_);
lean_ctor_set(v_reuseFailAlloc_2230_, 3, v_l_2086_);
lean_ctor_set(v_reuseFailAlloc_2230_, 4, v_r_2087_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
else
{
lean_object* v_impl_2231_; lean_object* v___x_2232_; 
lean_dec(v_size_2083_);
v_impl_2231_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2080_, v_v_2081_, v_l_2086_);
v___x_2232_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2087_) == 0)
{
lean_object* v_size_2233_; lean_object* v_size_2234_; lean_object* v_k_2235_; lean_object* v_v_2236_; lean_object* v_l_2237_; lean_object* v_r_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; 
v_size_2233_ = lean_ctor_get(v_r_2087_, 0);
v_size_2234_ = lean_ctor_get(v_impl_2231_, 0);
v_k_2235_ = lean_ctor_get(v_impl_2231_, 1);
v_v_2236_ = lean_ctor_get(v_impl_2231_, 2);
v_l_2237_ = lean_ctor_get(v_impl_2231_, 3);
v_r_2238_ = lean_ctor_get(v_impl_2231_, 4);
lean_inc(v_r_2238_);
v___x_2239_ = lean_unsigned_to_nat(3u);
v___x_2240_ = lean_nat_mul(v___x_2239_, v_size_2233_);
v___x_2241_ = lean_nat_dec_lt(v___x_2240_, v_size_2234_);
lean_dec(v___x_2240_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2245_; 
lean_dec(v_r_2238_);
v___x_2242_ = lean_nat_add(v___x_2232_, v_size_2234_);
v___x_2243_ = lean_nat_add(v___x_2242_, v_size_2233_);
lean_dec(v___x_2242_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 3, v_impl_2231_);
lean_ctor_set(v___x_2089_, 0, v___x_2243_);
v___x_2245_ = v___x_2089_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2246_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2246_, 3, v_impl_2231_);
lean_ctor_set(v_reuseFailAlloc_2246_, 4, v_r_2087_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
else
{
lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2312_; 
lean_inc(v_l_2237_);
lean_inc(v_v_2236_);
lean_inc(v_k_2235_);
lean_inc(v_size_2234_);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_impl_2231_);
if (v_isSharedCheck_2312_ == 0)
{
lean_object* v_unused_2313_; lean_object* v_unused_2314_; lean_object* v_unused_2315_; lean_object* v_unused_2316_; lean_object* v_unused_2317_; 
v_unused_2313_ = lean_ctor_get(v_impl_2231_, 4);
lean_dec(v_unused_2313_);
v_unused_2314_ = lean_ctor_get(v_impl_2231_, 3);
lean_dec(v_unused_2314_);
v_unused_2315_ = lean_ctor_get(v_impl_2231_, 2);
lean_dec(v_unused_2315_);
v_unused_2316_ = lean_ctor_get(v_impl_2231_, 1);
lean_dec(v_unused_2316_);
v_unused_2317_ = lean_ctor_get(v_impl_2231_, 0);
lean_dec(v_unused_2317_);
v___x_2248_ = v_impl_2231_;
v_isShared_2249_ = v_isSharedCheck_2312_;
goto v_resetjp_2247_;
}
else
{
lean_dec(v_impl_2231_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2312_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v_size_2250_; lean_object* v_size_2251_; lean_object* v_k_2252_; lean_object* v_v_2253_; lean_object* v_l_2254_; lean_object* v_r_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; uint8_t v___x_2258_; 
v_size_2250_ = lean_ctor_get(v_l_2237_, 0);
v_size_2251_ = lean_ctor_get(v_r_2238_, 0);
v_k_2252_ = lean_ctor_get(v_r_2238_, 1);
v_v_2253_ = lean_ctor_get(v_r_2238_, 2);
v_l_2254_ = lean_ctor_get(v_r_2238_, 3);
v_r_2255_ = lean_ctor_get(v_r_2238_, 4);
v___x_2256_ = lean_unsigned_to_nat(2u);
v___x_2257_ = lean_nat_mul(v___x_2256_, v_size_2250_);
v___x_2258_ = lean_nat_dec_lt(v_size_2251_, v___x_2257_);
lean_dec(v___x_2257_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2287_; 
lean_inc(v_r_2255_);
lean_inc(v_l_2254_);
lean_inc(v_v_2253_);
lean_inc(v_k_2252_);
v_isSharedCheck_2287_ = !lean_is_exclusive(v_r_2238_);
if (v_isSharedCheck_2287_ == 0)
{
lean_object* v_unused_2288_; lean_object* v_unused_2289_; lean_object* v_unused_2290_; lean_object* v_unused_2291_; lean_object* v_unused_2292_; 
v_unused_2288_ = lean_ctor_get(v_r_2238_, 4);
lean_dec(v_unused_2288_);
v_unused_2289_ = lean_ctor_get(v_r_2238_, 3);
lean_dec(v_unused_2289_);
v_unused_2290_ = lean_ctor_get(v_r_2238_, 2);
lean_dec(v_unused_2290_);
v_unused_2291_ = lean_ctor_get(v_r_2238_, 1);
lean_dec(v_unused_2291_);
v_unused_2292_ = lean_ctor_get(v_r_2238_, 0);
lean_dec(v_unused_2292_);
v___x_2260_ = v_r_2238_;
v_isShared_2261_ = v_isSharedCheck_2287_;
goto v_resetjp_2259_;
}
else
{
lean_dec(v_r_2238_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2287_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___x_2275_; lean_object* v___y_2277_; 
v___x_2262_ = lean_nat_add(v___x_2232_, v_size_2234_);
lean_dec(v_size_2234_);
v___x_2263_ = lean_nat_add(v___x_2262_, v_size_2233_);
lean_dec(v___x_2262_);
v___x_2275_ = lean_nat_add(v___x_2232_, v_size_2250_);
if (lean_obj_tag(v_l_2254_) == 0)
{
lean_object* v_size_2285_; 
v_size_2285_ = lean_ctor_get(v_l_2254_, 0);
lean_inc(v_size_2285_);
v___y_2277_ = v_size_2285_;
goto v___jp_2276_;
}
else
{
lean_object* v___x_2286_; 
v___x_2286_ = lean_unsigned_to_nat(0u);
v___y_2277_ = v___x_2286_;
goto v___jp_2276_;
}
v___jp_2264_:
{
lean_object* v___x_2268_; lean_object* v___x_2270_; 
v___x_2268_ = lean_nat_add(v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec(v___y_2266_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 4, v_r_2087_);
lean_ctor_set(v___x_2260_, 3, v_r_2255_);
lean_ctor_set(v___x_2260_, 2, v_v_2085_);
lean_ctor_set(v___x_2260_, 1, v_k_2084_);
lean_ctor_set(v___x_2260_, 0, v___x_2268_);
v___x_2270_ = v___x_2260_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2268_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2274_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2274_, 3, v_r_2255_);
lean_ctor_set(v_reuseFailAlloc_2274_, 4, v_r_2087_);
v___x_2270_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2272_; 
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 4, v___x_2270_);
lean_ctor_set(v___x_2248_, 3, v___y_2265_);
lean_ctor_set(v___x_2248_, 2, v_v_2253_);
lean_ctor_set(v___x_2248_, 1, v_k_2252_);
lean_ctor_set(v___x_2248_, 0, v___x_2263_);
v___x_2272_ = v___x_2248_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2263_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_k_2252_);
lean_ctor_set(v_reuseFailAlloc_2273_, 2, v_v_2253_);
lean_ctor_set(v_reuseFailAlloc_2273_, 3, v___y_2265_);
lean_ctor_set(v_reuseFailAlloc_2273_, 4, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
v___jp_2276_:
{
lean_object* v___x_2278_; lean_object* v___x_2280_; 
v___x_2278_ = lean_nat_add(v___x_2275_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec(v___x_2275_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 4, v_l_2254_);
lean_ctor_set(v___x_2089_, 3, v_l_2237_);
lean_ctor_set(v___x_2089_, 2, v_v_2236_);
lean_ctor_set(v___x_2089_, 1, v_k_2235_);
lean_ctor_set(v___x_2089_, 0, v___x_2278_);
v___x_2280_ = v___x_2089_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2278_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_k_2235_);
lean_ctor_set(v_reuseFailAlloc_2284_, 2, v_v_2236_);
lean_ctor_set(v_reuseFailAlloc_2284_, 3, v_l_2237_);
lean_ctor_set(v_reuseFailAlloc_2284_, 4, v_l_2254_);
v___x_2280_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
lean_object* v___x_2281_; 
v___x_2281_ = lean_nat_add(v___x_2232_, v_size_2233_);
if (lean_obj_tag(v_r_2255_) == 0)
{
lean_object* v_size_2282_; 
v_size_2282_ = lean_ctor_get(v_r_2255_, 0);
lean_inc(v_size_2282_);
v___y_2265_ = v___x_2280_;
v___y_2266_ = v___x_2281_;
v___y_2267_ = v_size_2282_;
goto v___jp_2264_;
}
else
{
lean_object* v___x_2283_; 
v___x_2283_ = lean_unsigned_to_nat(0u);
v___y_2265_ = v___x_2280_;
v___y_2266_ = v___x_2281_;
v___y_2267_ = v___x_2283_;
goto v___jp_2264_;
}
}
}
}
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2298_; 
lean_del_object(v___x_2089_);
v___x_2293_ = lean_nat_add(v___x_2232_, v_size_2234_);
lean_dec(v_size_2234_);
v___x_2294_ = lean_nat_add(v___x_2293_, v_size_2233_);
lean_dec(v___x_2293_);
v___x_2295_ = lean_nat_add(v___x_2232_, v_size_2233_);
v___x_2296_ = lean_nat_add(v___x_2295_, v_size_2251_);
lean_dec(v___x_2295_);
lean_inc_ref(v_r_2087_);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 4, v_r_2087_);
lean_ctor_set(v___x_2248_, 3, v_r_2238_);
lean_ctor_set(v___x_2248_, 2, v_v_2085_);
lean_ctor_set(v___x_2248_, 1, v_k_2084_);
lean_ctor_set(v___x_2248_, 0, v___x_2296_);
v___x_2298_ = v___x_2248_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2296_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2311_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2311_, 3, v_r_2238_);
lean_ctor_set(v_reuseFailAlloc_2311_, 4, v_r_2087_);
v___x_2298_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
v_isSharedCheck_2305_ = !lean_is_exclusive(v_r_2087_);
if (v_isSharedCheck_2305_ == 0)
{
lean_object* v_unused_2306_; lean_object* v_unused_2307_; lean_object* v_unused_2308_; lean_object* v_unused_2309_; lean_object* v_unused_2310_; 
v_unused_2306_ = lean_ctor_get(v_r_2087_, 4);
lean_dec(v_unused_2306_);
v_unused_2307_ = lean_ctor_get(v_r_2087_, 3);
lean_dec(v_unused_2307_);
v_unused_2308_ = lean_ctor_get(v_r_2087_, 2);
lean_dec(v_unused_2308_);
v_unused_2309_ = lean_ctor_get(v_r_2087_, 1);
lean_dec(v_unused_2309_);
v_unused_2310_ = lean_ctor_get(v_r_2087_, 0);
lean_dec(v_unused_2310_);
v___x_2300_ = v_r_2087_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_dec(v_r_2087_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 4, v___x_2298_);
lean_ctor_set(v___x_2300_, 3, v_l_2237_);
lean_ctor_set(v___x_2300_, 2, v_v_2236_);
lean_ctor_set(v___x_2300_, 1, v_k_2235_);
lean_ctor_set(v___x_2300_, 0, v___x_2294_);
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v___x_2294_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v_k_2235_);
lean_ctor_set(v_reuseFailAlloc_2304_, 2, v_v_2236_);
lean_ctor_set(v_reuseFailAlloc_2304_, 3, v_l_2237_);
lean_ctor_set(v_reuseFailAlloc_2304_, 4, v___x_2298_);
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
}
}
else
{
lean_object* v_l_2318_; 
v_l_2318_ = lean_ctor_get(v_impl_2231_, 3);
if (lean_obj_tag(v_l_2318_) == 0)
{
lean_object* v_r_2319_; lean_object* v_k_2320_; lean_object* v_v_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2332_; 
lean_inc_ref(v_l_2318_);
v_r_2319_ = lean_ctor_get(v_impl_2231_, 4);
v_k_2320_ = lean_ctor_get(v_impl_2231_, 1);
v_v_2321_ = lean_ctor_get(v_impl_2231_, 2);
v_isSharedCheck_2332_ = !lean_is_exclusive(v_impl_2231_);
if (v_isSharedCheck_2332_ == 0)
{
lean_object* v_unused_2333_; lean_object* v_unused_2334_; 
v_unused_2333_ = lean_ctor_get(v_impl_2231_, 3);
lean_dec(v_unused_2333_);
v_unused_2334_ = lean_ctor_get(v_impl_2231_, 0);
lean_dec(v_unused_2334_);
v___x_2323_ = v_impl_2231_;
v_isShared_2324_ = v_isSharedCheck_2332_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_r_2319_);
lean_inc(v_v_2321_);
lean_inc(v_k_2320_);
lean_dec(v_impl_2231_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2332_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2325_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2319_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 3, v_r_2319_);
lean_ctor_set(v___x_2323_, 2, v_v_2085_);
lean_ctor_set(v___x_2323_, 1, v_k_2084_);
lean_ctor_set(v___x_2323_, 0, v___x_2232_);
v___x_2327_ = v___x_2323_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2331_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2331_, 3, v_r_2319_);
lean_ctor_set(v_reuseFailAlloc_2331_, 4, v_r_2319_);
v___x_2327_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2329_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 4, v___x_2327_);
lean_ctor_set(v___x_2089_, 3, v_l_2318_);
lean_ctor_set(v___x_2089_, 2, v_v_2321_);
lean_ctor_set(v___x_2089_, 1, v_k_2320_);
lean_ctor_set(v___x_2089_, 0, v___x_2325_);
v___x_2329_ = v___x_2089_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2325_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_k_2320_);
lean_ctor_set(v_reuseFailAlloc_2330_, 2, v_v_2321_);
lean_ctor_set(v_reuseFailAlloc_2330_, 3, v_l_2318_);
lean_ctor_set(v_reuseFailAlloc_2330_, 4, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
else
{
lean_object* v_r_2335_; 
v_r_2335_ = lean_ctor_get(v_impl_2231_, 4);
lean_inc(v_r_2335_);
if (lean_obj_tag(v_r_2335_) == 0)
{
lean_object* v_k_2336_; lean_object* v_v_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2360_; 
lean_inc(v_l_2318_);
v_k_2336_ = lean_ctor_get(v_impl_2231_, 1);
v_v_2337_ = lean_ctor_get(v_impl_2231_, 2);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_impl_2231_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; lean_object* v_unused_2362_; lean_object* v_unused_2363_; 
v_unused_2361_ = lean_ctor_get(v_impl_2231_, 4);
lean_dec(v_unused_2361_);
v_unused_2362_ = lean_ctor_get(v_impl_2231_, 3);
lean_dec(v_unused_2362_);
v_unused_2363_ = lean_ctor_get(v_impl_2231_, 0);
lean_dec(v_unused_2363_);
v___x_2339_ = v_impl_2231_;
v_isShared_2340_ = v_isSharedCheck_2360_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_v_2337_);
lean_inc(v_k_2336_);
lean_dec(v_impl_2231_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2360_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v_k_2341_; lean_object* v_v_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2356_; 
v_k_2341_ = lean_ctor_get(v_r_2335_, 1);
v_v_2342_ = lean_ctor_get(v_r_2335_, 2);
v_isSharedCheck_2356_ = !lean_is_exclusive(v_r_2335_);
if (v_isSharedCheck_2356_ == 0)
{
lean_object* v_unused_2357_; lean_object* v_unused_2358_; lean_object* v_unused_2359_; 
v_unused_2357_ = lean_ctor_get(v_r_2335_, 4);
lean_dec(v_unused_2357_);
v_unused_2358_ = lean_ctor_get(v_r_2335_, 3);
lean_dec(v_unused_2358_);
v_unused_2359_ = lean_ctor_get(v_r_2335_, 0);
lean_dec(v_unused_2359_);
v___x_2344_ = v_r_2335_;
v_isShared_2345_ = v_isSharedCheck_2356_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_v_2342_);
lean_inc(v_k_2341_);
lean_dec(v_r_2335_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2356_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2346_; lean_object* v___x_2348_; 
v___x_2346_ = lean_unsigned_to_nat(3u);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 4, v_l_2318_);
lean_ctor_set(v___x_2344_, 3, v_l_2318_);
lean_ctor_set(v___x_2344_, 2, v_v_2337_);
lean_ctor_set(v___x_2344_, 1, v_k_2336_);
lean_ctor_set(v___x_2344_, 0, v___x_2232_);
v___x_2348_ = v___x_2344_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v_k_2336_);
lean_ctor_set(v_reuseFailAlloc_2355_, 2, v_v_2337_);
lean_ctor_set(v_reuseFailAlloc_2355_, 3, v_l_2318_);
lean_ctor_set(v_reuseFailAlloc_2355_, 4, v_l_2318_);
v___x_2348_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2350_; 
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 4, v_l_2318_);
lean_ctor_set(v___x_2339_, 2, v_v_2085_);
lean_ctor_set(v___x_2339_, 1, v_k_2084_);
lean_ctor_set(v___x_2339_, 0, v___x_2232_);
v___x_2350_ = v___x_2339_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2354_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2354_, 3, v_l_2318_);
lean_ctor_set(v_reuseFailAlloc_2354_, 4, v_l_2318_);
v___x_2350_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2352_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 4, v___x_2350_);
lean_ctor_set(v___x_2089_, 3, v___x_2348_);
lean_ctor_set(v___x_2089_, 2, v_v_2342_);
lean_ctor_set(v___x_2089_, 1, v_k_2341_);
lean_ctor_set(v___x_2089_, 0, v___x_2346_);
v___x_2352_ = v___x_2089_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2346_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_k_2341_);
lean_ctor_set(v_reuseFailAlloc_2353_, 2, v_v_2342_);
lean_ctor_set(v_reuseFailAlloc_2353_, 3, v___x_2348_);
lean_ctor_set(v_reuseFailAlloc_2353_, 4, v___x_2350_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
}
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2366_; 
v___x_2364_ = lean_unsigned_to_nat(2u);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 4, v_r_2335_);
lean_ctor_set(v___x_2089_, 3, v_impl_2231_);
lean_ctor_set(v___x_2089_, 0, v___x_2364_);
v___x_2366_ = v___x_2089_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2364_);
lean_ctor_set(v_reuseFailAlloc_2367_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2367_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2367_, 3, v_impl_2231_);
lean_ctor_set(v_reuseFailAlloc_2367_, 4, v_r_2335_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = lean_unsigned_to_nat(1u);
v___x_2370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
lean_ctor_set(v___x_2370_, 1, v_k_2080_);
lean_ctor_set(v___x_2370_, 2, v_v_2081_);
lean_ctor_set(v___x_2370_, 3, v_t_2082_);
lean_ctor_set(v___x_2370_, 4, v_t_2082_);
return v___x_2370_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(lean_object* v_k_2371_, lean_object* v_t_2372_){
_start:
{
if (lean_obj_tag(v_t_2372_) == 0)
{
lean_object* v_k_2373_; lean_object* v_l_2374_; lean_object* v_r_2375_; uint8_t v___x_2376_; 
v_k_2373_ = lean_ctor_get(v_t_2372_, 1);
v_l_2374_ = lean_ctor_get(v_t_2372_, 3);
v_r_2375_ = lean_ctor_get(v_t_2372_, 4);
v___x_2376_ = lean_nat_dec_lt(v_k_2371_, v_k_2373_);
if (v___x_2376_ == 0)
{
uint8_t v___x_2377_; 
v___x_2377_ = lean_nat_dec_eq(v_k_2371_, v_k_2373_);
if (v___x_2377_ == 0)
{
v_t_2372_ = v_r_2375_;
goto _start;
}
else
{
return v___x_2377_;
}
}
else
{
v_t_2372_ = v_l_2374_;
goto _start;
}
}
else
{
uint8_t v___x_2380_; 
v___x_2380_ = 0;
return v___x_2380_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg___boxed(lean_object* v_k_2381_, lean_object* v_t_2382_){
_start:
{
uint8_t v_res_2383_; lean_object* v_r_2384_; 
v_res_2383_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2381_, v_t_2382_);
lean_dec(v_t_2382_);
lean_dec(v_k_2381_);
v_r_2384_ = lean_box(v_res_2383_);
return v_r_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(lean_object* v_y_2385_, lean_object* v_x_2386_, size_t v_x_2387_, size_t v_x_2388_){
_start:
{
if (lean_obj_tag(v_x_2386_) == 0)
{
lean_object* v_cs_2389_; size_t v_j_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; 
v_cs_2389_ = lean_ctor_get(v_x_2386_, 0);
v_j_2390_ = lean_usize_shift_right(v_x_2387_, v_x_2388_);
v___x_2391_ = lean_usize_to_nat(v_j_2390_);
v___x_2392_ = lean_array_get_size(v_cs_2389_);
v___x_2393_ = lean_nat_dec_lt(v___x_2391_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_dec(v___x_2391_);
lean_dec(v_y_2385_);
return v_x_2386_;
}
else
{
lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2411_; 
lean_inc_ref(v_cs_2389_);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_x_2386_);
if (v_isSharedCheck_2411_ == 0)
{
lean_object* v_unused_2412_; 
v_unused_2412_ = lean_ctor_get(v_x_2386_, 0);
lean_dec(v_unused_2412_);
v___x_2395_ = v_x_2386_;
v_isShared_2396_ = v_isSharedCheck_2411_;
goto v_resetjp_2394_;
}
else
{
lean_dec(v_x_2386_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2411_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
size_t v___x_2397_; size_t v___x_2398_; size_t v___x_2399_; size_t v_i_2400_; size_t v___x_2401_; size_t v_shift_2402_; lean_object* v_v_2403_; lean_object* v___x_2404_; lean_object* v_xs_x27_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2397_ = ((size_t)1ULL);
v___x_2398_ = lean_usize_shift_left(v___x_2397_, v_x_2388_);
v___x_2399_ = lean_usize_sub(v___x_2398_, v___x_2397_);
v_i_2400_ = lean_usize_land(v_x_2387_, v___x_2399_);
v___x_2401_ = ((size_t)5ULL);
v_shift_2402_ = lean_usize_sub(v_x_2388_, v___x_2401_);
v_v_2403_ = lean_array_fget(v_cs_2389_, v___x_2391_);
v___x_2404_ = lean_box(0);
v_xs_x27_2405_ = lean_array_fset(v_cs_2389_, v___x_2391_, v___x_2404_);
v___x_2406_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2385_, v_v_2403_, v_i_2400_, v_shift_2402_);
v___x_2407_ = lean_array_fset(v_xs_x27_2405_, v___x_2391_, v___x_2406_);
lean_dec(v___x_2391_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2407_);
v___x_2409_ = v___x_2395_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_object* v_vs_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
v_vs_2413_ = lean_ctor_get(v_x_2386_, 0);
v___x_2414_ = lean_usize_to_nat(v_x_2387_);
v___x_2415_ = lean_array_get_size(v_vs_2413_);
v___x_2416_ = lean_nat_dec_lt(v___x_2414_, v___x_2415_);
if (v___x_2416_ == 0)
{
lean_dec(v___x_2414_);
lean_dec(v_y_2385_);
return v_x_2386_;
}
else
{
lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2431_; 
lean_inc_ref(v_vs_2413_);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_x_2386_);
if (v_isSharedCheck_2431_ == 0)
{
lean_object* v_unused_2432_; 
v_unused_2432_ = lean_ctor_get(v_x_2386_, 0);
lean_dec(v_unused_2432_);
v___x_2418_ = v_x_2386_;
v_isShared_2419_ = v_isSharedCheck_2431_;
goto v_resetjp_2417_;
}
else
{
lean_dec(v_x_2386_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2431_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v_v_2420_; lean_object* v___x_2421_; lean_object* v_xs_x27_2422_; lean_object* v___y_2424_; uint8_t v___x_2429_; 
v_v_2420_ = lean_array_fget(v_vs_2413_, v___x_2414_);
v___x_2421_ = lean_box(0);
v_xs_x27_2422_ = lean_array_fset(v_vs_2413_, v___x_2414_, v___x_2421_);
v___x_2429_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2385_, v_v_2420_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2385_, v___x_2421_, v_v_2420_);
v___y_2424_ = v___x_2430_;
goto v___jp_2423_;
}
else
{
lean_dec(v_y_2385_);
v___y_2424_ = v_v_2420_;
goto v___jp_2423_;
}
v___jp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2427_; 
v___x_2425_ = lean_array_fset(v_xs_x27_2422_, v___x_2414_, v___y_2424_);
lean_dec(v___x_2414_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2425_);
v___x_2427_ = v___x_2418_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2433_, lean_object* v_x_2434_, lean_object* v_x_2435_, lean_object* v_x_2436_){
_start:
{
size_t v_x_3896__boxed_2437_; size_t v_x_3897__boxed_2438_; lean_object* v_res_2439_; 
v_x_3896__boxed_2437_ = lean_unbox_usize(v_x_2435_);
lean_dec(v_x_2435_);
v_x_3897__boxed_2438_ = lean_unbox_usize(v_x_2436_);
lean_dec(v_x_2436_);
v_res_2439_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2433_, v_x_2434_, v_x_3896__boxed_2437_, v_x_3897__boxed_2438_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(lean_object* v_y_2440_, lean_object* v_t_2441_, lean_object* v_i_2442_){
_start:
{
lean_object* v_root_2443_; lean_object* v_tail_2444_; lean_object* v_size_2445_; size_t v_shift_2446_; lean_object* v_tailOff_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2474_; 
v_root_2443_ = lean_ctor_get(v_t_2441_, 0);
v_tail_2444_ = lean_ctor_get(v_t_2441_, 1);
v_size_2445_ = lean_ctor_get(v_t_2441_, 2);
v_shift_2446_ = lean_ctor_get_usize(v_t_2441_, 4);
v_tailOff_2447_ = lean_ctor_get(v_t_2441_, 3);
v_isSharedCheck_2474_ = !lean_is_exclusive(v_t_2441_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2449_ = v_t_2441_;
v_isShared_2450_ = v_isSharedCheck_2474_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_tailOff_2447_);
lean_inc(v_size_2445_);
lean_inc(v_tail_2444_);
lean_inc(v_root_2443_);
lean_dec(v_t_2441_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2474_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
uint8_t v___x_2451_; 
v___x_2451_ = lean_nat_dec_le(v_tailOff_2447_, v_i_2442_);
if (v___x_2451_ == 0)
{
size_t v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2452_ = lean_usize_of_nat(v_i_2442_);
v___x_2453_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2440_, v_root_2443_, v___x_2452_, v_shift_2446_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2453_);
v___x_2455_ = v___x_2449_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_tail_2444_);
lean_ctor_set(v_reuseFailAlloc_2456_, 2, v_size_2445_);
lean_ctor_set(v_reuseFailAlloc_2456_, 3, v_tailOff_2447_);
lean_ctor_set_usize(v_reuseFailAlloc_2456_, 4, v_shift_2446_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
else
{
lean_object* v___x_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; 
v___x_2457_ = lean_nat_sub(v_i_2442_, v_tailOff_2447_);
v___x_2458_ = lean_array_get_size(v_tail_2444_);
v___x_2459_ = lean_nat_dec_lt(v___x_2457_, v___x_2458_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2461_; 
lean_dec(v___x_2457_);
lean_dec(v_y_2440_);
if (v_isShared_2450_ == 0)
{
v___x_2461_ = v___x_2449_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_root_2443_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v_tail_2444_);
lean_ctor_set(v_reuseFailAlloc_2462_, 2, v_size_2445_);
lean_ctor_set(v_reuseFailAlloc_2462_, 3, v_tailOff_2447_);
lean_ctor_set_usize(v_reuseFailAlloc_2462_, 4, v_shift_2446_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
else
{
lean_object* v_v_2463_; lean_object* v___x_2464_; lean_object* v_xs_x27_2465_; lean_object* v___y_2467_; uint8_t v___x_2472_; 
v_v_2463_ = lean_array_fget(v_tail_2444_, v___x_2457_);
v___x_2464_ = lean_box(0);
v_xs_x27_2465_ = lean_array_fset(v_tail_2444_, v___x_2457_, v___x_2464_);
v___x_2472_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2440_, v_v_2463_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2440_, v___x_2464_, v_v_2463_);
v___y_2467_ = v___x_2473_;
goto v___jp_2466_;
}
else
{
lean_dec(v_y_2440_);
v___y_2467_ = v_v_2463_;
goto v___jp_2466_;
}
v___jp_2466_:
{
lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2468_ = lean_array_fset(v_xs_x27_2465_, v___x_2457_, v___y_2467_);
lean_dec(v___x_2457_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 1, v___x_2468_);
v___x_2470_ = v___x_2449_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_root_2443_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v___x_2468_);
lean_ctor_set(v_reuseFailAlloc_2471_, 2, v_size_2445_);
lean_ctor_set(v_reuseFailAlloc_2471_, 3, v_tailOff_2447_);
lean_ctor_set_usize(v_reuseFailAlloc_2471_, 4, v_shift_2446_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2___boxed(lean_object* v_y_2475_, lean_object* v_t_2476_, lean_object* v_i_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2475_, v_t_2476_, v_i_2477_);
lean_dec(v_i_2477_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(lean_object* v_y_2479_, lean_object* v_x_2480_, lean_object* v_s_2481_){
_start:
{
lean_object* v_vars_2482_; lean_object* v_varMap_2483_; lean_object* v_varsHistory_2484_; lean_object* v_natToIntMap_2485_; lean_object* v_natDef_2486_; lean_object* v_dvds_2487_; lean_object* v_lowers_2488_; lean_object* v_uppers_2489_; lean_object* v_diseqs_2490_; lean_object* v_elimEqs_2491_; lean_object* v_elimStack_2492_; lean_object* v_occurs_2493_; lean_object* v_assignment_2494_; lean_object* v_nextCnstrId_2495_; uint8_t v_caseSplits_2496_; lean_object* v_steps_2497_; lean_object* v_conflict_x3f_2498_; lean_object* v_diseqSplits_2499_; lean_object* v_divMod_2500_; uint8_t v_usedCommRing_2501_; lean_object* v_nonlinearOccs_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2510_; 
v_vars_2482_ = lean_ctor_get(v_s_2481_, 0);
v_varMap_2483_ = lean_ctor_get(v_s_2481_, 1);
v_varsHistory_2484_ = lean_ctor_get(v_s_2481_, 2);
v_natToIntMap_2485_ = lean_ctor_get(v_s_2481_, 3);
v_natDef_2486_ = lean_ctor_get(v_s_2481_, 4);
v_dvds_2487_ = lean_ctor_get(v_s_2481_, 5);
v_lowers_2488_ = lean_ctor_get(v_s_2481_, 6);
v_uppers_2489_ = lean_ctor_get(v_s_2481_, 7);
v_diseqs_2490_ = lean_ctor_get(v_s_2481_, 8);
v_elimEqs_2491_ = lean_ctor_get(v_s_2481_, 9);
v_elimStack_2492_ = lean_ctor_get(v_s_2481_, 10);
v_occurs_2493_ = lean_ctor_get(v_s_2481_, 11);
v_assignment_2494_ = lean_ctor_get(v_s_2481_, 12);
v_nextCnstrId_2495_ = lean_ctor_get(v_s_2481_, 13);
v_caseSplits_2496_ = lean_ctor_get_uint8(v_s_2481_, sizeof(void*)*19);
v_steps_2497_ = lean_ctor_get(v_s_2481_, 14);
v_conflict_x3f_2498_ = lean_ctor_get(v_s_2481_, 15);
v_diseqSplits_2499_ = lean_ctor_get(v_s_2481_, 16);
v_divMod_2500_ = lean_ctor_get(v_s_2481_, 17);
v_usedCommRing_2501_ = lean_ctor_get_uint8(v_s_2481_, sizeof(void*)*19 + 1);
v_nonlinearOccs_2502_ = lean_ctor_get(v_s_2481_, 18);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_s_2481_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2504_ = v_s_2481_;
v_isShared_2505_ = v_isSharedCheck_2510_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_nonlinearOccs_2502_);
lean_inc(v_divMod_2500_);
lean_inc(v_diseqSplits_2499_);
lean_inc(v_conflict_x3f_2498_);
lean_inc(v_steps_2497_);
lean_inc(v_nextCnstrId_2495_);
lean_inc(v_assignment_2494_);
lean_inc(v_occurs_2493_);
lean_inc(v_elimStack_2492_);
lean_inc(v_elimEqs_2491_);
lean_inc(v_diseqs_2490_);
lean_inc(v_uppers_2489_);
lean_inc(v_lowers_2488_);
lean_inc(v_dvds_2487_);
lean_inc(v_natDef_2486_);
lean_inc(v_natToIntMap_2485_);
lean_inc(v_varsHistory_2484_);
lean_inc(v_varMap_2483_);
lean_inc(v_vars_2482_);
lean_dec(v_s_2481_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2510_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2506_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2479_, v_occurs_2493_, v_x_2480_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 11, v___x_2506_);
v___x_2508_ = v___x_2504_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_vars_2482_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_varMap_2483_);
lean_ctor_set(v_reuseFailAlloc_2509_, 2, v_varsHistory_2484_);
lean_ctor_set(v_reuseFailAlloc_2509_, 3, v_natToIntMap_2485_);
lean_ctor_set(v_reuseFailAlloc_2509_, 4, v_natDef_2486_);
lean_ctor_set(v_reuseFailAlloc_2509_, 5, v_dvds_2487_);
lean_ctor_set(v_reuseFailAlloc_2509_, 6, v_lowers_2488_);
lean_ctor_set(v_reuseFailAlloc_2509_, 7, v_uppers_2489_);
lean_ctor_set(v_reuseFailAlloc_2509_, 8, v_diseqs_2490_);
lean_ctor_set(v_reuseFailAlloc_2509_, 9, v_elimEqs_2491_);
lean_ctor_set(v_reuseFailAlloc_2509_, 10, v_elimStack_2492_);
lean_ctor_set(v_reuseFailAlloc_2509_, 11, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2509_, 12, v_assignment_2494_);
lean_ctor_set(v_reuseFailAlloc_2509_, 13, v_nextCnstrId_2495_);
lean_ctor_set(v_reuseFailAlloc_2509_, 14, v_steps_2497_);
lean_ctor_set(v_reuseFailAlloc_2509_, 15, v_conflict_x3f_2498_);
lean_ctor_set(v_reuseFailAlloc_2509_, 16, v_diseqSplits_2499_);
lean_ctor_set(v_reuseFailAlloc_2509_, 17, v_divMod_2500_);
lean_ctor_set(v_reuseFailAlloc_2509_, 18, v_nonlinearOccs_2502_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, sizeof(void*)*19, v_caseSplits_2496_);
lean_ctor_set_uint8(v_reuseFailAlloc_2509_, sizeof(void*)*19 + 1, v_usedCommRing_2501_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed(lean_object* v_y_2511_, lean_object* v_x_2512_, lean_object* v_s_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(v_y_2511_, v_x_2512_, v_s_2513_);
lean_dec(v_x_2512_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(lean_object* v_x_2515_, lean_object* v_y_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v___f_2520_; lean_object* v___x_2521_; 
lean_inc(v_x_2515_);
lean_inc(v_y_2516_);
v___f_2520_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2520_, 0, v_y_2516_);
lean_closure_set(v___f_2520_, 1, v_x_2515_);
v___x_2521_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2515_, v_a_2517_, v_a_2518_);
lean_dec(v_x_2515_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2533_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2533_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2533_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
uint8_t v___x_2526_; 
v___x_2526_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2516_, v_a_2522_);
lean_dec(v_a_2522_);
lean_dec(v_y_2516_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
lean_del_object(v___x_2524_);
v___x_2527_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2528_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2527_, v___f_2520_, v_a_2517_);
return v___x_2528_;
}
else
{
lean_object* v___x_2529_; lean_object* v___x_2531_; 
lean_dec_ref(v___f_2520_);
v___x_2529_ = lean_box(0);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2529_);
v___x_2531_ = v___x_2524_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2529_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec_ref(v___f_2520_);
lean_dec(v_y_2516_);
v_a_2534_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2521_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2521_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___boxed(lean_object* v_x_2542_, lean_object* v_y_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2542_, v_y_2543_, v_a_2544_, v_a_2545_);
lean_dec_ref(v_a_2545_);
lean_dec(v_a_2544_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc(lean_object* v_x_2548_, lean_object* v_y_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2548_, v_y_2549_, v_a_2550_, v_a_2558_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___boxed(lean_object* v_x_2562_, lean_object* v_y_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc(v_x_2562_, v_y_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec(v_a_2565_);
lean_dec(v_a_2564_);
return v_res_2575_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(lean_object* v_00_u03b2_2576_, lean_object* v_k_2577_, lean_object* v_t_2578_){
_start:
{
uint8_t v___x_2579_; 
v___x_2579_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2577_, v_t_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2580_, lean_object* v_k_2581_, lean_object* v_t_2582_){
_start:
{
uint8_t v_res_2583_; lean_object* v_r_2584_; 
v_res_2583_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(v_00_u03b2_2580_, v_k_2581_, v_t_2582_);
lean_dec(v_t_2582_);
lean_dec(v_k_2581_);
v_r_2584_ = lean_box(v_res_2583_);
return v_r_2584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1(lean_object* v_00_u03b2_2585_, lean_object* v_k_2586_, lean_object* v_v_2587_, lean_object* v_t_2588_, lean_object* v_hl_2589_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2586_, v_v_2587_, v_t_2588_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(lean_object* v_y_2591_, lean_object* v_p_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_){
_start:
{
if (lean_obj_tag(v_p_2592_) == 1)
{
lean_object* v_v_2596_; lean_object* v_p_2597_; lean_object* v___x_2598_; 
v_v_2596_ = lean_ctor_get(v_p_2592_, 1);
lean_inc(v_v_2596_);
v_p_2597_ = lean_ctor_get(v_p_2592_, 2);
lean_inc_ref(v_p_2597_);
lean_dec_ref_known(v_p_2592_, 3);
lean_inc(v_y_2591_);
v___x_2598_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_v_2596_, v_y_2591_, v_a_2593_, v_a_2594_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_dec_ref_known(v___x_2598_, 1);
v_p_2592_ = v_p_2597_;
goto _start;
}
else
{
lean_dec_ref(v_p_2597_);
lean_dec(v_y_2591_);
return v___x_2598_;
}
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec_ref(v_p_2592_);
lean_dec(v_y_2591_);
v___x_2600_ = lean_box(0);
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
return v___x_2601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg___boxed(lean_object* v_y_2602_, lean_object* v_p_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2602_, v_p_2603_, v_a_2604_, v_a_2605_);
lean_dec_ref(v_a_2605_);
lean_dec(v_a_2604_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(lean_object* v_y_2608_, lean_object* v_p_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2608_, v_p_2609_, v_a_2610_, v_a_2618_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___boxed(lean_object* v_y_2622_, lean_object* v_p_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(v_y_2622_, v_p_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
lean_dec(v_a_2631_);
lean_dec_ref(v_a_2630_);
lean_dec(v_a_2629_);
lean_dec_ref(v_a_2628_);
lean_dec(v_a_2627_);
lean_dec_ref(v_a_2626_);
lean_dec(v_a_2625_);
lean_dec(v_a_2624_);
return v_res_2635_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = ((lean_object*)(l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__0));
v___x_2638_ = l_Lean_stringToMessageData(v___x_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg(lean_object* v_p_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_){
_start:
{
if (lean_obj_tag(v_p_2639_) == 1)
{
lean_object* v_v_2646_; lean_object* v_p_2647_; lean_object* v___x_2648_; 
v_v_2646_ = lean_ctor_get(v_p_2639_, 1);
lean_inc(v_v_2646_);
v_p_2647_ = lean_ctor_get(v_p_2639_, 2);
lean_inc_ref(v_p_2647_);
lean_dec_ref_known(v_p_2639_, 3);
v___x_2648_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_v_2646_, v_p_2647_, v_a_2640_, v_a_2643_);
return v___x_2648_;
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
lean_dec_ref(v_p_2639_);
v___x_2649_ = lean_obj_once(&l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1, &l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1_once, _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1);
v___x_2650_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2649_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
return v___x_2650_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg___boxed(lean_object* v_p_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs(lean_object* v_p_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2659_, v_a_2660_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___boxed(lean_object* v_p_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_Int_Internal_Linear_Poly_updateOccs(v_p_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
lean_dec(v_a_2674_);
lean_dec(v_a_2673_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go_spec__0(lean_object* v_a_2685_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = l_Rat_ofInt(v_a_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(lean_object* v_a_2687_, lean_object* v_v_2688_, lean_object* v_a_2689_){
_start:
{
if (lean_obj_tag(v_a_2689_) == 0)
{
lean_object* v_k_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2699_; 
v_k_2690_ = lean_ctor_get(v_a_2689_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_a_2689_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2692_ = v_a_2689_;
v_isShared_2693_ = v_isSharedCheck_2699_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_k_2690_);
lean_dec(v_a_2689_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2699_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2697_; 
v___x_2694_ = l_Rat_ofInt(v_k_2690_);
v___x_2695_ = l_Rat_add(v_v_2688_, v___x_2694_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set_tag(v___x_2692_, 1);
lean_ctor_set(v___x_2692_, 0, v___x_2695_);
v___x_2697_ = v___x_2692_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2695_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
else
{
lean_object* v_k_2700_; lean_object* v_v_2701_; lean_object* v_p_2702_; lean_object* v_size_2703_; uint8_t v___x_2704_; 
v_k_2700_ = lean_ctor_get(v_a_2689_, 0);
lean_inc(v_k_2700_);
v_v_2701_ = lean_ctor_get(v_a_2689_, 1);
lean_inc(v_v_2701_);
v_p_2702_ = lean_ctor_get(v_a_2689_, 2);
lean_inc_ref(v_p_2702_);
lean_dec_ref_known(v_a_2689_, 3);
v_size_2703_ = lean_ctor_get(v_a_2687_, 2);
v___x_2704_ = lean_nat_dec_lt(v_v_2701_, v_size_2703_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; 
lean_dec_ref(v_p_2702_);
lean_dec(v_v_2701_);
lean_dec(v_k_2700_);
lean_dec_ref(v_v_2688_);
v___x_2705_ = lean_box(0);
return v___x_2705_;
}
else
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2706_ = l_instInhabitedRat;
v___x_2707_ = l_Rat_ofInt(v_k_2700_);
v___x_2708_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2706_, v_a_2687_, v_v_2701_);
lean_dec(v_v_2701_);
v___x_2709_ = l_Rat_mul(v___x_2707_, v___x_2708_);
lean_dec_ref(v___x_2707_);
v___x_2710_ = l_Rat_add(v_v_2688_, v___x_2709_);
v_v_2688_ = v___x_2710_;
v_a_2689_ = v_p_2702_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go___boxed(lean_object* v_a_2712_, lean_object* v_v_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_a_2712_, v_v_2713_, v_a_2714_);
lean_dec_ref(v_a_2712_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(lean_object* v_a_2716_){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = lean_nat_to_int(v_a_2716_);
v___x_2718_ = l_Rat_ofInt(v___x_2717_);
return v___x_2718_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = lean_unsigned_to_nat(0u);
v___x_2720_ = l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(v___x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg(lean_object* v_p_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2722_, v_a_2723_);
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
lean_object* v_assignment_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2734_; 
v_assignment_2730_ = lean_ctor_get(v_a_2726_, 12);
lean_inc_ref(v_assignment_2730_);
lean_dec(v_a_2726_);
v___x_2731_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2732_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_assignment_2730_, v___x_2731_, v_p_2721_);
lean_dec_ref(v_assignment_2730_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2732_);
v___x_2734_ = v___x_2728_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec_ref(v_p_2721_);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg___boxed(lean_object* v_p_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2745_, v_a_2746_, v_a_2747_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f(lean_object* v_p_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2750_, v_a_2751_, v_a_2759_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___boxed(lean_object* v_p_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Int_Internal_Linear_Poly_eval_x3f(v_p_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec(v_a_2764_);
return v_res_2775_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(lean_object* v_c_2776_){
_start:
{
lean_object* v_p_2777_; uint8_t v___x_2778_; 
v_p_2777_ = lean_ctor_get(v_c_2776_, 0);
v___x_2778_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat___boxed(lean_object* v_c_2779_){
_start:
{
uint8_t v_res_2780_; lean_object* v_r_2781_; 
v_res_2780_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(v_c_2779_);
lean_dec_ref(v_c_2779_);
v_r_2781_ = lean_box(v_res_2780_);
return v_r_2781_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(lean_object* v_c_2782_){
_start:
{
lean_object* v_d_2783_; lean_object* v_p_2784_; uint8_t v___x_2785_; 
v_d_2783_ = lean_ctor_get(v_c_2782_, 0);
lean_inc(v_d_2783_);
v_p_2784_ = lean_ctor_get(v_c_2782_, 1);
lean_inc_ref(v_p_2784_);
lean_dec_ref(v_c_2782_);
v___x_2785_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_2783_, v_p_2784_);
lean_dec_ref(v_p_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat___boxed(lean_object* v_c_2786_){
_start:
{
uint8_t v_res_2787_; lean_object* v_r_2788_; 
v_res_2787_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(v_c_2786_);
v_r_2788_ = lean_box(v_res_2787_);
return v_r_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object* v_c_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v_d_2793_; lean_object* v_p_2794_; lean_object* v___x_2795_; 
v_d_2793_ = lean_ctor_get(v_c_2789_, 0);
lean_inc(v_d_2793_);
v_p_2794_ = lean_ctor_get(v_c_2789_, 1);
lean_inc_ref(v_p_2794_);
lean_dec_ref(v_c_2789_);
v___x_2795_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2794_, v_a_2790_, v_a_2791_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2823_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2798_ = v___x_2795_;
v_isShared_2799_ = v_isSharedCheck_2823_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2823_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
if (lean_obj_tag(v_a_2796_) == 1)
{
lean_object* v_val_2800_; lean_object* v_num_2801_; lean_object* v_den_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; 
v_val_2800_ = lean_ctor_get(v_a_2796_, 0);
lean_inc(v_val_2800_);
lean_dec_ref_known(v_a_2796_, 1);
v_num_2801_ = lean_ctor_get(v_val_2800_, 0);
lean_inc(v_num_2801_);
v_den_2802_ = lean_ctor_get(v_val_2800_, 1);
lean_inc(v_den_2802_);
lean_dec(v_val_2800_);
v___x_2803_ = lean_unsigned_to_nat(1u);
v___x_2804_ = lean_nat_dec_eq(v_den_2802_, v___x_2803_);
lean_dec(v_den_2802_);
if (v___x_2804_ == 0)
{
uint8_t v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2808_; 
lean_dec(v_num_2801_);
lean_dec(v_d_2793_);
v___x_2805_ = 0;
v___x_2806_ = lean_box(v___x_2805_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2806_);
v___x_2808_ = v___x_2798_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2806_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
else
{
lean_object* v___x_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; uint8_t v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2816_; 
v___x_2810_ = lean_int_emod(v_num_2801_, v_d_2793_);
lean_dec(v_d_2793_);
lean_dec(v_num_2801_);
v___x_2811_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_2812_ = lean_int_dec_eq(v___x_2810_, v___x_2811_);
lean_dec(v___x_2810_);
v___x_2813_ = l_Lean_Bool_toLBool(v___x_2812_);
v___x_2814_ = lean_box(v___x_2813_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2814_);
v___x_2816_ = v___x_2798_;
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
uint8_t v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2821_; 
lean_dec(v_a_2796_);
lean_dec(v_d_2793_);
v___x_2818_ = 2;
v___x_2819_ = lean_box(v___x_2818_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2819_);
v___x_2821_ = v___x_2798_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2819_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_dec(v_d_2793_);
v_a_2824_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2795_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2795_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg___boxed(lean_object* v_c_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2832_, v_a_2833_, v_a_2834_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(lean_object* v_c_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2837_, v_a_2838_, v_a_2846_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___boxed(lean_object* v_c_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(v_c_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
lean_dec(v_a_2860_);
lean_dec_ref(v_a_2859_);
lean_dec(v_a_2858_);
lean_dec_ref(v_a_2857_);
lean_dec(v_a_2856_);
lean_dec_ref(v_a_2855_);
lean_dec(v_a_2854_);
lean_dec_ref(v_a_2853_);
lean_dec(v_a_2852_);
lean_dec(v_a_2851_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg(lean_object* v_p_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2863_, v_a_2864_, v_a_2865_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2885_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2870_ = v___x_2867_;
v_isShared_2871_ = v_isSharedCheck_2885_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2867_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2885_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
if (lean_obj_tag(v_a_2868_) == 1)
{
lean_object* v_val_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; uint8_t v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2878_; 
v_val_2872_ = lean_ctor_get(v_a_2868_, 0);
lean_inc(v_val_2872_);
lean_dec_ref_known(v_a_2868_, 1);
v___x_2873_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2874_ = l_Rat_instDecidableLe(v_val_2872_, v___x_2873_);
v___x_2875_ = l_Lean_Bool_toLBool(v___x_2874_);
v___x_2876_ = lean_box(v___x_2875_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v___x_2876_);
v___x_2878_ = v___x_2870_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
else
{
uint8_t v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2883_; 
lean_dec(v_a_2868_);
v___x_2880_ = 2;
v___x_2881_ = lean_box(v___x_2880_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v___x_2881_);
v___x_2883_ = v___x_2870_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
v_a_2886_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2867_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2867_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg___boxed(lean_object* v_p_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2894_, v_a_2895_, v_a_2896_);
lean_dec_ref(v_a_2896_);
lean_dec(v_a_2895_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe(lean_object* v_p_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2899_, v_a_2900_, v_a_2908_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___boxed(lean_object* v_p_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Int_Internal_Linear_Poly_satisfiedLe(v_p_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_);
lean_dec(v_a_2922_);
lean_dec_ref(v_a_2921_);
lean_dec(v_a_2920_);
lean_dec_ref(v_a_2919_);
lean_dec(v_a_2918_);
lean_dec_ref(v_a_2917_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec(v_a_2913_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(lean_object* v_c_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v_p_2929_; lean_object* v___x_2930_; 
v_p_2929_ = lean_ctor_get(v_c_2925_, 0);
lean_inc_ref(v_p_2929_);
lean_dec_ref(v_c_2925_);
v___x_2930_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2929_, v_a_2926_, v_a_2927_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg___boxed(lean_object* v_c_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2931_, v_a_2932_, v_a_2933_);
lean_dec_ref(v_a_2933_);
lean_dec(v_a_2932_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(lean_object* v_c_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2936_, v_a_2937_, v_a_2945_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___boxed(lean_object* v_c_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(v_c_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
lean_dec(v_a_2959_);
lean_dec_ref(v_a_2958_);
lean_dec(v_a_2957_);
lean_dec_ref(v_a_2956_);
lean_dec(v_a_2955_);
lean_dec_ref(v_a_2954_);
lean_dec(v_a_2953_);
lean_dec_ref(v_a_2952_);
lean_dec(v_a_2951_);
lean_dec(v_a_2950_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(lean_object* v_c_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v_p_2966_; lean_object* v___x_2967_; 
v_p_2966_ = lean_ctor_get(v_c_2962_, 0);
lean_inc_ref(v_p_2966_);
lean_dec_ref(v_c_2962_);
v___x_2967_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2966_, v_a_2963_, v_a_2964_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2987_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2970_ = v___x_2967_;
v_isShared_2971_ = v_isSharedCheck_2987_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2967_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2987_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
uint8_t v___y_2973_; 
if (lean_obj_tag(v_a_2968_) == 1)
{
lean_object* v_val_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v_val_2979_ = lean_ctor_get(v_a_2968_, 0);
lean_inc(v_val_2979_);
lean_dec_ref_known(v_a_2968_, 1);
v___x_2980_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2981_ = l_instDecidableEqRat_decEq(v_val_2979_, v___x_2980_);
lean_dec(v_val_2979_);
if (v___x_2981_ == 0)
{
uint8_t v___x_2982_; 
v___x_2982_ = 1;
v___y_2973_ = v___x_2982_;
goto v___jp_2972_;
}
else
{
uint8_t v___x_2983_; 
v___x_2983_ = 0;
v___y_2973_ = v___x_2983_;
goto v___jp_2972_;
}
}
else
{
uint8_t v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
lean_del_object(v___x_2970_);
lean_dec(v_a_2968_);
v___x_2984_ = 2;
v___x_2985_ = lean_box(v___x_2984_);
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
return v___x_2986_;
}
v___jp_2972_:
{
uint8_t v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2977_; 
v___x_2974_ = l_Lean_Bool_toLBool(v___y_2973_);
v___x_2975_ = lean_box(v___x_2974_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 0, v___x_2975_);
v___x_2977_ = v___x_2970_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
else
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
v_a_2988_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___x_2967_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2967_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg___boxed(lean_object* v_c_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_2996_, v_a_2997_, v_a_2998_);
lean_dec_ref(v_a_2998_);
lean_dec(v_a_2997_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(lean_object* v_c_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_3001_, v_a_3002_, v_a_3010_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___boxed(lean_object* v_c_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(v_c_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
lean_dec(v_a_3020_);
lean_dec_ref(v_a_3019_);
lean_dec(v_a_3018_);
lean_dec_ref(v_a_3017_);
lean_dec(v_a_3016_);
lean_dec(v_a_3015_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(lean_object* v_c_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v_p_3031_; lean_object* v___x_3032_; 
v_p_3031_ = lean_ctor_get(v_c_3027_, 0);
lean_inc_ref(v_p_3031_);
lean_dec_ref(v_c_3027_);
v___x_3032_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3031_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3050_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3035_ = v___x_3032_;
v_isShared_3036_ = v_isSharedCheck_3050_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3032_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3050_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
if (lean_obj_tag(v_a_3033_) == 1)
{
lean_object* v_val_3037_; lean_object* v___x_3038_; uint8_t v___x_3039_; uint8_t v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3043_; 
v_val_3037_ = lean_ctor_get(v_a_3033_, 0);
lean_inc(v_val_3037_);
lean_dec_ref_known(v_a_3033_, 1);
v___x_3038_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_3039_ = l_instDecidableEqRat_decEq(v_val_3037_, v___x_3038_);
lean_dec(v_val_3037_);
v___x_3040_ = l_Lean_Bool_toLBool(v___x_3039_);
v___x_3041_ = lean_box(v___x_3040_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 0, v___x_3041_);
v___x_3043_ = v___x_3035_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3041_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
else
{
uint8_t v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3048_; 
lean_dec(v_a_3033_);
v___x_3045_ = 2;
v___x_3046_ = lean_box(v___x_3045_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 0, v___x_3046_);
v___x_3048_ = v___x_3035_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
v_a_3051_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3032_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3032_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg___boxed(lean_object* v_c_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_3059_, v_a_3060_, v_a_3061_);
lean_dec_ref(v_a_3061_);
lean_dec(v_a_3060_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(lean_object* v_c_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_3064_, v_a_3065_, v_a_3073_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___boxed(lean_object* v_c_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(v_c_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
lean_dec(v_a_3087_);
lean_dec_ref(v_a_3086_);
lean_dec(v_a_3085_);
lean_dec_ref(v_a_3084_);
lean_dec(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
lean_dec(v_a_3079_);
lean_dec(v_a_3078_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg(lean_object* v_p_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_){
_start:
{
if (lean_obj_tag(v_p_3090_) == 0)
{
lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3101_; 
v_isSharedCheck_3101_ = !lean_is_exclusive(v_p_3090_);
if (v_isSharedCheck_3101_ == 0)
{
lean_object* v_unused_3102_; 
v_unused_3102_ = lean_ctor_get(v_p_3090_, 0);
lean_dec(v_unused_3102_);
v___x_3095_ = v_p_3090_;
v_isShared_3096_ = v_isSharedCheck_3101_;
goto v_resetjp_3094_;
}
else
{
lean_dec(v_p_3090_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3101_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3097_; lean_object* v___x_3099_; 
v___x_3097_ = lean_box(0);
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 0, v___x_3097_);
v___x_3099_ = v___x_3095_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
else
{
lean_object* v_k_3103_; lean_object* v_v_3104_; lean_object* v_p_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v_k_3103_ = lean_ctor_get(v_p_3090_, 0);
lean_inc(v_k_3103_);
v_v_3104_ = lean_ctor_get(v_p_3090_, 1);
lean_inc(v_v_3104_);
v_p_3105_ = lean_ctor_get(v_p_3090_, 2);
lean_inc_ref(v_p_3105_);
lean_dec_ref_known(v_p_3090_, 3);
v___x_3106_ = lean_box(0);
v___x_3107_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3091_, v_a_3092_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3133_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3110_ = v___x_3107_;
v_isShared_3111_ = v_isSharedCheck_3133_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3133_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___y_3113_; lean_object* v_elimEqs_3128_; lean_object* v_size_3129_; uint8_t v___x_3130_; 
v_elimEqs_3128_ = lean_ctor_get(v_a_3108_, 9);
lean_inc_ref(v_elimEqs_3128_);
lean_dec(v_a_3108_);
v_size_3129_ = lean_ctor_get(v_elimEqs_3128_, 2);
v___x_3130_ = lean_nat_dec_lt(v_v_3104_, v_size_3129_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3131_; 
lean_dec_ref(v_elimEqs_3128_);
v___x_3131_ = l_outOfBounds___redArg(v___x_3106_);
v___y_3113_ = v___x_3131_;
goto v___jp_3112_;
}
else
{
lean_object* v___x_3132_; 
v___x_3132_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3106_, v_elimEqs_3128_, v_v_3104_);
lean_dec_ref(v_elimEqs_3128_);
v___y_3113_ = v___x_3132_;
goto v___jp_3112_;
}
v___jp_3112_:
{
if (lean_obj_tag(v___y_3113_) == 1)
{
lean_object* v_val_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3126_; 
lean_dec_ref(v_p_3105_);
v_val_3114_ = lean_ctor_get(v___y_3113_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___y_3113_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3116_ = v___y_3113_;
v_isShared_3117_ = v_isSharedCheck_3126_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_val_3114_);
lean_dec(v___y_3113_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3126_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3121_; 
v___x_3118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3118_, 0, v_v_3104_);
lean_ctor_set(v___x_3118_, 1, v_val_3114_);
v___x_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3119_, 0, v_k_3103_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 0, v___x_3119_);
v___x_3121_ = v___x_3116_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3119_);
v___x_3121_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
lean_object* v___x_3123_; 
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v___x_3121_);
v___x_3123_ = v___x_3110_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
else
{
lean_dec(v___y_3113_);
lean_del_object(v___x_3110_);
lean_dec(v_v_3104_);
lean_dec(v_k_3103_);
v_p_3090_ = v_p_3105_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_dec_ref(v_p_3105_);
lean_dec(v_v_3104_);
lean_dec(v_k_3103_);
v_a_3134_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3107_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3107_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg___boxed(lean_object* v_p_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_3142_, v_a_3143_, v_a_3144_);
lean_dec_ref(v_a_3144_);
lean_dec(v_a_3143_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst(lean_object* v_p_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_){
_start:
{
lean_object* v___x_3159_; 
v___x_3159_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_3147_, v_a_3148_, v_a_3156_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___boxed(lean_object* v_p_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Int_Internal_Linear_Poly_findVarToSubst(v_p_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(lean_object* v_pred_3173_){
_start:
{
lean_object* v_c_u2081_3174_; lean_object* v_c_u2082_3175_; uint8_t v_left_3176_; lean_object* v_c_u2083_x3f_3177_; lean_object* v_p_3178_; lean_object* v_p_3179_; lean_object* v_a_3180_; lean_object* v_b_3181_; 
v_c_u2081_3174_ = lean_ctor_get(v_pred_3173_, 0);
v_c_u2082_3175_ = lean_ctor_get(v_pred_3173_, 1);
v_left_3176_ = lean_ctor_get_uint8(v_pred_3173_, sizeof(void*)*3);
v_c_u2083_x3f_3177_ = lean_ctor_get(v_pred_3173_, 2);
v_p_3178_ = lean_ctor_get(v_c_u2081_3174_, 0);
v_p_3179_ = lean_ctor_get(v_c_u2082_3175_, 0);
v_a_3180_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3178_);
v_b_3181_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3179_);
if (lean_obj_tag(v_c_u2083_x3f_3177_) == 0)
{
if (v_left_3176_ == 0)
{
lean_object* v___x_3182_; 
lean_dec(v_a_3180_);
v___x_3182_ = lean_nat_abs(v_b_3181_);
lean_dec(v_b_3181_);
return v___x_3182_;
}
else
{
lean_object* v___x_3183_; 
lean_dec(v_b_3181_);
v___x_3183_ = lean_nat_abs(v_a_3180_);
lean_dec(v_a_3180_);
return v___x_3183_;
}
}
else
{
lean_object* v_val_3184_; lean_object* v_d_3185_; lean_object* v_p_3186_; lean_object* v_c_3187_; 
v_val_3184_ = lean_ctor_get(v_c_u2083_x3f_3177_, 0);
v_d_3185_ = lean_ctor_get(v_val_3184_, 0);
v_p_3186_ = lean_ctor_get(v_val_3184_, 1);
v_c_3187_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3186_);
if (v_left_3176_ == 0)
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
lean_dec(v_a_3180_);
v___x_3188_ = lean_int_mul(v_b_3181_, v_d_3185_);
v___x_3189_ = l_Int_gcd(v___x_3188_, v_c_3187_);
lean_dec(v_c_3187_);
v___x_3190_ = lean_nat_to_int(v___x_3189_);
v___x_3191_ = lean_int_ediv(v___x_3188_, v___x_3190_);
lean_dec(v___x_3190_);
lean_dec(v___x_3188_);
v___x_3192_ = l_Int_lcm(v_b_3181_, v___x_3191_);
lean_dec(v___x_3191_);
lean_dec(v_b_3181_);
return v___x_3192_;
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
lean_dec(v_b_3181_);
v___x_3193_ = lean_int_mul(v_a_3180_, v_d_3185_);
v___x_3194_ = l_Int_gcd(v___x_3193_, v_c_3187_);
lean_dec(v_c_3187_);
v___x_3195_ = lean_nat_to_int(v___x_3194_);
v___x_3196_ = lean_int_ediv(v___x_3193_, v___x_3195_);
lean_dec(v___x_3195_);
lean_dec(v___x_3193_);
v___x_3197_ = l_Int_lcm(v_a_3180_, v___x_3196_);
lean_dec(v___x_3196_);
lean_dec(v_a_3180_);
return v___x_3197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases___boxed(lean_object* v_pred_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(v_pred_3198_);
lean_dec_ref(v_pred_3198_);
return v_res_3199_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0));
v___x_3202_ = l_Lean_stringToMessageData(v___x_3201_);
return v___x_3202_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4(void){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3));
v___x_3207_ = l_Lean_MessageData_ofFormat(v___x_3206_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(lean_object* v_pred_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_){
_start:
{
lean_object* v_c_u2081_3212_; lean_object* v_c_u2082_3213_; lean_object* v_c_u2083_x3f_3214_; lean_object* v___x_3215_; 
v_c_u2081_3212_ = lean_ctor_get(v_pred_3208_, 0);
lean_inc_ref(v_c_u2081_3212_);
v_c_u2082_3213_ = lean_ctor_get(v_pred_3208_, 1);
lean_inc_ref(v_c_u2082_3213_);
v_c_u2083_x3f_3214_ = lean_ctor_get(v_pred_3208_, 2);
lean_inc(v_c_u2083_x3f_3214_);
lean_dec_ref(v_pred_3208_);
v___x_3215_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3212_, v_a_3209_, v_a_3210_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_a_3216_; lean_object* v___x_3217_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_a_3216_);
lean_dec_ref_known(v___x_3215_, 1);
v___x_3217_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3213_, v_a_3209_, v_a_3210_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3236_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3220_ = v___x_3217_;
v_isShared_3221_ = v_isSharedCheck_3236_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3217_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3236_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v_____do__lift_3223_; 
if (lean_obj_tag(v_c_u2083_x3f_3214_) == 1)
{
lean_object* v_val_3232_; lean_object* v___x_3233_; 
v_val_3232_ = lean_ctor_get(v_c_u2083_x3f_3214_, 0);
lean_inc(v_val_3232_);
lean_dec_ref_known(v_c_u2083_x3f_3214_, 1);
v___x_3233_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_val_3232_, v_a_3209_, v_a_3210_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
lean_inc(v_a_3234_);
lean_dec_ref_known(v___x_3233_, 1);
v_____do__lift_3223_ = v_a_3234_;
goto v___jp_3222_;
}
else
{
lean_del_object(v___x_3220_);
lean_dec(v_a_3218_);
lean_dec(v_a_3216_);
return v___x_3233_;
}
}
else
{
lean_object* v___x_3235_; 
lean_dec(v_c_u2083_x3f_3214_);
v___x_3235_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4);
v_____do__lift_3223_ = v___x_3235_;
goto v___jp_3222_;
}
v___jp_3222_:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3224_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3225_, 0, v_a_3216_);
lean_ctor_set(v___x_3225_, 1, v___x_3224_);
v___x_3226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
lean_ctor_set(v___x_3226_, 1, v_a_3218_);
v___x_3227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
lean_ctor_set(v___x_3227_, 1, v___x_3224_);
v___x_3228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
lean_ctor_set(v___x_3228_, 1, v_____do__lift_3223_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 0, v___x_3228_);
v___x_3230_ = v___x_3220_;
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
lean_dec(v_a_3216_);
lean_dec(v_c_u2083_x3f_3214_);
return v___x_3217_;
}
}
else
{
lean_dec(v_c_u2083_x3f_3214_);
lean_dec_ref(v_c_u2082_3213_);
return v___x_3215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___boxed(lean_object* v_pred_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_3237_, v_a_3238_, v_a_3239_);
lean_dec_ref(v_a_3239_);
lean_dec(v_a_3238_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(lean_object* v_pred_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_){
_start:
{
lean_object* v___x_3254_; 
v___x_3254_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_3242_, v_a_3243_, v_a_3251_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___boxed(lean_object* v_pred_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(v_pred_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_);
lean_dec(v_a_3265_);
lean_dec_ref(v_a_3264_);
lean_dec(v_a_3263_);
lean_dec_ref(v_a_3262_);
lean_dec(v_a_3261_);
lean_dec_ref(v_a_3260_);
lean_dec(v_a_3259_);
lean_dec_ref(v_a_3258_);
lean_dec(v_a_3257_);
lean_dec(v_a_3256_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(lean_object* v_h_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_){
_start:
{
switch(lean_obj_tag(v_h_3268_))
{
case 0:
{
lean_object* v_c_3272_; lean_object* v___x_3273_; 
v_c_3272_ = lean_ctor_get(v_h_3268_, 0);
lean_inc_ref(v_c_3272_);
lean_dec_ref_known(v_h_3268_, 1);
v___x_3273_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_3272_, v_a_3269_, v_a_3270_);
return v___x_3273_;
}
case 1:
{
lean_object* v_c_3274_; lean_object* v___x_3275_; 
v_c_3274_ = lean_ctor_get(v_h_3268_, 0);
lean_inc_ref(v_c_3274_);
lean_dec_ref_known(v_h_3268_, 1);
v___x_3275_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3274_, v_a_3269_, v_a_3270_);
return v___x_3275_;
}
case 2:
{
lean_object* v_c_3276_; lean_object* v___x_3277_; 
v_c_3276_ = lean_ctor_get(v_h_3268_, 0);
lean_inc_ref(v_c_3276_);
lean_dec_ref_known(v_h_3268_, 1);
v___x_3277_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_3276_, v_a_3269_, v_a_3270_);
return v___x_3277_;
}
case 3:
{
lean_object* v_c_3278_; lean_object* v___x_3279_; 
v_c_3278_ = lean_ctor_get(v_h_3268_, 0);
lean_inc_ref(v_c_3278_);
lean_dec_ref_known(v_h_3268_, 1);
v___x_3279_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_3278_, v_a_3269_, v_a_3270_);
return v___x_3279_;
}
default: 
{
lean_object* v_c_u2081_3280_; lean_object* v_c_u2082_3281_; lean_object* v_c_u2083_3282_; lean_object* v___x_3283_; 
v_c_u2081_3280_ = lean_ctor_get(v_h_3268_, 0);
lean_inc_ref(v_c_u2081_3280_);
v_c_u2082_3281_ = lean_ctor_get(v_h_3268_, 1);
lean_inc_ref(v_c_u2082_3281_);
v_c_u2083_3282_ = lean_ctor_get(v_h_3268_, 2);
lean_inc_ref(v_c_u2083_3282_);
lean_dec_ref_known(v_h_3268_, 3);
v___x_3283_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3280_, v_a_3269_, v_a_3270_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___x_3285_; 
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
lean_inc(v_a_3284_);
lean_dec_ref_known(v___x_3283_, 1);
v___x_3285_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3281_, v_a_3269_, v_a_3270_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3287_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
lean_dec_ref_known(v___x_3285_, 1);
v___x_3287_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2083_3282_, v_a_3269_, v_a_3270_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3300_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3290_ = v___x_3287_;
v_isShared_3291_ = v_isSharedCheck_3300_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3287_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3300_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3298_; 
v___x_3292_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3293_, 0, v_a_3284_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
lean_ctor_set(v___x_3294_, 1, v_a_3286_);
v___x_3295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3294_);
lean_ctor_set(v___x_3295_, 1, v___x_3292_);
v___x_3296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3295_);
lean_ctor_set(v___x_3296_, 1, v_a_3288_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 0, v___x_3296_);
v___x_3298_ = v___x_3290_;
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
else
{
lean_dec(v_a_3286_);
lean_dec(v_a_3284_);
return v___x_3287_;
}
}
else
{
lean_dec(v_a_3284_);
lean_dec_ref(v_c_u2083_3282_);
return v___x_3285_;
}
}
else
{
lean_dec_ref(v_c_u2083_3282_);
lean_dec_ref(v_c_u2082_3281_);
return v___x_3283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg___boxed(lean_object* v_h_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3301_, v_a_3302_, v_a_3303_);
lean_dec_ref(v_a_3303_);
lean_dec(v_a_3302_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(lean_object* v_h_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3306_, v_a_3307_, v_a_3315_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___boxed(lean_object* v_h_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(v_h_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_);
lean_dec(v_a_3329_);
lean_dec_ref(v_a_3328_);
lean_dec(v_a_3327_);
lean_dec_ref(v_a_3326_);
lean_dec(v_a_3325_);
lean_dec_ref(v_a_3324_);
lean_dec(v_a_3323_);
lean_dec_ref(v_a_3322_);
lean_dec(v_a_3321_);
lean_dec(v_a_3320_);
return v_res_3331_;
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
