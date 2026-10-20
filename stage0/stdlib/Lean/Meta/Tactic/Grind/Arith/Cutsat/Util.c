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
v_lia_291_ = lean_ctor_get_uint8(v_a_287_, sizeof(void*)*14 + 24);
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
v_conflict_x3f_446_ = lean_ctor_get(v_a_442_, 15);
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
lean_object* v_vars_904_; lean_object* v_varMap_905_; lean_object* v_varsHistory_906_; lean_object* v_natToIntMap_907_; lean_object* v_natDef_908_; lean_object* v_dvds_909_; lean_object* v_lowers_910_; lean_object* v_uppers_911_; lean_object* v_diseqs_912_; lean_object* v_elimEqs_913_; lean_object* v_elimStack_914_; lean_object* v_occurs_915_; lean_object* v_assignment_916_; lean_object* v_nextCnstrId_917_; uint8_t v_caseSplits_918_; lean_object* v_steps_919_; lean_object* v_conflict_x3f_920_; lean_object* v_diseqSplits_921_; lean_object* v_divMod_922_; uint8_t v_usedCommRing_923_; lean_object* v_nonlinearOccs_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_932_; 
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
v_caseSplits_918_ = lean_ctor_get_uint8(v_s_903_, sizeof(void*)*19);
v_steps_919_ = lean_ctor_get(v_s_903_, 14);
v_conflict_x3f_920_ = lean_ctor_get(v_s_903_, 15);
v_diseqSplits_921_ = lean_ctor_get(v_s_903_, 16);
v_divMod_922_ = lean_ctor_get(v_s_903_, 17);
v_usedCommRing_923_ = lean_ctor_get_uint8(v_s_903_, sizeof(void*)*19 + 1);
v_nonlinearOccs_924_ = lean_ctor_get(v_s_903_, 18);
v_isSharedCheck_932_ = !lean_is_exclusive(v_s_903_);
if (v_isSharedCheck_932_ == 0)
{
v___x_926_ = v_s_903_;
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_nonlinearOccs_924_);
lean_inc(v_divMod_922_);
lean_inc(v_diseqSplits_921_);
lean_inc(v_conflict_x3f_920_);
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
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_928_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_916_, v_x_902_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 12, v___x_928_);
v___x_930_ = v___x_926_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_vars_904_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_varMap_905_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_varsHistory_906_);
lean_ctor_set(v_reuseFailAlloc_931_, 3, v_natToIntMap_907_);
lean_ctor_set(v_reuseFailAlloc_931_, 4, v_natDef_908_);
lean_ctor_set(v_reuseFailAlloc_931_, 5, v_dvds_909_);
lean_ctor_set(v_reuseFailAlloc_931_, 6, v_lowers_910_);
lean_ctor_set(v_reuseFailAlloc_931_, 7, v_uppers_911_);
lean_ctor_set(v_reuseFailAlloc_931_, 8, v_diseqs_912_);
lean_ctor_set(v_reuseFailAlloc_931_, 9, v_elimEqs_913_);
lean_ctor_set(v_reuseFailAlloc_931_, 10, v_elimStack_914_);
lean_ctor_set(v_reuseFailAlloc_931_, 11, v_occurs_915_);
lean_ctor_set(v_reuseFailAlloc_931_, 12, v___x_928_);
lean_ctor_set(v_reuseFailAlloc_931_, 13, v_nextCnstrId_917_);
lean_ctor_set(v_reuseFailAlloc_931_, 14, v_steps_919_);
lean_ctor_set(v_reuseFailAlloc_931_, 15, v_conflict_x3f_920_);
lean_ctor_set(v_reuseFailAlloc_931_, 16, v_diseqSplits_921_);
lean_ctor_set(v_reuseFailAlloc_931_, 17, v_divMod_922_);
lean_ctor_set(v_reuseFailAlloc_931_, 18, v_nonlinearOccs_924_);
lean_ctor_set_uint8(v_reuseFailAlloc_931_, sizeof(void*)*19, v_caseSplits_918_);
lean_ctor_set_uint8(v_reuseFailAlloc_931_, sizeof(void*)*19 + 1, v_usedCommRing_923_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_x_933_, lean_object* v_s_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(v_x_933_, v_s_934_);
lean_dec(v_x_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object* v_x_936_, lean_object* v_a_937_){
_start:
{
lean_object* v___f_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___f_939_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_939_, 0, v_x_936_);
v___x_940_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_941_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_940_, v___f_939_, v_a_937_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___boxed(lean_object* v_x_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_942_, v_a_943_);
lean_dec(v_a_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(lean_object* v_x_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_946_, v_a_947_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___boxed(lean_object* v_x_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(v_x_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec(v_a_960_);
return v_res_971_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__0));
v___x_974_ = l_Lean_stringToMessageData(v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_unsigned_to_nat(1u);
v___x_976_ = lean_nat_to_int(v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__3));
v___x_979_ = l_Lean_stringToMessageData(v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(lean_object* v_r_980_, lean_object* v_p_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
if (lean_obj_tag(v_p_981_) == 0)
{
lean_object* v_k_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1003_; 
v_k_985_ = lean_ctor_get(v_p_981_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_p_981_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_987_ = v_p_981_;
v_isShared_988_ = v_isSharedCheck_1003_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_k_985_);
lean_dec(v_p_981_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1003_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_989_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_990_ = lean_int_dec_eq(v_k_985_, v___x_989_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_991_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v_r_980_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l_Int_repr(v_k_985_);
lean_dec(v_k_985_);
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 3);
lean_ctor_set(v___x_987_, 0, v___x_993_);
v___x_995_ = v___x_987_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_999_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = l_Lean_MessageData_ofFormat(v___x_995_);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_992_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
}
else
{
lean_object* v___x_1001_; 
lean_dec(v_k_985_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v_r_980_);
v___x_1001_ = v___x_987_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_r_980_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
else
{
lean_object* v_k_1004_; lean_object* v_v_1005_; lean_object* v_p_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v_k_1004_ = lean_ctor_get(v_p_981_, 0);
lean_inc(v_k_1004_);
v_v_1005_ = lean_ctor_get(v_p_981_, 1);
lean_inc(v_v_1005_);
v_p_1006_ = lean_ctor_get(v_p_981_, 2);
lean_inc_ref(v_p_1006_);
lean_dec_ref_known(v_p_981_, 3);
v___x_1007_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_1008_ = lean_int_dec_eq(v_k_1004_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_1005_, v_a_982_, v_a_983_);
lean_dec(v_v_1005_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
v___x_1011_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v_r_980_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Int_repr(v_k_1004_);
lean_dec(v_k_1004_);
v___x_1014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
v___x_1015_ = l_Lean_MessageData_ofFormat(v___x_1014_);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1012_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_1010_);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v_r_980_ = v___x_1020_;
v_p_981_ = v_p_1006_;
goto _start;
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec_ref(v_p_1006_);
lean_dec(v_k_1004_);
lean_dec_ref(v_r_980_);
v_a_1022_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1009_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1009_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
else
{
lean_object* v___x_1030_; 
lean_dec(v_k_1004_);
v___x_1030_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_1005_, v_a_982_, v_a_983_);
lean_dec(v_v_1005_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1031_);
lean_dec_ref_known(v___x_1030_, 1);
v___x_1032_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_1033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1033_, 0, v_r_980_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_1031_);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v_r_980_ = v___x_1035_;
v_p_981_ = v_p_1006_;
goto _start;
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref(v_p_1006_);
lean_dec_ref(v_r_980_);
v_a_1037_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1030_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1030_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___boxed(lean_object* v_r_1045_, lean_object* v_p_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v_r_1045_, v_p_1046_, v_a_1047_, v_a_1048_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(lean_object* v_r_1051_, lean_object* v_p_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v_r_1051_, v_p_1052_, v_a_1053_, v_a_1061_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___boxed(lean_object* v_r_1065_, lean_object* v_p_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(v_r_1065_, v_p_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec(v_a_1067_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___redArg(lean_object* v_p_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
if (lean_obj_tag(v_p_1079_) == 0)
{
lean_object* v_k_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1093_; 
v_k_1083_ = lean_ctor_get(v_p_1079_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_p_1079_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1085_ = v_p_1079_;
v_isShared_1086_ = v_isSharedCheck_1093_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_k_1083_);
lean_dec(v_p_1079_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1093_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1087_ = l_Int_repr(v_k_1083_);
lean_dec(v_k_1083_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 3);
lean_ctor_set(v___x_1085_, 0, v___x_1087_);
v___x_1089_ = v___x_1085_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = l_Lean_MessageData_ofFormat(v___x_1089_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
}
else
{
lean_object* v_k_1094_; lean_object* v_v_1095_; lean_object* v_p_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; 
v_k_1094_ = lean_ctor_get(v_p_1079_, 0);
lean_inc(v_k_1094_);
v_v_1095_ = lean_ctor_get(v_p_1079_, 1);
lean_inc(v_v_1095_);
v_p_1096_ = lean_ctor_get(v_p_1079_, 2);
lean_inc_ref(v_p_1096_);
lean_dec_ref_known(v_p_1079_, 3);
v___x_1097_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_1098_ = lean_int_dec_eq(v_k_1094_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_1095_, v_a_1080_, v_a_1081_);
lean_dec(v_v_1095_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1099_, 1);
v___x_1101_ = l_Int_repr(v_k_1094_);
lean_dec(v_k_1094_);
v___x_1102_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
v___x_1103_ = l_Lean_MessageData_ofFormat(v___x_1102_);
v___x_1104_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4);
v___x_1105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_1100_);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v___x_1107_, v_p_1096_, v_a_1080_, v_a_1081_);
return v___x_1108_;
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec_ref(v_p_1096_);
lean_dec(v_k_1094_);
v_a_1109_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1099_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1099_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
else
{
lean_object* v___x_1117_; 
lean_dec(v_k_1094_);
v___x_1117_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_1095_, v_a_1080_, v_a_1081_);
lean_dec(v_v_1095_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v___x_1119_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_1118_);
v___x_1120_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v___x_1119_, v_p_1096_, v_a_1080_, v_a_1081_);
return v___x_1120_;
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec_ref(v_p_1096_);
v_a_1121_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1117_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1117_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___redArg___boxed(lean_object* v_p_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1129_, v_a_1130_, v_a_1131_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp(lean_object* v_p_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1134_, v_a_1135_, v_a_1143_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___boxed(lean_object* v_p_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Int_Internal_Linear_Poly_pp(v_p_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec(v_a_1148_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0(lean_object* v_a_1160_, lean_object* v___x_1161_, lean_object* v_x_1162_){
_start:
{
lean_object* v_size_1163_; uint8_t v___x_1164_; 
v_size_1163_ = lean_ctor_get(v_a_1160_, 2);
v___x_1164_ = lean_nat_dec_lt(v_x_1162_, v_size_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; 
v___x_1165_ = l_outOfBounds___redArg(v___x_1161_);
return v___x_1165_;
}
else
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1161_, v_a_1160_, v_x_1162_);
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed(lean_object* v_a_1167_, lean_object* v___x_1168_, lean_object* v_x_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0(v_a_1167_, v___x_1168_, v_x_1169_);
lean_dec(v_x_1169_);
lean_dec_ref(v___x_1168_);
lean_dec_ref(v_a_1167_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(lean_object* v_p_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = l_Lean_instInhabitedExpr;
v___x_1176_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_1172_, v_a_1173_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___f_1178_; lean_object* v___x_1179_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1176_, 1);
v___f_1178_ = lean_alloc_closure((void*)(l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1178_, 0, v_a_1177_);
lean_closure_set(v___f_1178_, 1, v___x_1175_);
v___x_1179_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_1178_, v_p_1171_);
return v___x_1179_;
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec_ref(v_p_1171_);
v_a_1180_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1176_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1176_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
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
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___boxed(lean_object* v_p_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1188_, v_a_1189_, v_a_1190_);
lean_dec_ref(v_a_1190_);
lean_dec(v_a_1189_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27(lean_object* v_p_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1193_, v_a_1194_, v_a_1202_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___boxed(lean_object* v_p_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Int_Internal_Linear_Poly_denoteExpr_x27(v_p_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
lean_dec(v_a_1208_);
lean_dec(v_a_1207_);
return v_res_1218_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object* v_c_1219_){
_start:
{
lean_object* v_p_1220_; 
v_p_1220_ = lean_ctor_get(v_c_1219_, 1);
if (lean_obj_tag(v_p_1220_) == 0)
{
lean_object* v_d_1221_; lean_object* v_k_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v_d_1221_ = lean_ctor_get(v_c_1219_, 0);
v_k_1222_ = lean_ctor_get(v_p_1220_, 0);
v___x_1223_ = lean_int_emod(v_k_1222_, v_d_1221_);
v___x_1224_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1225_ = lean_int_dec_eq(v___x_1223_, v___x_1224_);
lean_dec(v___x_1223_);
return v___x_1225_;
}
else
{
lean_object* v_d_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v_d_1226_ = lean_ctor_get(v_c_1219_, 0);
v___x_1227_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_1228_ = lean_int_dec_eq(v_d_1226_, v___x_1227_);
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial___boxed(lean_object* v_c_1229_){
_start:
{
uint8_t v_res_1230_; lean_object* v_r_1231_; 
v_res_1230_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_c_1229_);
lean_dec_ref(v_c_1229_);
v_r_1231_ = lean_box(v_res_1230_);
return v_r_1231_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0));
v___x_1234_ = l_Lean_stringToMessageData(v___x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object* v_c_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v_d_1239_; lean_object* v_p_1240_; lean_object* v___x_1241_; 
v_d_1239_ = lean_ctor_get(v_c_1235_, 0);
lean_inc(v_d_1239_);
v_p_1240_ = lean_ctor_get(v_c_1235_, 1);
lean_inc_ref(v_p_1240_);
lean_dec_ref(v_c_1235_);
v___x_1241_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1240_, v_a_1236_, v_a_1237_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1255_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1255_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1255_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1246_ = l_Int_repr(v_d_1239_);
lean_dec(v_d_1239_);
v___x_1247_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
v___x_1248_ = l_Lean_MessageData_ofFormat(v___x_1247_);
v___x_1249_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1);
v___x_1250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set(v___x_1251_, 1, v_a_1242_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1251_);
v___x_1253_ = v___x_1244_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
else
{
lean_dec(v_d_1239_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___boxed(lean_object* v_c_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1256_, v_a_1257_, v_a_1258_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(lean_object* v_c_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1261_, v_a_1262_, v_a_1270_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___boxed(lean_object* v_c_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(v_c_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec(v_a_1275_);
return v_res_1286_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = lean_unsigned_to_nat(0u);
v___x_1293_ = l_Lean_Level_ofNat(v___x_1292_);
return v___x_1293_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1294_ = lean_box(0);
v___x_1295_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3);
v___x_1296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
lean_ctor_set(v___x_1296_, 1, v___x_1294_);
return v___x_1296_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1297_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4);
v___x_1298_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2));
v___x_1299_ = l_Lean_Expr_const___override(v___x_1298_, v___x_1297_);
return v___x_1299_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = lean_box(0);
v___x_1304_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7));
v___x_1305_ = l_Lean_Expr_const___override(v___x_1304_, v___x_1303_);
return v___x_1305_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = lean_box(0);
v___x_1311_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10));
v___x_1312_ = l_Lean_Expr_const___override(v___x_1311_, v___x_1310_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(lean_object* v_c_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_d_1317_; lean_object* v_p_1318_; lean_object* v___x_1319_; 
v_d_1317_ = lean_ctor_get(v_c_1313_, 0);
lean_inc(v_d_1317_);
v_p_1318_ = lean_ctor_get(v_c_1313_, 1);
lean_inc_ref(v_p_1318_);
lean_dec_ref(v_c_1313_);
v___x_1319_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1318_, v_a_1314_, v_a_1315_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1341_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1322_ = v___x_1319_;
v_isShared_1323_ = v_isSharedCheck_1341_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1319_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1341_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___y_1325_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1331_ = lean_int_dec_le(v___x_1330_, v_d_1317_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1332_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5);
v___x_1333_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8);
v___x_1334_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11);
v___x_1335_ = lean_int_neg(v_d_1317_);
lean_dec(v_d_1317_);
v___x_1336_ = l_Int_toNat(v___x_1335_);
lean_dec(v___x_1335_);
v___x_1337_ = l_Lean_instToExprInt_mkNat(v___x_1336_);
v___x_1338_ = l_Lean_mkApp3(v___x_1332_, v___x_1333_, v___x_1334_, v___x_1337_);
v___y_1325_ = v___x_1338_;
goto v___jp_1324_;
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = l_Int_toNat(v_d_1317_);
lean_dec(v_d_1317_);
v___x_1340_ = l_Lean_instToExprInt_mkNat(v___x_1339_);
v___y_1325_ = v___x_1340_;
goto v___jp_1324_;
}
v___jp_1324_:
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1326_ = l_Lean_mkIntDvd(v___y_1325_, v_a_1320_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v___x_1326_);
v___x_1328_ = v___x_1322_;
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
lean_dec(v_d_1317_);
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1342_, v_a_1343_, v_a_1344_);
lean_dec_ref(v_a_1344_);
lean_dec(v_a_1343_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(lean_object* v_c_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1347_, v_a_1348_, v_a_1356_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___boxed(lean_object* v_c_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(v_c_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec(v_a_1361_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(lean_object* v_msgData_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; lean_object* v_env_1380_; uint8_t v___x_1381_; lean_object* v_env_1382_; lean_object* v___x_1383_; lean_object* v_toCold_1384_; lean_object* v_mctx_1385_; lean_object* v_lctx_1386_; lean_object* v_options_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1379_ = lean_st_ref_get(v___y_1377_);
v_env_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc_ref(v_env_1380_);
lean_dec(v___x_1379_);
v___x_1381_ = 0;
v_env_1382_ = l_Lean_Environment_setRecordingDeps(v_env_1380_, v___x_1381_);
v___x_1383_ = lean_st_ref_get(v___y_1375_);
v_toCold_1384_ = lean_ctor_get(v___y_1376_, 0);
v_mctx_1385_ = lean_ctor_get(v___x_1383_, 0);
lean_inc_ref(v_mctx_1385_);
lean_dec(v___x_1383_);
v_lctx_1386_ = lean_ctor_get(v___y_1374_, 2);
v_options_1387_ = lean_ctor_get(v_toCold_1384_, 2);
lean_inc_ref(v_options_1387_);
lean_inc_ref(v_lctx_1386_);
v___x_1388_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1388_, 0, v_env_1382_);
lean_ctor_set(v___x_1388_, 1, v_mctx_1385_);
lean_ctor_set(v___x_1388_, 2, v_lctx_1386_);
lean_ctor_set(v___x_1388_, 3, v_options_1387_);
v___x_1389_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
lean_ctor_set(v___x_1389_, 1, v_msgData_1373_);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object* v_msgData_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msgData_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(lean_object* v_msg_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_ref_1404_; lean_object* v___x_1405_; lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1414_; 
v_ref_1404_ = lean_ctor_get(v___y_1401_, 2);
v___x_1405_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msg_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1414_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1412_; 
lean_inc(v_ref_1404_);
v___x_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1410_, 0, v_ref_1404_);
lean_ctor_set(v___x_1410_, 1, v_a_1406_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set_tag(v___x_1408_, 1);
lean_ctor_set(v___x_1408_, 0, v___x_1410_);
v___x_1412_ = v___x_1408_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg___boxed(lean_object* v_msg_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
return v_res_1421_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0));
v___x_1424_ = l_Lean_stringToMessageData(v___x_1423_);
return v___x_1424_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2));
v___x_1427_ = l_Lean_stringToMessageData(v___x_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object* v_c_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1428_, v_a_1429_, v_a_1437_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
v___x_1442_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1443_ = l_Lean_indentD(v_a_1441_);
v___x_1444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1442_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3);
v___x_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1444_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1446_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
return v___x_1447_;
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
v_a_1448_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1440_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1440_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(lean_object* v_00_u03b1_1469_, lean_object* v_c_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1483_, lean_object* v_c_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(v_00_u03b1_1483_, v_c_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
lean_dec(v_a_1486_);
lean_dec(v_a_1485_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(lean_object* v_00_u03b1_1497_, lean_object* v_msg_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1498_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___boxed(lean_object* v_00_u03b1_1511_, lean_object* v_msg_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(v_00_u03b1_1511_, v_msg_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec(v___y_1513_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial_spec__0(lean_object* v_a_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_nat_to_int(v_a_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(lean_object* v_c_1527_){
_start:
{
lean_object* v_p_1528_; 
v_p_1528_ = lean_ctor_get(v_c_1527_, 0);
if (lean_obj_tag(v_p_1528_) == 0)
{
lean_object* v_k_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v_k_1529_ = lean_ctor_get(v_p_1528_, 0);
v___x_1530_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1531_ = lean_int_dec_eq(v_k_1529_, v___x_1530_);
if (v___x_1531_ == 0)
{
uint8_t v___x_1532_; 
v___x_1532_ = 1;
return v___x_1532_;
}
else
{
uint8_t v___x_1533_; 
v___x_1533_ = 0;
return v___x_1533_;
}
}
else
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1534_ = l_Int_Internal_Linear_Poly_getConst(v_p_1528_);
v___x_1535_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v_p_1528_);
v___x_1536_ = lean_nat_to_int(v___x_1535_);
v___x_1537_ = lean_int_emod(v___x_1534_, v___x_1536_);
lean_dec(v___x_1536_);
lean_dec(v___x_1534_);
v___x_1538_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1539_ = lean_int_dec_eq(v___x_1537_, v___x_1538_);
lean_dec(v___x_1537_);
if (v___x_1539_ == 0)
{
uint8_t v___x_1540_; 
v___x_1540_ = 1;
return v___x_1540_;
}
else
{
uint8_t v___x_1541_; 
v___x_1541_ = 0;
return v___x_1541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial___boxed(lean_object* v_c_1542_){
_start:
{
uint8_t v_res_1543_; lean_object* v_r_1544_; 
v_res_1543_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(v_c_1542_);
lean_dec_ref(v_c_1542_);
v_r_1544_ = lean_box(v_res_1543_);
return v_r_1544_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0));
v___x_1547_ = l_Lean_stringToMessageData(v___x_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(lean_object* v_c_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_p_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1569_; 
v_p_1552_ = lean_ctor_get(v_c_1548_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v_c_1548_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; 
v_unused_1570_ = lean_ctor_get(v_c_1548_, 1);
lean_dec(v_unused_1570_);
v___x_1554_ = v_c_1548_;
v_isShared_1555_ = v_isSharedCheck_1569_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_p_1552_);
lean_dec(v_c_1548_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1569_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1552_, v_a_1549_, v_a_1550_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1568_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1568_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1568_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1561_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1);
if (v_isShared_1555_ == 0)
{
lean_ctor_set_tag(v___x_1554_, 7);
lean_ctor_set(v___x_1554_, 1, v___x_1561_);
lean_ctor_set(v___x_1554_, 0, v_a_1557_);
v___x_1563_ = v___x_1554_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1557_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1565_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1563_);
v___x_1565_ = v___x_1559_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
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
else
{
lean_del_object(v___x_1554_);
return v___x_1556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___boxed(lean_object* v_c_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1571_, v_a_1572_, v_a_1573_);
lean_dec_ref(v_a_1573_);
lean_dec(v_a_1572_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(lean_object* v_c_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1576_, v_a_1577_, v_a_1585_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___boxed(lean_object* v_c_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(v_c_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
lean_dec(v_a_1595_);
lean_dec_ref(v_a_1594_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
lean_dec(v_a_1591_);
lean_dec(v_a_1590_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(lean_object* v_c_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1602_, v_a_1603_, v_a_1606_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
v___x_1611_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1612_ = l_Lean_indentD(v_a_1610_);
v___x_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1613_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_);
return v___x_1614_;
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
v_a_1615_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1609_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1609_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(lean_object* v_00_u03b1_1631_, lean_object* v_c_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1632_, v_a_1633_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1645_, lean_object* v_c_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(v_00_u03b1_1645_, v_c_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec(v_a_1647_);
return v_res_1658_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1660_ = l_Lean_mkIntLit(v___x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(lean_object* v_c_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v_p_1665_; lean_object* v___x_1666_; 
v_p_1665_ = lean_ctor_get(v_c_1661_, 0);
lean_inc_ref(v_p_1665_);
lean_dec_ref(v_c_1661_);
v___x_1666_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1665_, v_a_1662_, v_a_1663_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1677_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1677_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1677_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1671_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1672_ = l_Lean_mkIntEq(v_a_1667_, v___x_1671_);
v___x_1673_ = l_Lean_mkNot(v___x_1672_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v___x_1673_);
v___x_1675_ = v___x_1669_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
else
{
return v___x_1666_;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(lean_object* v_c_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1683_, v_a_1684_, v_a_1692_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___boxed(lean_object* v_c_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(v_c_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec(v_a_1698_);
lean_dec(v_a_1697_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert___boxed(lean_object* v_c_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_00___x40___internal___hyg_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = lean_grind_cutsat_assert_le(v_c_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
return v_res_1733_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(lean_object* v_c_1734_){
_start:
{
lean_object* v_p_1735_; 
v_p_1735_ = lean_ctor_get(v_c_1734_, 0);
if (lean_obj_tag(v_p_1735_) == 0)
{
lean_object* v_k_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v_k_1736_ = lean_ctor_get(v_p_1735_, 0);
v___x_1737_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1738_ = lean_int_dec_le(v_k_1736_, v___x_1737_);
return v___x_1738_;
}
else
{
uint8_t v___x_1739_; 
v___x_1739_ = 0;
return v___x_1739_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial___boxed(lean_object* v_c_1740_){
_start:
{
uint8_t v_res_1741_; lean_object* v_r_1742_; 
v_res_1741_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_c_1740_);
lean_dec_ref(v_c_1740_);
v_r_1742_ = lean_box(v_res_1741_);
return v_r_1742_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0));
v___x_1745_ = l_Lean_stringToMessageData(v___x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(lean_object* v_c_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_p_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1767_; 
v_p_1750_ = lean_ctor_get(v_c_1746_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_c_1746_);
if (v_isSharedCheck_1767_ == 0)
{
lean_object* v_unused_1768_; 
v_unused_1768_ = lean_ctor_get(v_c_1746_, 1);
lean_dec(v_unused_1768_);
v___x_1752_ = v_c_1746_;
v_isShared_1753_ = v_isSharedCheck_1767_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_p_1750_);
lean_dec(v_c_1746_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1767_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1750_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1766_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1766_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1766_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1759_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1);
if (v_isShared_1753_ == 0)
{
lean_ctor_set_tag(v___x_1752_, 7);
lean_ctor_set(v___x_1752_, 1, v___x_1759_);
lean_ctor_set(v___x_1752_, 0, v_a_1755_);
v___x_1761_ = v___x_1752_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1755_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1763_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v___x_1761_);
v___x_1763_ = v___x_1757_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
else
{
lean_del_object(v___x_1752_);
return v___x_1754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___boxed(lean_object* v_c_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1769_, v_a_1770_, v_a_1771_);
lean_dec_ref(v_a_1771_);
lean_dec(v_a_1770_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(lean_object* v_c_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1774_, v_a_1775_, v_a_1783_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___boxed(lean_object* v_c_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(v_c_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec(v_a_1788_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(lean_object* v_c_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_p_1804_; lean_object* v___x_1805_; 
v_p_1804_ = lean_ctor_get(v_c_1800_, 0);
lean_inc_ref(v_p_1804_);
lean_dec_ref(v_c_1800_);
v___x_1805_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1804_, v_a_1801_, v_a_1802_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1815_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1815_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1815_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1810_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1811_ = l_Lean_mkIntLE(v_a_1806_, v___x_1810_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1811_);
v___x_1813_ = v___x_1808_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
else
{
return v___x_1805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1816_, v_a_1817_, v_a_1818_);
lean_dec_ref(v_a_1818_);
lean_dec(v_a_1817_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(lean_object* v_c_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1821_, v_a_1822_, v_a_1830_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___boxed(lean_object* v_c_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(v_c_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec(v_a_1835_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(lean_object* v_c_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1847_, v_a_1848_, v_a_1851_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref_known(v___x_1854_, 1);
v___x_1856_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1857_ = l_Lean_indentD(v_a_1855_);
v___x_1858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1858_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_);
return v___x_1859_;
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
v_a_1860_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1854_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1854_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(lean_object* v_00_u03b1_1876_, lean_object* v_c_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1877_, v_a_1878_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1890_, lean_object* v_c_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(v_00_u03b1_1890_, v_c_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec(v_a_1892_);
return v_res_1903_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(lean_object* v_c_1904_){
_start:
{
lean_object* v_p_1905_; 
v_p_1905_ = lean_ctor_get(v_c_1904_, 0);
if (lean_obj_tag(v_p_1905_) == 0)
{
lean_object* v_k_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
v_k_1906_ = lean_ctor_get(v_p_1905_, 0);
v___x_1907_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1908_ = lean_int_dec_eq(v_k_1906_, v___x_1907_);
return v___x_1908_;
}
else
{
uint8_t v___x_1909_; 
v___x_1909_ = 0;
return v___x_1909_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial___boxed(lean_object* v_c_1910_){
_start:
{
uint8_t v_res_1911_; lean_object* v_r_1912_; 
v_res_1911_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(v_c_1910_);
lean_dec_ref(v_c_1910_);
v_r_1912_ = lean_box(v_res_1911_);
return v_r_1912_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0));
v___x_1915_ = l_Lean_stringToMessageData(v___x_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object* v_c_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v_p_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1937_; 
v_p_1920_ = lean_ctor_get(v_c_1916_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_c_1916_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v_c_1916_, 1);
lean_dec(v_unused_1938_);
v___x_1922_ = v_c_1916_;
v_isShared_1923_ = v_isSharedCheck_1937_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_p_1920_);
lean_dec(v_c_1916_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1937_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1920_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1936_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1936_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1936_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1929_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1);
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 7);
lean_ctor_set(v___x_1922_, 1, v___x_1929_);
lean_ctor_set(v___x_1922_, 0, v_a_1925_);
v___x_1931_ = v___x_1922_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1925_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1933_; 
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1931_);
v___x_1933_ = v___x_1927_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
else
{
lean_del_object(v___x_1922_);
return v___x_1924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___boxed(lean_object* v_c_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1939_, v_a_1940_, v_a_1941_);
lean_dec_ref(v_a_1941_);
lean_dec(v_a_1940_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(lean_object* v_c_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1944_, v_a_1945_, v_a_1953_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___boxed(lean_object* v_c_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(v_c_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
lean_dec(v_a_1959_);
lean_dec(v_a_1958_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(lean_object* v_c_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v_p_1974_; lean_object* v___x_1975_; 
v_p_1974_ = lean_ctor_get(v_c_1970_, 0);
lean_inc_ref(v_p_1974_);
lean_dec_ref(v_c_1970_);
v___x_1975_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1974_, v_a_1971_, v_a_1972_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1985_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_1985_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1985_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1980_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1981_ = l_Lean_mkIntEq(v_a_1976_, v___x_1980_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_1981_);
v___x_1983_ = v___x_1978_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
else
{
return v___x_1975_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1986_, v_a_1987_, v_a_1988_);
lean_dec_ref(v_a_1988_);
lean_dec(v_a_1987_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(lean_object* v_c_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1991_, v_a_1992_, v_a_2000_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___boxed(lean_object* v_c_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(v_c_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
lean_dec(v_a_2014_);
lean_dec_ref(v_a_2013_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec(v_a_2006_);
lean_dec(v_a_2005_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(lean_object* v_c_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_2017_, v_a_2018_, v_a_2021_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 1);
v___x_2026_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_2027_ = l_Lean_indentD(v_a_2025_);
v___x_2028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2026_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
v___x_2029_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2028_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
return v___x_2029_;
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
v_a_2030_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2024_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2024_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_);
lean_dec(v_a_2043_);
lean_dec_ref(v_a_2042_);
lean_dec(v_a_2041_);
lean_dec_ref(v_a_2040_);
lean_dec(v_a_2039_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(lean_object* v_00_u03b1_2046_, lean_object* v_c_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_2047_, v_a_2048_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_2060_, lean_object* v_c_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(v_00_u03b1_2060_, v_c_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec(v_a_2062_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(lean_object* v_x_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2075_, v_a_2076_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2095_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2095_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2095_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v_occurs_2083_; lean_object* v_size_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v_occurs_2083_ = lean_ctor_get(v_a_2079_, 11);
lean_inc_ref(v_occurs_2083_);
lean_dec(v_a_2079_);
v_size_2084_ = lean_ctor_get(v_occurs_2083_, 2);
v___x_2085_ = lean_box(1);
v___x_2086_ = lean_nat_dec_lt(v_x_2074_, v_size_2084_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
lean_dec_ref(v_occurs_2083_);
v___x_2087_ = l_outOfBounds___redArg(v___x_2085_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2087_);
v___x_2089_ = v___x_2081_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2091_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2085_, v_occurs_2083_, v_x_2074_);
lean_dec_ref(v_occurs_2083_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2091_);
v___x_2093_ = v___x_2081_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
v_a_2096_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2078_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2078_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg___boxed(lean_object* v_x_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2104_, v_a_2105_, v_a_2106_);
lean_dec_ref(v_a_2106_);
lean_dec(v_a_2105_);
lean_dec(v_x_2104_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(lean_object* v_x_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2109_, v_a_2110_, v_a_2118_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___boxed(lean_object* v_x_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(v_x_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
lean_dec(v_a_2128_);
lean_dec_ref(v_a_2127_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec(v_a_2123_);
lean_dec(v_x_2122_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(lean_object* v_k_2135_, lean_object* v_v_2136_, lean_object* v_t_2137_){
_start:
{
if (lean_obj_tag(v_t_2137_) == 0)
{
lean_object* v_size_2138_; lean_object* v_k_2139_; lean_object* v_v_2140_; lean_object* v_l_2141_; lean_object* v_r_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2423_; 
v_size_2138_ = lean_ctor_get(v_t_2137_, 0);
v_k_2139_ = lean_ctor_get(v_t_2137_, 1);
v_v_2140_ = lean_ctor_get(v_t_2137_, 2);
v_l_2141_ = lean_ctor_get(v_t_2137_, 3);
v_r_2142_ = lean_ctor_get(v_t_2137_, 4);
v_isSharedCheck_2423_ = !lean_is_exclusive(v_t_2137_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2144_ = v_t_2137_;
v_isShared_2145_ = v_isSharedCheck_2423_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_r_2142_);
lean_inc(v_l_2141_);
lean_inc(v_v_2140_);
lean_inc(v_k_2139_);
lean_inc(v_size_2138_);
lean_dec(v_t_2137_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2423_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
uint8_t v___x_2146_; 
v___x_2146_ = lean_nat_dec_lt(v_k_2135_, v_k_2139_);
if (v___x_2146_ == 0)
{
uint8_t v___x_2147_; 
v___x_2147_ = lean_nat_dec_eq(v_k_2135_, v_k_2139_);
if (v___x_2147_ == 0)
{
lean_object* v_impl_2148_; lean_object* v___x_2149_; 
lean_dec(v_size_2138_);
v_impl_2148_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2135_, v_v_2136_, v_r_2142_);
v___x_2149_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2141_) == 0)
{
lean_object* v_size_2150_; lean_object* v_size_2151_; lean_object* v_k_2152_; lean_object* v_v_2153_; lean_object* v_l_2154_; lean_object* v_r_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v_size_2150_ = lean_ctor_get(v_l_2141_, 0);
v_size_2151_ = lean_ctor_get(v_impl_2148_, 0);
v_k_2152_ = lean_ctor_get(v_impl_2148_, 1);
v_v_2153_ = lean_ctor_get(v_impl_2148_, 2);
v_l_2154_ = lean_ctor_get(v_impl_2148_, 3);
lean_inc(v_l_2154_);
v_r_2155_ = lean_ctor_get(v_impl_2148_, 4);
v___x_2156_ = lean_unsigned_to_nat(3u);
v___x_2157_ = lean_nat_mul(v___x_2156_, v_size_2150_);
v___x_2158_ = lean_nat_dec_lt(v___x_2157_, v_size_2151_);
lean_dec(v___x_2157_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
lean_dec(v_l_2154_);
v___x_2159_ = lean_nat_add(v___x_2149_, v_size_2150_);
v___x_2160_ = lean_nat_add(v___x_2159_, v_size_2151_);
lean_dec(v___x_2159_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 4, v_impl_2148_);
lean_ctor_set(v___x_2144_, 0, v___x_2160_);
v___x_2162_ = v___x_2144_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2163_, 3, v_l_2141_);
lean_ctor_set(v_reuseFailAlloc_2163_, 4, v_impl_2148_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
else
{
lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2227_; 
lean_inc(v_r_2155_);
lean_inc(v_v_2153_);
lean_inc(v_k_2152_);
lean_inc(v_size_2151_);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_impl_2148_);
if (v_isSharedCheck_2227_ == 0)
{
lean_object* v_unused_2228_; lean_object* v_unused_2229_; lean_object* v_unused_2230_; lean_object* v_unused_2231_; lean_object* v_unused_2232_; 
v_unused_2228_ = lean_ctor_get(v_impl_2148_, 4);
lean_dec(v_unused_2228_);
v_unused_2229_ = lean_ctor_get(v_impl_2148_, 3);
lean_dec(v_unused_2229_);
v_unused_2230_ = lean_ctor_get(v_impl_2148_, 2);
lean_dec(v_unused_2230_);
v_unused_2231_ = lean_ctor_get(v_impl_2148_, 1);
lean_dec(v_unused_2231_);
v_unused_2232_ = lean_ctor_get(v_impl_2148_, 0);
lean_dec(v_unused_2232_);
v___x_2165_ = v_impl_2148_;
v_isShared_2166_ = v_isSharedCheck_2227_;
goto v_resetjp_2164_;
}
else
{
lean_dec(v_impl_2148_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2227_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v_size_2167_; lean_object* v_k_2168_; lean_object* v_v_2169_; lean_object* v_l_2170_; lean_object* v_r_2171_; lean_object* v_size_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v_size_2167_ = lean_ctor_get(v_l_2154_, 0);
v_k_2168_ = lean_ctor_get(v_l_2154_, 1);
v_v_2169_ = lean_ctor_get(v_l_2154_, 2);
v_l_2170_ = lean_ctor_get(v_l_2154_, 3);
v_r_2171_ = lean_ctor_get(v_l_2154_, 4);
v_size_2172_ = lean_ctor_get(v_r_2155_, 0);
v___x_2173_ = lean_unsigned_to_nat(2u);
v___x_2174_ = lean_nat_mul(v___x_2173_, v_size_2172_);
v___x_2175_ = lean_nat_dec_lt(v_size_2167_, v___x_2174_);
lean_dec(v___x_2174_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2203_; 
lean_inc(v_r_2171_);
lean_inc(v_l_2170_);
lean_inc(v_v_2169_);
lean_inc(v_k_2168_);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_l_2154_);
if (v_isSharedCheck_2203_ == 0)
{
lean_object* v_unused_2204_; lean_object* v_unused_2205_; lean_object* v_unused_2206_; lean_object* v_unused_2207_; lean_object* v_unused_2208_; 
v_unused_2204_ = lean_ctor_get(v_l_2154_, 4);
lean_dec(v_unused_2204_);
v_unused_2205_ = lean_ctor_get(v_l_2154_, 3);
lean_dec(v_unused_2205_);
v_unused_2206_ = lean_ctor_get(v_l_2154_, 2);
lean_dec(v_unused_2206_);
v_unused_2207_ = lean_ctor_get(v_l_2154_, 1);
lean_dec(v_unused_2207_);
v_unused_2208_ = lean_ctor_get(v_l_2154_, 0);
lean_dec(v_unused_2208_);
v___x_2177_ = v_l_2154_;
v_isShared_2178_ = v_isSharedCheck_2203_;
goto v_resetjp_2176_;
}
else
{
lean_dec(v_l_2154_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2203_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2193_; 
v___x_2179_ = lean_nat_add(v___x_2149_, v_size_2150_);
v___x_2180_ = lean_nat_add(v___x_2179_, v_size_2151_);
lean_dec(v_size_2151_);
if (lean_obj_tag(v_l_2170_) == 0)
{
lean_object* v_size_2201_; 
v_size_2201_ = lean_ctor_get(v_l_2170_, 0);
lean_inc(v_size_2201_);
v___y_2193_ = v_size_2201_;
goto v___jp_2192_;
}
else
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_unsigned_to_nat(0u);
v___y_2193_ = v___x_2202_;
goto v___jp_2192_;
}
v___jp_2181_:
{
lean_object* v___x_2185_; lean_object* v___x_2187_; 
v___x_2185_ = lean_nat_add(v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec(v___y_2183_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 4, v_r_2155_);
lean_ctor_set(v___x_2177_, 3, v_r_2171_);
lean_ctor_set(v___x_2177_, 2, v_v_2153_);
lean_ctor_set(v___x_2177_, 1, v_k_2152_);
lean_ctor_set(v___x_2177_, 0, v___x_2185_);
v___x_2187_ = v___x_2177_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2185_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_k_2152_);
lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_v_2153_);
lean_ctor_set(v_reuseFailAlloc_2191_, 3, v_r_2171_);
lean_ctor_set(v_reuseFailAlloc_2191_, 4, v_r_2155_);
v___x_2187_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2189_; 
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 4, v___x_2187_);
lean_ctor_set(v___x_2165_, 3, v___y_2182_);
lean_ctor_set(v___x_2165_, 2, v_v_2169_);
lean_ctor_set(v___x_2165_, 1, v_k_2168_);
lean_ctor_set(v___x_2165_, 0, v___x_2180_);
v___x_2189_ = v___x_2165_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_k_2168_);
lean_ctor_set(v_reuseFailAlloc_2190_, 2, v_v_2169_);
lean_ctor_set(v_reuseFailAlloc_2190_, 3, v___y_2182_);
lean_ctor_set(v_reuseFailAlloc_2190_, 4, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
v___jp_2192_:
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = lean_nat_add(v___x_2179_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec(v___x_2179_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 4, v_l_2170_);
lean_ctor_set(v___x_2144_, 0, v___x_2194_);
v___x_2196_ = v___x_2144_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2200_, 3, v_l_2141_);
lean_ctor_set(v_reuseFailAlloc_2200_, 4, v_l_2170_);
v___x_2196_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2197_; 
v___x_2197_ = lean_nat_add(v___x_2149_, v_size_2172_);
if (lean_obj_tag(v_r_2171_) == 0)
{
lean_object* v_size_2198_; 
v_size_2198_ = lean_ctor_get(v_r_2171_, 0);
lean_inc(v_size_2198_);
v___y_2182_ = v___x_2196_;
v___y_2183_ = v___x_2197_;
v___y_2184_ = v_size_2198_;
goto v___jp_2181_;
}
else
{
lean_object* v___x_2199_; 
v___x_2199_ = lean_unsigned_to_nat(0u);
v___y_2182_ = v___x_2196_;
v___y_2183_ = v___x_2197_;
v___y_2184_ = v___x_2199_;
goto v___jp_2181_;
}
}
}
}
}
else
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
lean_del_object(v___x_2144_);
v___x_2209_ = lean_nat_add(v___x_2149_, v_size_2150_);
v___x_2210_ = lean_nat_add(v___x_2209_, v_size_2151_);
lean_dec(v_size_2151_);
v___x_2211_ = lean_nat_add(v___x_2209_, v_size_2167_);
lean_dec(v___x_2209_);
lean_inc_ref(v_l_2141_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 4, v_l_2154_);
lean_ctor_set(v___x_2165_, 3, v_l_2141_);
lean_ctor_set(v___x_2165_, 2, v_v_2140_);
lean_ctor_set(v___x_2165_, 1, v_k_2139_);
lean_ctor_set(v___x_2165_, 0, v___x_2211_);
v___x_2213_ = v___x_2165_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_l_2141_);
lean_ctor_set(v_reuseFailAlloc_2226_, 4, v_l_2154_);
v___x_2213_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
v_isSharedCheck_2220_ = !lean_is_exclusive(v_l_2141_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; lean_object* v_unused_2222_; lean_object* v_unused_2223_; lean_object* v_unused_2224_; lean_object* v_unused_2225_; 
v_unused_2221_ = lean_ctor_get(v_l_2141_, 4);
lean_dec(v_unused_2221_);
v_unused_2222_ = lean_ctor_get(v_l_2141_, 3);
lean_dec(v_unused_2222_);
v_unused_2223_ = lean_ctor_get(v_l_2141_, 2);
lean_dec(v_unused_2223_);
v_unused_2224_ = lean_ctor_get(v_l_2141_, 1);
lean_dec(v_unused_2224_);
v_unused_2225_ = lean_ctor_get(v_l_2141_, 0);
lean_dec(v_unused_2225_);
v___x_2215_ = v_l_2141_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_dec(v_l_2141_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 4, v_r_2155_);
lean_ctor_set(v___x_2215_, 3, v___x_2213_);
lean_ctor_set(v___x_2215_, 2, v_v_2153_);
lean_ctor_set(v___x_2215_, 1, v_k_2152_);
lean_ctor_set(v___x_2215_, 0, v___x_2210_);
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2210_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_k_2152_);
lean_ctor_set(v_reuseFailAlloc_2219_, 2, v_v_2153_);
lean_ctor_set(v_reuseFailAlloc_2219_, 3, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2219_, 4, v_r_2155_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2233_; 
v_l_2233_ = lean_ctor_get(v_impl_2148_, 3);
lean_inc(v_l_2233_);
if (lean_obj_tag(v_l_2233_) == 0)
{
lean_object* v_r_2234_; lean_object* v_k_2235_; lean_object* v_v_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2259_; 
v_r_2234_ = lean_ctor_get(v_impl_2148_, 4);
v_k_2235_ = lean_ctor_get(v_impl_2148_, 1);
v_v_2236_ = lean_ctor_get(v_impl_2148_, 2);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_impl_2148_);
if (v_isSharedCheck_2259_ == 0)
{
lean_object* v_unused_2260_; lean_object* v_unused_2261_; 
v_unused_2260_ = lean_ctor_get(v_impl_2148_, 3);
lean_dec(v_unused_2260_);
v_unused_2261_ = lean_ctor_get(v_impl_2148_, 0);
lean_dec(v_unused_2261_);
v___x_2238_ = v_impl_2148_;
v_isShared_2239_ = v_isSharedCheck_2259_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_r_2234_);
lean_inc(v_v_2236_);
lean_inc(v_k_2235_);
lean_dec(v_impl_2148_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2259_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v_k_2240_; lean_object* v_v_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2255_; 
v_k_2240_ = lean_ctor_get(v_l_2233_, 1);
v_v_2241_ = lean_ctor_get(v_l_2233_, 2);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_l_2233_);
if (v_isSharedCheck_2255_ == 0)
{
lean_object* v_unused_2256_; lean_object* v_unused_2257_; lean_object* v_unused_2258_; 
v_unused_2256_ = lean_ctor_get(v_l_2233_, 4);
lean_dec(v_unused_2256_);
v_unused_2257_ = lean_ctor_get(v_l_2233_, 3);
lean_dec(v_unused_2257_);
v_unused_2258_ = lean_ctor_get(v_l_2233_, 0);
lean_dec(v_unused_2258_);
v___x_2243_ = v_l_2233_;
v_isShared_2244_ = v_isSharedCheck_2255_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_v_2241_);
lean_inc(v_k_2240_);
lean_dec(v_l_2233_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2255_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2245_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2234_, 2);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 4, v_r_2234_);
lean_ctor_set(v___x_2243_, 3, v_r_2234_);
lean_ctor_set(v___x_2243_, 2, v_v_2140_);
lean_ctor_set(v___x_2243_, 1, v_k_2139_);
lean_ctor_set(v___x_2243_, 0, v___x_2149_);
v___x_2247_ = v___x_2243_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2254_, 3, v_r_2234_);
lean_ctor_set(v_reuseFailAlloc_2254_, 4, v_r_2234_);
v___x_2247_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
lean_object* v___x_2249_; 
lean_inc(v_r_2234_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 3, v_r_2234_);
lean_ctor_set(v___x_2238_, 0, v___x_2149_);
v___x_2249_ = v___x_2238_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_k_2235_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v_v_2236_);
lean_ctor_set(v_reuseFailAlloc_2253_, 3, v_r_2234_);
lean_ctor_set(v_reuseFailAlloc_2253_, 4, v_r_2234_);
v___x_2249_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2251_; 
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 4, v___x_2249_);
lean_ctor_set(v___x_2144_, 3, v___x_2247_);
lean_ctor_set(v___x_2144_, 2, v_v_2241_);
lean_ctor_set(v___x_2144_, 1, v_k_2240_);
lean_ctor_set(v___x_2144_, 0, v___x_2245_);
v___x_2251_ = v___x_2144_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2245_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_k_2240_);
lean_ctor_set(v_reuseFailAlloc_2252_, 2, v_v_2241_);
lean_ctor_set(v_reuseFailAlloc_2252_, 3, v___x_2247_);
lean_ctor_set(v_reuseFailAlloc_2252_, 4, v___x_2249_);
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
}
}
else
{
lean_object* v_r_2262_; 
v_r_2262_ = lean_ctor_get(v_impl_2148_, 4);
lean_inc(v_r_2262_);
if (lean_obj_tag(v_r_2262_) == 0)
{
lean_object* v_k_2263_; lean_object* v_v_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2275_; 
v_k_2263_ = lean_ctor_get(v_impl_2148_, 1);
v_v_2264_ = lean_ctor_get(v_impl_2148_, 2);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_impl_2148_);
if (v_isSharedCheck_2275_ == 0)
{
lean_object* v_unused_2276_; lean_object* v_unused_2277_; lean_object* v_unused_2278_; 
v_unused_2276_ = lean_ctor_get(v_impl_2148_, 4);
lean_dec(v_unused_2276_);
v_unused_2277_ = lean_ctor_get(v_impl_2148_, 3);
lean_dec(v_unused_2277_);
v_unused_2278_ = lean_ctor_get(v_impl_2148_, 0);
lean_dec(v_unused_2278_);
v___x_2266_ = v_impl_2148_;
v_isShared_2267_ = v_isSharedCheck_2275_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_v_2264_);
lean_inc(v_k_2263_);
lean_dec(v_impl_2148_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2275_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2268_; lean_object* v___x_2270_; 
v___x_2268_ = lean_unsigned_to_nat(3u);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 4, v_l_2233_);
lean_ctor_set(v___x_2266_, 2, v_v_2140_);
lean_ctor_set(v___x_2266_, 1, v_k_2139_);
lean_ctor_set(v___x_2266_, 0, v___x_2149_);
v___x_2270_ = v___x_2266_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2274_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2274_, 3, v_l_2233_);
lean_ctor_set(v_reuseFailAlloc_2274_, 4, v_l_2233_);
v___x_2270_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2272_; 
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 4, v_r_2262_);
lean_ctor_set(v___x_2144_, 3, v___x_2270_);
lean_ctor_set(v___x_2144_, 2, v_v_2264_);
lean_ctor_set(v___x_2144_, 1, v_k_2263_);
lean_ctor_set(v___x_2144_, 0, v___x_2268_);
v___x_2272_ = v___x_2144_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2268_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_k_2263_);
lean_ctor_set(v_reuseFailAlloc_2273_, 2, v_v_2264_);
lean_ctor_set(v_reuseFailAlloc_2273_, 3, v___x_2270_);
lean_ctor_set(v_reuseFailAlloc_2273_, 4, v_r_2262_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2281_; 
v___x_2279_ = lean_unsigned_to_nat(2u);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 4, v_impl_2148_);
lean_ctor_set(v___x_2144_, 3, v_r_2262_);
lean_ctor_set(v___x_2144_, 0, v___x_2279_);
v___x_2281_ = v___x_2144_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2282_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2282_, 3, v_r_2262_);
lean_ctor_set(v_reuseFailAlloc_2282_, 4, v_impl_2148_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
else
{
lean_object* v___x_2284_; 
lean_dec(v_v_2140_);
lean_dec(v_k_2139_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 2, v_v_2136_);
lean_ctor_set(v___x_2144_, 1, v_k_2135_);
v___x_2284_ = v___x_2144_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_size_2138_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v_k_2135_);
lean_ctor_set(v_reuseFailAlloc_2285_, 2, v_v_2136_);
lean_ctor_set(v_reuseFailAlloc_2285_, 3, v_l_2141_);
lean_ctor_set(v_reuseFailAlloc_2285_, 4, v_r_2142_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
else
{
lean_object* v_impl_2286_; lean_object* v___x_2287_; 
lean_dec(v_size_2138_);
v_impl_2286_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2135_, v_v_2136_, v_l_2141_);
v___x_2287_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2142_) == 0)
{
lean_object* v_size_2288_; lean_object* v_size_2289_; lean_object* v_k_2290_; lean_object* v_v_2291_; lean_object* v_l_2292_; lean_object* v_r_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; 
v_size_2288_ = lean_ctor_get(v_r_2142_, 0);
v_size_2289_ = lean_ctor_get(v_impl_2286_, 0);
v_k_2290_ = lean_ctor_get(v_impl_2286_, 1);
v_v_2291_ = lean_ctor_get(v_impl_2286_, 2);
v_l_2292_ = lean_ctor_get(v_impl_2286_, 3);
v_r_2293_ = lean_ctor_get(v_impl_2286_, 4);
lean_inc(v_r_2293_);
v___x_2294_ = lean_unsigned_to_nat(3u);
v___x_2295_ = lean_nat_mul(v___x_2294_, v_size_2288_);
v___x_2296_ = lean_nat_dec_lt(v___x_2295_, v_size_2289_);
lean_dec(v___x_2295_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2300_; 
lean_dec(v_r_2293_);
v___x_2297_ = lean_nat_add(v___x_2287_, v_size_2289_);
v___x_2298_ = lean_nat_add(v___x_2297_, v_size_2288_);
lean_dec(v___x_2297_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 3, v_impl_2286_);
lean_ctor_set(v___x_2144_, 0, v___x_2298_);
v___x_2300_ = v___x_2144_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2301_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2301_, 3, v_impl_2286_);
lean_ctor_set(v_reuseFailAlloc_2301_, 4, v_r_2142_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
else
{
lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2367_; 
lean_inc(v_l_2292_);
lean_inc(v_v_2291_);
lean_inc(v_k_2290_);
lean_inc(v_size_2289_);
v_isSharedCheck_2367_ = !lean_is_exclusive(v_impl_2286_);
if (v_isSharedCheck_2367_ == 0)
{
lean_object* v_unused_2368_; lean_object* v_unused_2369_; lean_object* v_unused_2370_; lean_object* v_unused_2371_; lean_object* v_unused_2372_; 
v_unused_2368_ = lean_ctor_get(v_impl_2286_, 4);
lean_dec(v_unused_2368_);
v_unused_2369_ = lean_ctor_get(v_impl_2286_, 3);
lean_dec(v_unused_2369_);
v_unused_2370_ = lean_ctor_get(v_impl_2286_, 2);
lean_dec(v_unused_2370_);
v_unused_2371_ = lean_ctor_get(v_impl_2286_, 1);
lean_dec(v_unused_2371_);
v_unused_2372_ = lean_ctor_get(v_impl_2286_, 0);
lean_dec(v_unused_2372_);
v___x_2303_ = v_impl_2286_;
v_isShared_2304_ = v_isSharedCheck_2367_;
goto v_resetjp_2302_;
}
else
{
lean_dec(v_impl_2286_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2367_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v_size_2305_; lean_object* v_size_2306_; lean_object* v_k_2307_; lean_object* v_v_2308_; lean_object* v_l_2309_; lean_object* v_r_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; 
v_size_2305_ = lean_ctor_get(v_l_2292_, 0);
v_size_2306_ = lean_ctor_get(v_r_2293_, 0);
v_k_2307_ = lean_ctor_get(v_r_2293_, 1);
v_v_2308_ = lean_ctor_get(v_r_2293_, 2);
v_l_2309_ = lean_ctor_get(v_r_2293_, 3);
v_r_2310_ = lean_ctor_get(v_r_2293_, 4);
v___x_2311_ = lean_unsigned_to_nat(2u);
v___x_2312_ = lean_nat_mul(v___x_2311_, v_size_2305_);
v___x_2313_ = lean_nat_dec_lt(v_size_2306_, v___x_2312_);
lean_dec(v___x_2312_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2342_; 
lean_inc(v_r_2310_);
lean_inc(v_l_2309_);
lean_inc(v_v_2308_);
lean_inc(v_k_2307_);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_r_2293_);
if (v_isSharedCheck_2342_ == 0)
{
lean_object* v_unused_2343_; lean_object* v_unused_2344_; lean_object* v_unused_2345_; lean_object* v_unused_2346_; lean_object* v_unused_2347_; 
v_unused_2343_ = lean_ctor_get(v_r_2293_, 4);
lean_dec(v_unused_2343_);
v_unused_2344_ = lean_ctor_get(v_r_2293_, 3);
lean_dec(v_unused_2344_);
v_unused_2345_ = lean_ctor_get(v_r_2293_, 2);
lean_dec(v_unused_2345_);
v_unused_2346_ = lean_ctor_get(v_r_2293_, 1);
lean_dec(v_unused_2346_);
v_unused_2347_ = lean_ctor_get(v_r_2293_, 0);
lean_dec(v_unused_2347_);
v___x_2315_ = v_r_2293_;
v_isShared_2316_ = v_isSharedCheck_2342_;
goto v_resetjp_2314_;
}
else
{
lean_dec(v_r_2293_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2342_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___x_2330_; lean_object* v___y_2332_; 
v___x_2317_ = lean_nat_add(v___x_2287_, v_size_2289_);
lean_dec(v_size_2289_);
v___x_2318_ = lean_nat_add(v___x_2317_, v_size_2288_);
lean_dec(v___x_2317_);
v___x_2330_ = lean_nat_add(v___x_2287_, v_size_2305_);
if (lean_obj_tag(v_l_2309_) == 0)
{
lean_object* v_size_2340_; 
v_size_2340_ = lean_ctor_get(v_l_2309_, 0);
lean_inc(v_size_2340_);
v___y_2332_ = v_size_2340_;
goto v___jp_2331_;
}
else
{
lean_object* v___x_2341_; 
v___x_2341_ = lean_unsigned_to_nat(0u);
v___y_2332_ = v___x_2341_;
goto v___jp_2331_;
}
v___jp_2319_:
{
lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2323_ = lean_nat_add(v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec(v___y_2321_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 4, v_r_2142_);
lean_ctor_set(v___x_2315_, 3, v_r_2310_);
lean_ctor_set(v___x_2315_, 2, v_v_2140_);
lean_ctor_set(v___x_2315_, 1, v_k_2139_);
lean_ctor_set(v___x_2315_, 0, v___x_2323_);
v___x_2325_ = v___x_2315_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2323_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2329_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2329_, 3, v_r_2310_);
lean_ctor_set(v_reuseFailAlloc_2329_, 4, v_r_2142_);
v___x_2325_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2327_; 
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 4, v___x_2325_);
lean_ctor_set(v___x_2303_, 3, v___y_2320_);
lean_ctor_set(v___x_2303_, 2, v_v_2308_);
lean_ctor_set(v___x_2303_, 1, v_k_2307_);
lean_ctor_set(v___x_2303_, 0, v___x_2318_);
v___x_2327_ = v___x_2303_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_k_2307_);
lean_ctor_set(v_reuseFailAlloc_2328_, 2, v_v_2308_);
lean_ctor_set(v_reuseFailAlloc_2328_, 3, v___y_2320_);
lean_ctor_set(v_reuseFailAlloc_2328_, 4, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
v___jp_2331_:
{
lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2333_ = lean_nat_add(v___x_2330_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec(v___x_2330_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 4, v_l_2309_);
lean_ctor_set(v___x_2144_, 3, v_l_2292_);
lean_ctor_set(v___x_2144_, 2, v_v_2291_);
lean_ctor_set(v___x_2144_, 1, v_k_2290_);
lean_ctor_set(v___x_2144_, 0, v___x_2333_);
v___x_2335_ = v___x_2144_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2333_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_k_2290_);
lean_ctor_set(v_reuseFailAlloc_2339_, 2, v_v_2291_);
lean_ctor_set(v_reuseFailAlloc_2339_, 3, v_l_2292_);
lean_ctor_set(v_reuseFailAlloc_2339_, 4, v_l_2309_);
v___x_2335_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2336_; 
v___x_2336_ = lean_nat_add(v___x_2287_, v_size_2288_);
if (lean_obj_tag(v_r_2310_) == 0)
{
lean_object* v_size_2337_; 
v_size_2337_ = lean_ctor_get(v_r_2310_, 0);
lean_inc(v_size_2337_);
v___y_2320_ = v___x_2335_;
v___y_2321_ = v___x_2336_;
v___y_2322_ = v_size_2337_;
goto v___jp_2319_;
}
else
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_unsigned_to_nat(0u);
v___y_2320_ = v___x_2335_;
v___y_2321_ = v___x_2336_;
v___y_2322_ = v___x_2338_;
goto v___jp_2319_;
}
}
}
}
}
else
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2353_; 
lean_del_object(v___x_2144_);
v___x_2348_ = lean_nat_add(v___x_2287_, v_size_2289_);
lean_dec(v_size_2289_);
v___x_2349_ = lean_nat_add(v___x_2348_, v_size_2288_);
lean_dec(v___x_2348_);
v___x_2350_ = lean_nat_add(v___x_2287_, v_size_2288_);
v___x_2351_ = lean_nat_add(v___x_2350_, v_size_2306_);
lean_dec(v___x_2350_);
lean_inc_ref(v_r_2142_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 4, v_r_2142_);
lean_ctor_set(v___x_2303_, 3, v_r_2293_);
lean_ctor_set(v___x_2303_, 2, v_v_2140_);
lean_ctor_set(v___x_2303_, 1, v_k_2139_);
lean_ctor_set(v___x_2303_, 0, v___x_2351_);
v___x_2353_ = v___x_2303_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2351_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2366_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2366_, 3, v_r_2293_);
lean_ctor_set(v_reuseFailAlloc_2366_, 4, v_r_2142_);
v___x_2353_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
v_isSharedCheck_2360_ = !lean_is_exclusive(v_r_2142_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; lean_object* v_unused_2362_; lean_object* v_unused_2363_; lean_object* v_unused_2364_; lean_object* v_unused_2365_; 
v_unused_2361_ = lean_ctor_get(v_r_2142_, 4);
lean_dec(v_unused_2361_);
v_unused_2362_ = lean_ctor_get(v_r_2142_, 3);
lean_dec(v_unused_2362_);
v_unused_2363_ = lean_ctor_get(v_r_2142_, 2);
lean_dec(v_unused_2363_);
v_unused_2364_ = lean_ctor_get(v_r_2142_, 1);
lean_dec(v_unused_2364_);
v_unused_2365_ = lean_ctor_get(v_r_2142_, 0);
lean_dec(v_unused_2365_);
v___x_2355_ = v_r_2142_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_dec(v_r_2142_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 4, v___x_2353_);
lean_ctor_set(v___x_2355_, 3, v_l_2292_);
lean_ctor_set(v___x_2355_, 2, v_v_2291_);
lean_ctor_set(v___x_2355_, 1, v_k_2290_);
lean_ctor_set(v___x_2355_, 0, v___x_2349_);
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_k_2290_);
lean_ctor_set(v_reuseFailAlloc_2359_, 2, v_v_2291_);
lean_ctor_set(v_reuseFailAlloc_2359_, 3, v_l_2292_);
lean_ctor_set(v_reuseFailAlloc_2359_, 4, v___x_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2373_; 
v_l_2373_ = lean_ctor_get(v_impl_2286_, 3);
if (lean_obj_tag(v_l_2373_) == 0)
{
lean_object* v_r_2374_; lean_object* v_k_2375_; lean_object* v_v_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2387_; 
lean_inc_ref(v_l_2373_);
v_r_2374_ = lean_ctor_get(v_impl_2286_, 4);
v_k_2375_ = lean_ctor_get(v_impl_2286_, 1);
v_v_2376_ = lean_ctor_get(v_impl_2286_, 2);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_impl_2286_);
if (v_isSharedCheck_2387_ == 0)
{
lean_object* v_unused_2388_; lean_object* v_unused_2389_; 
v_unused_2388_ = lean_ctor_get(v_impl_2286_, 3);
lean_dec(v_unused_2388_);
v_unused_2389_ = lean_ctor_get(v_impl_2286_, 0);
lean_dec(v_unused_2389_);
v___x_2378_ = v_impl_2286_;
v_isShared_2379_ = v_isSharedCheck_2387_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_r_2374_);
lean_inc(v_v_2376_);
lean_inc(v_k_2375_);
lean_dec(v_impl_2286_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2387_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2380_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2374_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 3, v_r_2374_);
lean_ctor_set(v___x_2378_, 2, v_v_2140_);
lean_ctor_set(v___x_2378_, 1, v_k_2139_);
lean_ctor_set(v___x_2378_, 0, v___x_2287_);
v___x_2382_ = v___x_2378_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2386_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2386_, 3, v_r_2374_);
lean_ctor_set(v_reuseFailAlloc_2386_, 4, v_r_2374_);
v___x_2382_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2384_; 
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 4, v___x_2382_);
lean_ctor_set(v___x_2144_, 3, v_l_2373_);
lean_ctor_set(v___x_2144_, 2, v_v_2376_);
lean_ctor_set(v___x_2144_, 1, v_k_2375_);
lean_ctor_set(v___x_2144_, 0, v___x_2380_);
v___x_2384_ = v___x_2144_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_k_2375_);
lean_ctor_set(v_reuseFailAlloc_2385_, 2, v_v_2376_);
lean_ctor_set(v_reuseFailAlloc_2385_, 3, v_l_2373_);
lean_ctor_set(v_reuseFailAlloc_2385_, 4, v___x_2382_);
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
else
{
lean_object* v_r_2390_; 
v_r_2390_ = lean_ctor_get(v_impl_2286_, 4);
lean_inc(v_r_2390_);
if (lean_obj_tag(v_r_2390_) == 0)
{
lean_object* v_k_2391_; lean_object* v_v_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2415_; 
lean_inc(v_l_2373_);
v_k_2391_ = lean_ctor_get(v_impl_2286_, 1);
v_v_2392_ = lean_ctor_get(v_impl_2286_, 2);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_impl_2286_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; lean_object* v_unused_2417_; lean_object* v_unused_2418_; 
v_unused_2416_ = lean_ctor_get(v_impl_2286_, 4);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v_impl_2286_, 3);
lean_dec(v_unused_2417_);
v_unused_2418_ = lean_ctor_get(v_impl_2286_, 0);
lean_dec(v_unused_2418_);
v___x_2394_ = v_impl_2286_;
v_isShared_2395_ = v_isSharedCheck_2415_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_v_2392_);
lean_inc(v_k_2391_);
lean_dec(v_impl_2286_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2415_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v_k_2396_; lean_object* v_v_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2411_; 
v_k_2396_ = lean_ctor_get(v_r_2390_, 1);
v_v_2397_ = lean_ctor_get(v_r_2390_, 2);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_r_2390_);
if (v_isSharedCheck_2411_ == 0)
{
lean_object* v_unused_2412_; lean_object* v_unused_2413_; lean_object* v_unused_2414_; 
v_unused_2412_ = lean_ctor_get(v_r_2390_, 4);
lean_dec(v_unused_2412_);
v_unused_2413_ = lean_ctor_get(v_r_2390_, 3);
lean_dec(v_unused_2413_);
v_unused_2414_ = lean_ctor_get(v_r_2390_, 0);
lean_dec(v_unused_2414_);
v___x_2399_ = v_r_2390_;
v_isShared_2400_ = v_isSharedCheck_2411_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_v_2397_);
lean_inc(v_k_2396_);
lean_dec(v_r_2390_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2411_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2401_ = lean_unsigned_to_nat(3u);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 4, v_l_2373_);
lean_ctor_set(v___x_2399_, 3, v_l_2373_);
lean_ctor_set(v___x_2399_, 2, v_v_2392_);
lean_ctor_set(v___x_2399_, 1, v_k_2391_);
lean_ctor_set(v___x_2399_, 0, v___x_2287_);
v___x_2403_ = v___x_2399_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2410_, 1, v_k_2391_);
lean_ctor_set(v_reuseFailAlloc_2410_, 2, v_v_2392_);
lean_ctor_set(v_reuseFailAlloc_2410_, 3, v_l_2373_);
lean_ctor_set(v_reuseFailAlloc_2410_, 4, v_l_2373_);
v___x_2403_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2405_; 
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 4, v_l_2373_);
lean_ctor_set(v___x_2394_, 2, v_v_2140_);
lean_ctor_set(v___x_2394_, 1, v_k_2139_);
lean_ctor_set(v___x_2394_, 0, v___x_2287_);
v___x_2405_ = v___x_2394_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2409_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2409_, 3, v_l_2373_);
lean_ctor_set(v_reuseFailAlloc_2409_, 4, v_l_2373_);
v___x_2405_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2407_; 
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 4, v___x_2405_);
lean_ctor_set(v___x_2144_, 3, v___x_2403_);
lean_ctor_set(v___x_2144_, 2, v_v_2397_);
lean_ctor_set(v___x_2144_, 1, v_k_2396_);
lean_ctor_set(v___x_2144_, 0, v___x_2401_);
v___x_2407_ = v___x_2144_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v_k_2396_);
lean_ctor_set(v_reuseFailAlloc_2408_, 2, v_v_2397_);
lean_ctor_set(v_reuseFailAlloc_2408_, 3, v___x_2403_);
lean_ctor_set(v_reuseFailAlloc_2408_, 4, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
}
else
{
lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2419_ = lean_unsigned_to_nat(2u);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 4, v_r_2390_);
lean_ctor_set(v___x_2144_, 3, v_impl_2286_);
lean_ctor_set(v___x_2144_, 0, v___x_2419_);
v___x_2421_ = v___x_2144_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_k_2139_);
lean_ctor_set(v_reuseFailAlloc_2422_, 2, v_v_2140_);
lean_ctor_set(v_reuseFailAlloc_2422_, 3, v_impl_2286_);
lean_ctor_set(v_reuseFailAlloc_2422_, 4, v_r_2390_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = lean_unsigned_to_nat(1u);
v___x_2425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
lean_ctor_set(v___x_2425_, 1, v_k_2135_);
lean_ctor_set(v___x_2425_, 2, v_v_2136_);
lean_ctor_set(v___x_2425_, 3, v_t_2137_);
lean_ctor_set(v___x_2425_, 4, v_t_2137_);
return v___x_2425_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(lean_object* v_k_2426_, lean_object* v_t_2427_){
_start:
{
if (lean_obj_tag(v_t_2427_) == 0)
{
lean_object* v_k_2428_; lean_object* v_l_2429_; lean_object* v_r_2430_; uint8_t v___x_2431_; 
v_k_2428_ = lean_ctor_get(v_t_2427_, 1);
v_l_2429_ = lean_ctor_get(v_t_2427_, 3);
v_r_2430_ = lean_ctor_get(v_t_2427_, 4);
v___x_2431_ = lean_nat_dec_lt(v_k_2426_, v_k_2428_);
if (v___x_2431_ == 0)
{
uint8_t v___x_2432_; 
v___x_2432_ = lean_nat_dec_eq(v_k_2426_, v_k_2428_);
if (v___x_2432_ == 0)
{
v_t_2427_ = v_r_2430_;
goto _start;
}
else
{
return v___x_2432_;
}
}
else
{
v_t_2427_ = v_l_2429_;
goto _start;
}
}
else
{
uint8_t v___x_2435_; 
v___x_2435_ = 0;
return v___x_2435_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg___boxed(lean_object* v_k_2436_, lean_object* v_t_2437_){
_start:
{
uint8_t v_res_2438_; lean_object* v_r_2439_; 
v_res_2438_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2436_, v_t_2437_);
lean_dec(v_t_2437_);
lean_dec(v_k_2436_);
v_r_2439_ = lean_box(v_res_2438_);
return v_r_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(lean_object* v_y_2440_, lean_object* v_x_2441_, size_t v_x_2442_, size_t v_x_2443_){
_start:
{
if (lean_obj_tag(v_x_2441_) == 0)
{
lean_object* v_cs_2444_; size_t v_j_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; uint8_t v___x_2448_; 
v_cs_2444_ = lean_ctor_get(v_x_2441_, 0);
v_j_2445_ = lean_usize_shift_right(v_x_2442_, v_x_2443_);
v___x_2446_ = lean_usize_to_nat(v_j_2445_);
v___x_2447_ = lean_array_get_size(v_cs_2444_);
v___x_2448_ = lean_nat_dec_lt(v___x_2446_, v___x_2447_);
if (v___x_2448_ == 0)
{
lean_dec(v___x_2446_);
lean_dec(v_y_2440_);
return v_x_2441_;
}
else
{
lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2466_; 
lean_inc_ref(v_cs_2444_);
v_isSharedCheck_2466_ = !lean_is_exclusive(v_x_2441_);
if (v_isSharedCheck_2466_ == 0)
{
lean_object* v_unused_2467_; 
v_unused_2467_ = lean_ctor_get(v_x_2441_, 0);
lean_dec(v_unused_2467_);
v___x_2450_ = v_x_2441_;
v_isShared_2451_ = v_isSharedCheck_2466_;
goto v_resetjp_2449_;
}
else
{
lean_dec(v_x_2441_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2466_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
size_t v___x_2452_; size_t v___x_2453_; size_t v___x_2454_; size_t v_i_2455_; size_t v___x_2456_; size_t v_shift_2457_; lean_object* v_v_2458_; lean_object* v___x_2459_; lean_object* v_xs_x27_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2452_ = ((size_t)1ULL);
v___x_2453_ = lean_usize_shift_left(v___x_2452_, v_x_2443_);
v___x_2454_ = lean_usize_sub(v___x_2453_, v___x_2452_);
v_i_2455_ = lean_usize_land(v_x_2442_, v___x_2454_);
v___x_2456_ = ((size_t)5ULL);
v_shift_2457_ = lean_usize_sub(v_x_2443_, v___x_2456_);
v_v_2458_ = lean_array_fget(v_cs_2444_, v___x_2446_);
v___x_2459_ = lean_box(0);
v_xs_x27_2460_ = lean_array_fset(v_cs_2444_, v___x_2446_, v___x_2459_);
v___x_2461_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2440_, v_v_2458_, v_i_2455_, v_shift_2457_);
v___x_2462_ = lean_array_fset(v_xs_x27_2460_, v___x_2446_, v___x_2461_);
lean_dec(v___x_2446_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v___x_2462_);
v___x_2464_ = v___x_2450_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
else
{
lean_object* v_vs_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; uint8_t v___x_2471_; 
v_vs_2468_ = lean_ctor_get(v_x_2441_, 0);
v___x_2469_ = lean_usize_to_nat(v_x_2442_);
v___x_2470_ = lean_array_get_size(v_vs_2468_);
v___x_2471_ = lean_nat_dec_lt(v___x_2469_, v___x_2470_);
if (v___x_2471_ == 0)
{
lean_dec(v___x_2469_);
lean_dec(v_y_2440_);
return v_x_2441_;
}
else
{
lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2486_; 
lean_inc_ref(v_vs_2468_);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_x_2441_);
if (v_isSharedCheck_2486_ == 0)
{
lean_object* v_unused_2487_; 
v_unused_2487_ = lean_ctor_get(v_x_2441_, 0);
lean_dec(v_unused_2487_);
v___x_2473_ = v_x_2441_;
v_isShared_2474_ = v_isSharedCheck_2486_;
goto v_resetjp_2472_;
}
else
{
lean_dec(v_x_2441_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2486_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v_v_2475_; lean_object* v___x_2476_; lean_object* v_xs_x27_2477_; lean_object* v___y_2479_; uint8_t v___x_2484_; 
v_v_2475_ = lean_array_fget(v_vs_2468_, v___x_2469_);
v___x_2476_ = lean_box(0);
v_xs_x27_2477_ = lean_array_fset(v_vs_2468_, v___x_2469_, v___x_2476_);
v___x_2484_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2440_, v_v_2475_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; 
v___x_2485_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2440_, v___x_2476_, v_v_2475_);
v___y_2479_ = v___x_2485_;
goto v___jp_2478_;
}
else
{
lean_dec(v_y_2440_);
v___y_2479_ = v_v_2475_;
goto v___jp_2478_;
}
v___jp_2478_:
{
lean_object* v___x_2480_; lean_object* v___x_2482_; 
v___x_2480_ = lean_array_fset(v_xs_x27_2477_, v___x_2469_, v___y_2479_);
lean_dec(v___x_2469_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 0, v___x_2480_);
v___x_2482_ = v___x_2473_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2480_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2488_, lean_object* v_x_2489_, lean_object* v_x_2490_, lean_object* v_x_2491_){
_start:
{
size_t v_x_3896__boxed_2492_; size_t v_x_3897__boxed_2493_; lean_object* v_res_2494_; 
v_x_3896__boxed_2492_ = lean_unbox_usize(v_x_2490_);
lean_dec(v_x_2490_);
v_x_3897__boxed_2493_ = lean_unbox_usize(v_x_2491_);
lean_dec(v_x_2491_);
v_res_2494_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2488_, v_x_2489_, v_x_3896__boxed_2492_, v_x_3897__boxed_2493_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(lean_object* v_y_2495_, lean_object* v_t_2496_, lean_object* v_i_2497_){
_start:
{
lean_object* v_root_2498_; lean_object* v_tail_2499_; lean_object* v_size_2500_; size_t v_shift_2501_; lean_object* v_tailOff_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2529_; 
v_root_2498_ = lean_ctor_get(v_t_2496_, 0);
v_tail_2499_ = lean_ctor_get(v_t_2496_, 1);
v_size_2500_ = lean_ctor_get(v_t_2496_, 2);
v_shift_2501_ = lean_ctor_get_usize(v_t_2496_, 4);
v_tailOff_2502_ = lean_ctor_get(v_t_2496_, 3);
v_isSharedCheck_2529_ = !lean_is_exclusive(v_t_2496_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2504_ = v_t_2496_;
v_isShared_2505_ = v_isSharedCheck_2529_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_tailOff_2502_);
lean_inc(v_size_2500_);
lean_inc(v_tail_2499_);
lean_inc(v_root_2498_);
lean_dec(v_t_2496_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2529_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
uint8_t v___x_2506_; 
v___x_2506_ = lean_nat_dec_le(v_tailOff_2502_, v_i_2497_);
if (v___x_2506_ == 0)
{
size_t v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2510_; 
v___x_2507_ = lean_usize_of_nat(v_i_2497_);
v___x_2508_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2495_, v_root_2498_, v___x_2507_, v_shift_2501_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 0, v___x_2508_);
v___x_2510_ = v___x_2504_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_tail_2499_);
lean_ctor_set(v_reuseFailAlloc_2511_, 2, v_size_2500_);
lean_ctor_set(v_reuseFailAlloc_2511_, 3, v_tailOff_2502_);
lean_ctor_set_usize(v_reuseFailAlloc_2511_, 4, v_shift_2501_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
else
{
lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; 
v___x_2512_ = lean_nat_sub(v_i_2497_, v_tailOff_2502_);
v___x_2513_ = lean_array_get_size(v_tail_2499_);
v___x_2514_ = lean_nat_dec_lt(v___x_2512_, v___x_2513_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2516_; 
lean_dec(v___x_2512_);
lean_dec(v_y_2495_);
if (v_isShared_2505_ == 0)
{
v___x_2516_ = v___x_2504_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_root_2498_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_tail_2499_);
lean_ctor_set(v_reuseFailAlloc_2517_, 2, v_size_2500_);
lean_ctor_set(v_reuseFailAlloc_2517_, 3, v_tailOff_2502_);
lean_ctor_set_usize(v_reuseFailAlloc_2517_, 4, v_shift_2501_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
else
{
lean_object* v_v_2518_; lean_object* v___x_2519_; lean_object* v_xs_x27_2520_; lean_object* v___y_2522_; uint8_t v___x_2527_; 
v_v_2518_ = lean_array_fget(v_tail_2499_, v___x_2512_);
v___x_2519_ = lean_box(0);
v_xs_x27_2520_ = lean_array_fset(v_tail_2499_, v___x_2512_, v___x_2519_);
v___x_2527_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2495_, v_v_2518_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; 
v___x_2528_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2495_, v___x_2519_, v_v_2518_);
v___y_2522_ = v___x_2528_;
goto v___jp_2521_;
}
else
{
lean_dec(v_y_2495_);
v___y_2522_ = v_v_2518_;
goto v___jp_2521_;
}
v___jp_2521_:
{
lean_object* v___x_2523_; lean_object* v___x_2525_; 
v___x_2523_ = lean_array_fset(v_xs_x27_2520_, v___x_2512_, v___y_2522_);
lean_dec(v___x_2512_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 1, v___x_2523_);
v___x_2525_ = v___x_2504_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_root_2498_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v___x_2523_);
lean_ctor_set(v_reuseFailAlloc_2526_, 2, v_size_2500_);
lean_ctor_set(v_reuseFailAlloc_2526_, 3, v_tailOff_2502_);
lean_ctor_set_usize(v_reuseFailAlloc_2526_, 4, v_shift_2501_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2___boxed(lean_object* v_y_2530_, lean_object* v_t_2531_, lean_object* v_i_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2530_, v_t_2531_, v_i_2532_);
lean_dec(v_i_2532_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(lean_object* v_y_2534_, lean_object* v_x_2535_, lean_object* v_s_2536_){
_start:
{
lean_object* v_vars_2537_; lean_object* v_varMap_2538_; lean_object* v_varsHistory_2539_; lean_object* v_natToIntMap_2540_; lean_object* v_natDef_2541_; lean_object* v_dvds_2542_; lean_object* v_lowers_2543_; lean_object* v_uppers_2544_; lean_object* v_diseqs_2545_; lean_object* v_elimEqs_2546_; lean_object* v_elimStack_2547_; lean_object* v_occurs_2548_; lean_object* v_assignment_2549_; lean_object* v_nextCnstrId_2550_; uint8_t v_caseSplits_2551_; lean_object* v_steps_2552_; lean_object* v_conflict_x3f_2553_; lean_object* v_diseqSplits_2554_; lean_object* v_divMod_2555_; uint8_t v_usedCommRing_2556_; lean_object* v_nonlinearOccs_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2565_; 
v_vars_2537_ = lean_ctor_get(v_s_2536_, 0);
v_varMap_2538_ = lean_ctor_get(v_s_2536_, 1);
v_varsHistory_2539_ = lean_ctor_get(v_s_2536_, 2);
v_natToIntMap_2540_ = lean_ctor_get(v_s_2536_, 3);
v_natDef_2541_ = lean_ctor_get(v_s_2536_, 4);
v_dvds_2542_ = lean_ctor_get(v_s_2536_, 5);
v_lowers_2543_ = lean_ctor_get(v_s_2536_, 6);
v_uppers_2544_ = lean_ctor_get(v_s_2536_, 7);
v_diseqs_2545_ = lean_ctor_get(v_s_2536_, 8);
v_elimEqs_2546_ = lean_ctor_get(v_s_2536_, 9);
v_elimStack_2547_ = lean_ctor_get(v_s_2536_, 10);
v_occurs_2548_ = lean_ctor_get(v_s_2536_, 11);
v_assignment_2549_ = lean_ctor_get(v_s_2536_, 12);
v_nextCnstrId_2550_ = lean_ctor_get(v_s_2536_, 13);
v_caseSplits_2551_ = lean_ctor_get_uint8(v_s_2536_, sizeof(void*)*19);
v_steps_2552_ = lean_ctor_get(v_s_2536_, 14);
v_conflict_x3f_2553_ = lean_ctor_get(v_s_2536_, 15);
v_diseqSplits_2554_ = lean_ctor_get(v_s_2536_, 16);
v_divMod_2555_ = lean_ctor_get(v_s_2536_, 17);
v_usedCommRing_2556_ = lean_ctor_get_uint8(v_s_2536_, sizeof(void*)*19 + 1);
v_nonlinearOccs_2557_ = lean_ctor_get(v_s_2536_, 18);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_s_2536_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2559_ = v_s_2536_;
v_isShared_2560_ = v_isSharedCheck_2565_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_nonlinearOccs_2557_);
lean_inc(v_divMod_2555_);
lean_inc(v_diseqSplits_2554_);
lean_inc(v_conflict_x3f_2553_);
lean_inc(v_steps_2552_);
lean_inc(v_nextCnstrId_2550_);
lean_inc(v_assignment_2549_);
lean_inc(v_occurs_2548_);
lean_inc(v_elimStack_2547_);
lean_inc(v_elimEqs_2546_);
lean_inc(v_diseqs_2545_);
lean_inc(v_uppers_2544_);
lean_inc(v_lowers_2543_);
lean_inc(v_dvds_2542_);
lean_inc(v_natDef_2541_);
lean_inc(v_natToIntMap_2540_);
lean_inc(v_varsHistory_2539_);
lean_inc(v_varMap_2538_);
lean_inc(v_vars_2537_);
lean_dec(v_s_2536_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2565_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2561_; lean_object* v___x_2563_; 
v___x_2561_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2534_, v_occurs_2548_, v_x_2535_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 11, v___x_2561_);
v___x_2563_ = v___x_2559_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_vars_2537_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_varMap_2538_);
lean_ctor_set(v_reuseFailAlloc_2564_, 2, v_varsHistory_2539_);
lean_ctor_set(v_reuseFailAlloc_2564_, 3, v_natToIntMap_2540_);
lean_ctor_set(v_reuseFailAlloc_2564_, 4, v_natDef_2541_);
lean_ctor_set(v_reuseFailAlloc_2564_, 5, v_dvds_2542_);
lean_ctor_set(v_reuseFailAlloc_2564_, 6, v_lowers_2543_);
lean_ctor_set(v_reuseFailAlloc_2564_, 7, v_uppers_2544_);
lean_ctor_set(v_reuseFailAlloc_2564_, 8, v_diseqs_2545_);
lean_ctor_set(v_reuseFailAlloc_2564_, 9, v_elimEqs_2546_);
lean_ctor_set(v_reuseFailAlloc_2564_, 10, v_elimStack_2547_);
lean_ctor_set(v_reuseFailAlloc_2564_, 11, v___x_2561_);
lean_ctor_set(v_reuseFailAlloc_2564_, 12, v_assignment_2549_);
lean_ctor_set(v_reuseFailAlloc_2564_, 13, v_nextCnstrId_2550_);
lean_ctor_set(v_reuseFailAlloc_2564_, 14, v_steps_2552_);
lean_ctor_set(v_reuseFailAlloc_2564_, 15, v_conflict_x3f_2553_);
lean_ctor_set(v_reuseFailAlloc_2564_, 16, v_diseqSplits_2554_);
lean_ctor_set(v_reuseFailAlloc_2564_, 17, v_divMod_2555_);
lean_ctor_set(v_reuseFailAlloc_2564_, 18, v_nonlinearOccs_2557_);
lean_ctor_set_uint8(v_reuseFailAlloc_2564_, sizeof(void*)*19, v_caseSplits_2551_);
lean_ctor_set_uint8(v_reuseFailAlloc_2564_, sizeof(void*)*19 + 1, v_usedCommRing_2556_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed(lean_object* v_y_2566_, lean_object* v_x_2567_, lean_object* v_s_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(v_y_2566_, v_x_2567_, v_s_2568_);
lean_dec(v_x_2567_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(lean_object* v_x_2570_, lean_object* v_y_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v___f_2575_; lean_object* v___x_2576_; 
lean_inc(v_x_2570_);
lean_inc(v_y_2571_);
v___f_2575_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2575_, 0, v_y_2571_);
lean_closure_set(v___f_2575_, 1, v_x_2570_);
v___x_2576_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2570_, v_a_2572_, v_a_2573_);
lean_dec(v_x_2570_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2588_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2588_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2588_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
uint8_t v___x_2581_; 
v___x_2581_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2571_, v_a_2577_);
lean_dec(v_a_2577_);
lean_dec(v_y_2571_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
lean_del_object(v___x_2579_);
v___x_2582_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2583_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2582_, v___f_2575_, v_a_2572_);
return v___x_2583_;
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
lean_dec_ref(v___f_2575_);
v___x_2584_ = lean_box(0);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2584_);
v___x_2586_ = v___x_2579_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec_ref(v___f_2575_);
lean_dec(v_y_2571_);
v_a_2589_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2576_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2576_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___boxed(lean_object* v_x_2597_, lean_object* v_y_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2597_, v_y_2598_, v_a_2599_, v_a_2600_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc(lean_object* v_x_2603_, lean_object* v_y_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2603_, v_y_2604_, v_a_2605_, v_a_2613_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___boxed(lean_object* v_x_2617_, lean_object* v_y_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc(v_x_2617_, v_y_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
lean_dec(v_a_2622_);
lean_dec_ref(v_a_2621_);
lean_dec(v_a_2620_);
lean_dec(v_a_2619_);
return v_res_2630_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(lean_object* v_00_u03b2_2631_, lean_object* v_k_2632_, lean_object* v_t_2633_){
_start:
{
uint8_t v___x_2634_; 
v___x_2634_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2632_, v_t_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2635_, lean_object* v_k_2636_, lean_object* v_t_2637_){
_start:
{
uint8_t v_res_2638_; lean_object* v_r_2639_; 
v_res_2638_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(v_00_u03b2_2635_, v_k_2636_, v_t_2637_);
lean_dec(v_t_2637_);
lean_dec(v_k_2636_);
v_r_2639_ = lean_box(v_res_2638_);
return v_r_2639_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1(lean_object* v_00_u03b2_2640_, lean_object* v_k_2641_, lean_object* v_v_2642_, lean_object* v_t_2643_, lean_object* v_hl_2644_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2641_, v_v_2642_, v_t_2643_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(lean_object* v_y_2646_, lean_object* v_p_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_){
_start:
{
if (lean_obj_tag(v_p_2647_) == 1)
{
lean_object* v_v_2651_; lean_object* v_p_2652_; lean_object* v___x_2653_; 
v_v_2651_ = lean_ctor_get(v_p_2647_, 1);
lean_inc(v_v_2651_);
v_p_2652_ = lean_ctor_get(v_p_2647_, 2);
lean_inc_ref(v_p_2652_);
lean_dec_ref_known(v_p_2647_, 3);
lean_inc(v_y_2646_);
v___x_2653_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_v_2651_, v_y_2646_, v_a_2648_, v_a_2649_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_dec_ref_known(v___x_2653_, 1);
v_p_2647_ = v_p_2652_;
goto _start;
}
else
{
lean_dec_ref(v_p_2652_);
lean_dec(v_y_2646_);
return v___x_2653_;
}
}
else
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
lean_dec_ref(v_p_2647_);
lean_dec(v_y_2646_);
v___x_2655_ = lean_box(0);
v___x_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
return v___x_2656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg___boxed(lean_object* v_y_2657_, lean_object* v_p_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2657_, v_p_2658_, v_a_2659_, v_a_2660_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(lean_object* v_y_2663_, lean_object* v_p_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2663_, v_p_2664_, v_a_2665_, v_a_2673_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___boxed(lean_object* v_y_2677_, lean_object* v_p_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(v_y_2677_, v_p_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec(v_a_2679_);
return v_res_2690_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = ((lean_object*)(l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__0));
v___x_2693_ = l_Lean_stringToMessageData(v___x_2692_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg(lean_object* v_p_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
if (lean_obj_tag(v_p_2694_) == 1)
{
lean_object* v_v_2701_; lean_object* v_p_2702_; lean_object* v___x_2703_; 
v_v_2701_ = lean_ctor_get(v_p_2694_, 1);
lean_inc(v_v_2701_);
v_p_2702_ = lean_ctor_get(v_p_2694_, 2);
lean_inc_ref(v_p_2702_);
lean_dec_ref_known(v_p_2694_, 3);
v___x_2703_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_v_2701_, v_p_2702_, v_a_2695_, v_a_2698_);
return v___x_2703_;
}
else
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
lean_dec_ref(v_p_2694_);
v___x_2704_ = lean_obj_once(&l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1, &l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1_once, _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1);
v___x_2705_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2704_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
return v___x_2705_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg___boxed(lean_object* v_p_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec(v_a_2707_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs(lean_object* v_p_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2714_, v_a_2715_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___boxed(lean_object* v_p_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Int_Internal_Linear_Poly_updateOccs(v_p_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
lean_dec(v_a_2737_);
lean_dec_ref(v_a_2736_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
lean_dec(v_a_2733_);
lean_dec_ref(v_a_2732_);
lean_dec(v_a_2731_);
lean_dec_ref(v_a_2730_);
lean_dec(v_a_2729_);
lean_dec(v_a_2728_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go_spec__0(lean_object* v_a_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Rat_ofInt(v_a_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(lean_object* v_a_2742_, lean_object* v_v_2743_, lean_object* v_a_2744_){
_start:
{
if (lean_obj_tag(v_a_2744_) == 0)
{
lean_object* v_k_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2754_; 
v_k_2745_ = lean_ctor_get(v_a_2744_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_a_2744_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2747_ = v_a_2744_;
v_isShared_2748_ = v_isSharedCheck_2754_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_k_2745_);
lean_dec(v_a_2744_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2754_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2749_ = l_Rat_ofInt(v_k_2745_);
v___x_2750_ = l_Rat_add(v_v_2743_, v___x_2749_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set_tag(v___x_2747_, 1);
lean_ctor_set(v___x_2747_, 0, v___x_2750_);
v___x_2752_ = v___x_2747_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
else
{
lean_object* v_k_2755_; lean_object* v_v_2756_; lean_object* v_p_2757_; lean_object* v_size_2758_; uint8_t v___x_2759_; 
v_k_2755_ = lean_ctor_get(v_a_2744_, 0);
lean_inc(v_k_2755_);
v_v_2756_ = lean_ctor_get(v_a_2744_, 1);
lean_inc(v_v_2756_);
v_p_2757_ = lean_ctor_get(v_a_2744_, 2);
lean_inc_ref(v_p_2757_);
lean_dec_ref_known(v_a_2744_, 3);
v_size_2758_ = lean_ctor_get(v_a_2742_, 2);
v___x_2759_ = lean_nat_dec_lt(v_v_2756_, v_size_2758_);
if (v___x_2759_ == 0)
{
lean_object* v___x_2760_; 
lean_dec_ref(v_p_2757_);
lean_dec(v_v_2756_);
lean_dec(v_k_2755_);
lean_dec_ref(v_v_2743_);
v___x_2760_ = lean_box(0);
return v___x_2760_;
}
else
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2761_ = l_instInhabitedRat;
v___x_2762_ = l_Rat_ofInt(v_k_2755_);
v___x_2763_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2761_, v_a_2742_, v_v_2756_);
lean_dec(v_v_2756_);
v___x_2764_ = l_Rat_mul(v___x_2762_, v___x_2763_);
lean_dec_ref(v___x_2762_);
v___x_2765_ = l_Rat_add(v_v_2743_, v___x_2764_);
v_v_2743_ = v___x_2765_;
v_a_2744_ = v_p_2757_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go___boxed(lean_object* v_a_2767_, lean_object* v_v_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_a_2767_, v_v_2768_, v_a_2769_);
lean_dec_ref(v_a_2767_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(lean_object* v_a_2771_){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = lean_nat_to_int(v_a_2771_);
v___x_2773_ = l_Rat_ofInt(v___x_2772_);
return v___x_2773_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = lean_unsigned_to_nat(0u);
v___x_2775_ = l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(v___x_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg(lean_object* v_p_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2777_, v_a_2778_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2791_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2783_ = v___x_2780_;
v_isShared_2784_ = v_isSharedCheck_2791_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2780_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2791_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v_assignment_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2789_; 
v_assignment_2785_ = lean_ctor_get(v_a_2781_, 12);
lean_inc_ref(v_assignment_2785_);
lean_dec(v_a_2781_);
v___x_2786_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2787_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_assignment_2785_, v___x_2786_, v_p_2776_);
lean_dec_ref(v_assignment_2785_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v___x_2787_);
v___x_2789_ = v___x_2783_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec_ref(v_p_2776_);
v_a_2792_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2780_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2780_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg___boxed(lean_object* v_p_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2800_, v_a_2801_, v_a_2802_);
lean_dec_ref(v_a_2802_);
lean_dec(v_a_2801_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f(lean_object* v_p_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2805_, v_a_2806_, v_a_2814_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___boxed(lean_object* v_p_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Int_Internal_Linear_Poly_eval_x3f(v_p_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
lean_dec(v_a_2828_);
lean_dec_ref(v_a_2827_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
lean_dec(v_a_2824_);
lean_dec_ref(v_a_2823_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec(v_a_2819_);
return v_res_2830_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(lean_object* v_c_2831_){
_start:
{
lean_object* v_p_2832_; uint8_t v___x_2833_; 
v_p_2832_ = lean_ctor_get(v_c_2831_, 0);
v___x_2833_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat___boxed(lean_object* v_c_2834_){
_start:
{
uint8_t v_res_2835_; lean_object* v_r_2836_; 
v_res_2835_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(v_c_2834_);
lean_dec_ref(v_c_2834_);
v_r_2836_ = lean_box(v_res_2835_);
return v_r_2836_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(lean_object* v_c_2837_){
_start:
{
lean_object* v_d_2838_; lean_object* v_p_2839_; uint8_t v___x_2840_; 
v_d_2838_ = lean_ctor_get(v_c_2837_, 0);
lean_inc(v_d_2838_);
v_p_2839_ = lean_ctor_get(v_c_2837_, 1);
lean_inc_ref(v_p_2839_);
lean_dec_ref(v_c_2837_);
v___x_2840_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_2838_, v_p_2839_);
lean_dec_ref(v_p_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat___boxed(lean_object* v_c_2841_){
_start:
{
uint8_t v_res_2842_; lean_object* v_r_2843_; 
v_res_2842_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(v_c_2841_);
v_r_2843_ = lean_box(v_res_2842_);
return v_r_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object* v_c_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_){
_start:
{
lean_object* v_d_2848_; lean_object* v_p_2849_; lean_object* v___x_2850_; 
v_d_2848_ = lean_ctor_get(v_c_2844_, 0);
lean_inc(v_d_2848_);
v_p_2849_ = lean_ctor_get(v_c_2844_, 1);
lean_inc_ref(v_p_2849_);
lean_dec_ref(v_c_2844_);
v___x_2850_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2849_, v_a_2845_, v_a_2846_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2878_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2853_ = v___x_2850_;
v_isShared_2854_ = v_isSharedCheck_2878_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2850_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2878_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
if (lean_obj_tag(v_a_2851_) == 1)
{
lean_object* v_val_2855_; lean_object* v_num_2856_; lean_object* v_den_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v_val_2855_ = lean_ctor_get(v_a_2851_, 0);
lean_inc(v_val_2855_);
lean_dec_ref_known(v_a_2851_, 1);
v_num_2856_ = lean_ctor_get(v_val_2855_, 0);
lean_inc(v_num_2856_);
v_den_2857_ = lean_ctor_get(v_val_2855_, 1);
lean_inc(v_den_2857_);
lean_dec(v_val_2855_);
v___x_2858_ = lean_unsigned_to_nat(1u);
v___x_2859_ = lean_nat_dec_eq(v_den_2857_, v___x_2858_);
lean_dec(v_den_2857_);
if (v___x_2859_ == 0)
{
uint8_t v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2863_; 
lean_dec(v_num_2856_);
lean_dec(v_d_2848_);
v___x_2860_ = 0;
v___x_2861_ = lean_box(v___x_2860_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v___x_2861_);
v___x_2863_ = v___x_2853_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2861_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; uint8_t v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2871_; 
v___x_2865_ = lean_int_emod(v_num_2856_, v_d_2848_);
lean_dec(v_d_2848_);
lean_dec(v_num_2856_);
v___x_2866_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_2867_ = lean_int_dec_eq(v___x_2865_, v___x_2866_);
lean_dec(v___x_2865_);
v___x_2868_ = l_Lean_Bool_toLBool(v___x_2867_);
v___x_2869_ = lean_box(v___x_2868_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v___x_2869_);
v___x_2871_ = v___x_2853_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2869_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
else
{
uint8_t v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2876_; 
lean_dec(v_a_2851_);
lean_dec(v_d_2848_);
v___x_2873_ = 2;
v___x_2874_ = lean_box(v___x_2873_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v___x_2874_);
v___x_2876_ = v___x_2853_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec(v_d_2848_);
v_a_2879_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2850_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2850_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg___boxed(lean_object* v_c_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2887_, v_a_2888_, v_a_2889_);
lean_dec_ref(v_a_2889_);
lean_dec(v_a_2888_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(lean_object* v_c_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2892_, v_a_2893_, v_a_2901_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___boxed(lean_object* v_c_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(v_c_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_);
lean_dec(v_a_2915_);
lean_dec_ref(v_a_2914_);
lean_dec(v_a_2913_);
lean_dec_ref(v_a_2912_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec(v_a_2906_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg(lean_object* v_p_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2918_, v_a_2919_, v_a_2920_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2940_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2925_ = v___x_2922_;
v_isShared_2926_ = v_isSharedCheck_2940_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2922_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2940_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
if (lean_obj_tag(v_a_2923_) == 1)
{
lean_object* v_val_2927_; lean_object* v___x_2928_; uint8_t v___x_2929_; uint8_t v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2933_; 
v_val_2927_ = lean_ctor_get(v_a_2923_, 0);
lean_inc(v_val_2927_);
lean_dec_ref_known(v_a_2923_, 1);
v___x_2928_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2929_ = l_Rat_instDecidableLe(v_val_2927_, v___x_2928_);
v___x_2930_ = l_Lean_Bool_toLBool(v___x_2929_);
v___x_2931_ = lean_box(v___x_2930_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 0, v___x_2931_);
v___x_2933_ = v___x_2925_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v___x_2931_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
else
{
uint8_t v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2938_; 
lean_dec(v_a_2923_);
v___x_2935_ = 2;
v___x_2936_ = lean_box(v___x_2935_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 0, v___x_2936_);
v___x_2938_ = v___x_2925_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2936_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
v_a_2941_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2922_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2922_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg___boxed(lean_object* v_p_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2949_, v_a_2950_, v_a_2951_);
lean_dec_ref(v_a_2951_);
lean_dec(v_a_2950_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe(lean_object* v_p_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2954_, v_a_2955_, v_a_2963_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___boxed(lean_object* v_p_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_Int_Internal_Linear_Poly_satisfiedLe(v_p_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_);
lean_dec(v_a_2977_);
lean_dec_ref(v_a_2976_);
lean_dec(v_a_2975_);
lean_dec_ref(v_a_2974_);
lean_dec(v_a_2973_);
lean_dec_ref(v_a_2972_);
lean_dec(v_a_2971_);
lean_dec_ref(v_a_2970_);
lean_dec(v_a_2969_);
lean_dec(v_a_2968_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(lean_object* v_c_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v_p_2984_; lean_object* v___x_2985_; 
v_p_2984_ = lean_ctor_get(v_c_2980_, 0);
lean_inc_ref(v_p_2984_);
lean_dec_ref(v_c_2980_);
v___x_2985_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2984_, v_a_2981_, v_a_2982_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg___boxed(lean_object* v_c_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2986_, v_a_2987_, v_a_2988_);
lean_dec_ref(v_a_2988_);
lean_dec(v_a_2987_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(lean_object* v_c_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2991_, v_a_2992_, v_a_3000_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___boxed(lean_object* v_c_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(v_c_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
lean_dec(v_a_3006_);
lean_dec(v_a_3005_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(lean_object* v_c_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v_p_3021_; lean_object* v___x_3022_; 
v_p_3021_ = lean_ctor_get(v_c_3017_, 0);
lean_inc_ref(v_p_3021_);
lean_dec_ref(v_c_3017_);
v___x_3022_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3021_, v_a_3018_, v_a_3019_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3042_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3025_ = v___x_3022_;
v_isShared_3026_ = v_isSharedCheck_3042_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3022_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3042_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
uint8_t v___y_3028_; 
if (lean_obj_tag(v_a_3023_) == 1)
{
lean_object* v_val_3034_; lean_object* v___x_3035_; uint8_t v___x_3036_; 
v_val_3034_ = lean_ctor_get(v_a_3023_, 0);
lean_inc(v_val_3034_);
lean_dec_ref_known(v_a_3023_, 1);
v___x_3035_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_3036_ = l_instDecidableEqRat_decEq(v_val_3034_, v___x_3035_);
lean_dec(v_val_3034_);
if (v___x_3036_ == 0)
{
uint8_t v___x_3037_; 
v___x_3037_ = 1;
v___y_3028_ = v___x_3037_;
goto v___jp_3027_;
}
else
{
uint8_t v___x_3038_; 
v___x_3038_ = 0;
v___y_3028_ = v___x_3038_;
goto v___jp_3027_;
}
}
else
{
uint8_t v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
lean_del_object(v___x_3025_);
lean_dec(v_a_3023_);
v___x_3039_ = 2;
v___x_3040_ = lean_box(v___x_3039_);
v___x_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
return v___x_3041_;
}
v___jp_3027_:
{
uint8_t v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3032_; 
v___x_3029_ = l_Lean_Bool_toLBool(v___y_3028_);
v___x_3030_ = lean_box(v___x_3029_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 0, v___x_3030_);
v___x_3032_ = v___x_3025_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_3030_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
v_a_3043_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3022_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3022_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
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
return v___x_3048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg___boxed(lean_object* v_c_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_3051_, v_a_3052_, v_a_3053_);
lean_dec_ref(v_a_3053_);
lean_dec(v_a_3052_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(lean_object* v_c_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_3056_, v_a_3057_, v_a_3065_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___boxed(lean_object* v_c_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(v_c_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec(v_a_3075_);
lean_dec_ref(v_a_3074_);
lean_dec(v_a_3073_);
lean_dec_ref(v_a_3072_);
lean_dec(v_a_3071_);
lean_dec(v_a_3070_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(lean_object* v_c_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v_p_3086_; lean_object* v___x_3087_; 
v_p_3086_ = lean_ctor_get(v_c_3082_, 0);
lean_inc_ref(v_p_3086_);
lean_dec_ref(v_c_3082_);
v___x_3087_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3086_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3105_; 
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3090_ = v___x_3087_;
v_isShared_3091_ = v_isSharedCheck_3105_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3087_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3105_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
if (lean_obj_tag(v_a_3088_) == 1)
{
lean_object* v_val_3092_; lean_object* v___x_3093_; uint8_t v___x_3094_; uint8_t v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3098_; 
v_val_3092_ = lean_ctor_get(v_a_3088_, 0);
lean_inc(v_val_3092_);
lean_dec_ref_known(v_a_3088_, 1);
v___x_3093_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_3094_ = l_instDecidableEqRat_decEq(v_val_3092_, v___x_3093_);
lean_dec(v_val_3092_);
v___x_3095_ = l_Lean_Bool_toLBool(v___x_3094_);
v___x_3096_ = lean_box(v___x_3095_);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v___x_3096_);
v___x_3098_ = v___x_3090_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3096_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
else
{
uint8_t v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3103_; 
lean_dec(v_a_3088_);
v___x_3100_ = 2;
v___x_3101_ = lean_box(v___x_3100_);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v___x_3101_);
v___x_3103_ = v___x_3090_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3101_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
v_a_3106_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3087_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3087_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg___boxed(lean_object* v_c_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_3114_, v_a_3115_, v_a_3116_);
lean_dec_ref(v_a_3116_);
lean_dec(v_a_3115_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(lean_object* v_c_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_3119_, v_a_3120_, v_a_3128_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___boxed(lean_object* v_c_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(v_c_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
lean_dec(v_a_3140_);
lean_dec_ref(v_a_3139_);
lean_dec(v_a_3138_);
lean_dec_ref(v_a_3137_);
lean_dec(v_a_3136_);
lean_dec_ref(v_a_3135_);
lean_dec(v_a_3134_);
lean_dec(v_a_3133_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg(lean_object* v_p_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_){
_start:
{
if (lean_obj_tag(v_p_3145_) == 0)
{
lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3156_; 
v_isSharedCheck_3156_ = !lean_is_exclusive(v_p_3145_);
if (v_isSharedCheck_3156_ == 0)
{
lean_object* v_unused_3157_; 
v_unused_3157_ = lean_ctor_get(v_p_3145_, 0);
lean_dec(v_unused_3157_);
v___x_3150_ = v_p_3145_;
v_isShared_3151_ = v_isSharedCheck_3156_;
goto v_resetjp_3149_;
}
else
{
lean_dec(v_p_3145_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3156_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; lean_object* v___x_3154_; 
v___x_3152_ = lean_box(0);
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 0, v___x_3152_);
v___x_3154_ = v___x_3150_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v___x_3152_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
else
{
lean_object* v_k_3158_; lean_object* v_v_3159_; lean_object* v_p_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v_k_3158_ = lean_ctor_get(v_p_3145_, 0);
lean_inc(v_k_3158_);
v_v_3159_ = lean_ctor_get(v_p_3145_, 1);
lean_inc(v_v_3159_);
v_p_3160_ = lean_ctor_get(v_p_3145_, 2);
lean_inc_ref(v_p_3160_);
lean_dec_ref_known(v_p_3145_, 3);
v___x_3161_ = lean_box(0);
v___x_3162_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3146_, v_a_3147_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3188_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3165_ = v___x_3162_;
v_isShared_3166_ = v_isSharedCheck_3188_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3162_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3188_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___y_3168_; lean_object* v_elimEqs_3183_; lean_object* v_size_3184_; uint8_t v___x_3185_; 
v_elimEqs_3183_ = lean_ctor_get(v_a_3163_, 9);
lean_inc_ref(v_elimEqs_3183_);
lean_dec(v_a_3163_);
v_size_3184_ = lean_ctor_get(v_elimEqs_3183_, 2);
v___x_3185_ = lean_nat_dec_lt(v_v_3159_, v_size_3184_);
if (v___x_3185_ == 0)
{
lean_object* v___x_3186_; 
lean_dec_ref(v_elimEqs_3183_);
v___x_3186_ = l_outOfBounds___redArg(v___x_3161_);
v___y_3168_ = v___x_3186_;
goto v___jp_3167_;
}
else
{
lean_object* v___x_3187_; 
v___x_3187_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3161_, v_elimEqs_3183_, v_v_3159_);
lean_dec_ref(v_elimEqs_3183_);
v___y_3168_ = v___x_3187_;
goto v___jp_3167_;
}
v___jp_3167_:
{
if (lean_obj_tag(v___y_3168_) == 1)
{
lean_object* v_val_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3181_; 
lean_dec_ref(v_p_3160_);
v_val_3169_ = lean_ctor_get(v___y_3168_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___y_3168_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3171_ = v___y_3168_;
v_isShared_3172_ = v_isSharedCheck_3181_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_val_3169_);
lean_dec(v___y_3168_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3181_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3176_; 
v___x_3173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3173_, 0, v_v_3159_);
lean_ctor_set(v___x_3173_, 1, v_val_3169_);
v___x_3174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3174_, 0, v_k_3158_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 0, v___x_3174_);
v___x_3176_ = v___x_3171_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v___x_3174_);
v___x_3176_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
lean_object* v___x_3178_; 
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 0, v___x_3176_);
v___x_3178_ = v___x_3165_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
else
{
lean_dec(v___y_3168_);
lean_del_object(v___x_3165_);
lean_dec(v_v_3159_);
lean_dec(v_k_3158_);
v_p_3145_ = v_p_3160_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec_ref(v_p_3160_);
lean_dec(v_v_3159_);
lean_dec(v_k_3158_);
v_a_3189_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3162_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3162_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg___boxed(lean_object* v_p_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_3197_, v_a_3198_, v_a_3199_);
lean_dec_ref(v_a_3199_);
lean_dec(v_a_3198_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst(lean_object* v_p_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_){
_start:
{
lean_object* v___x_3214_; 
v___x_3214_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_3202_, v_a_3203_, v_a_3211_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___boxed(lean_object* v_p_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Int_Internal_Linear_Poly_findVarToSubst(v_p_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
lean_dec(v_a_3217_);
lean_dec(v_a_3216_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(lean_object* v_pred_3228_){
_start:
{
lean_object* v_c_u2081_3229_; lean_object* v_c_u2082_3230_; uint8_t v_left_3231_; lean_object* v_c_u2083_x3f_3232_; lean_object* v_p_3233_; lean_object* v_p_3234_; lean_object* v_a_3235_; lean_object* v_b_3236_; 
v_c_u2081_3229_ = lean_ctor_get(v_pred_3228_, 0);
v_c_u2082_3230_ = lean_ctor_get(v_pred_3228_, 1);
v_left_3231_ = lean_ctor_get_uint8(v_pred_3228_, sizeof(void*)*3);
v_c_u2083_x3f_3232_ = lean_ctor_get(v_pred_3228_, 2);
v_p_3233_ = lean_ctor_get(v_c_u2081_3229_, 0);
v_p_3234_ = lean_ctor_get(v_c_u2082_3230_, 0);
v_a_3235_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3233_);
v_b_3236_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3234_);
if (lean_obj_tag(v_c_u2083_x3f_3232_) == 0)
{
if (v_left_3231_ == 0)
{
lean_object* v___x_3237_; 
lean_dec(v_a_3235_);
v___x_3237_ = lean_nat_abs(v_b_3236_);
lean_dec(v_b_3236_);
return v___x_3237_;
}
else
{
lean_object* v___x_3238_; 
lean_dec(v_b_3236_);
v___x_3238_ = lean_nat_abs(v_a_3235_);
lean_dec(v_a_3235_);
return v___x_3238_;
}
}
else
{
lean_object* v_val_3239_; lean_object* v_d_3240_; lean_object* v_p_3241_; lean_object* v_c_3242_; 
v_val_3239_ = lean_ctor_get(v_c_u2083_x3f_3232_, 0);
v_d_3240_ = lean_ctor_get(v_val_3239_, 0);
v_p_3241_ = lean_ctor_get(v_val_3239_, 1);
v_c_3242_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3241_);
if (v_left_3231_ == 0)
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
lean_dec(v_a_3235_);
v___x_3243_ = lean_int_mul(v_b_3236_, v_d_3240_);
v___x_3244_ = l_Int_gcd(v___x_3243_, v_c_3242_);
lean_dec(v_c_3242_);
v___x_3245_ = lean_nat_to_int(v___x_3244_);
v___x_3246_ = lean_int_ediv(v___x_3243_, v___x_3245_);
lean_dec(v___x_3245_);
lean_dec(v___x_3243_);
v___x_3247_ = l_Int_lcm(v_b_3236_, v___x_3246_);
lean_dec(v___x_3246_);
lean_dec(v_b_3236_);
return v___x_3247_;
}
else
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
lean_dec(v_b_3236_);
v___x_3248_ = lean_int_mul(v_a_3235_, v_d_3240_);
v___x_3249_ = l_Int_gcd(v___x_3248_, v_c_3242_);
lean_dec(v_c_3242_);
v___x_3250_ = lean_nat_to_int(v___x_3249_);
v___x_3251_ = lean_int_ediv(v___x_3248_, v___x_3250_);
lean_dec(v___x_3250_);
lean_dec(v___x_3248_);
v___x_3252_ = l_Int_lcm(v_a_3235_, v___x_3251_);
lean_dec(v___x_3251_);
lean_dec(v_a_3235_);
return v___x_3252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases___boxed(lean_object* v_pred_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(v_pred_3253_);
lean_dec_ref(v_pred_3253_);
return v_res_3254_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3256_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0));
v___x_3257_ = l_Lean_stringToMessageData(v___x_3256_);
return v___x_3257_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4(void){
_start:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3261_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3));
v___x_3262_ = l_Lean_MessageData_ofFormat(v___x_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(lean_object* v_pred_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v_c_u2081_3267_; lean_object* v_c_u2082_3268_; lean_object* v_c_u2083_x3f_3269_; lean_object* v___x_3270_; 
v_c_u2081_3267_ = lean_ctor_get(v_pred_3263_, 0);
lean_inc_ref(v_c_u2081_3267_);
v_c_u2082_3268_ = lean_ctor_get(v_pred_3263_, 1);
lean_inc_ref(v_c_u2082_3268_);
v_c_u2083_x3f_3269_ = lean_ctor_get(v_pred_3263_, 2);
lean_inc(v_c_u2083_x3f_3269_);
lean_dec_ref(v_pred_3263_);
v___x_3270_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3267_, v_a_3264_, v_a_3265_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3272_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3270_, 1);
v___x_3272_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3268_, v_a_3264_, v_a_3265_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3291_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3275_ = v___x_3272_;
v_isShared_3276_ = v_isSharedCheck_3291_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3272_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3291_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v_____do__lift_3278_; 
if (lean_obj_tag(v_c_u2083_x3f_3269_) == 1)
{
lean_object* v_val_3287_; lean_object* v___x_3288_; 
v_val_3287_ = lean_ctor_get(v_c_u2083_x3f_3269_, 0);
lean_inc(v_val_3287_);
lean_dec_ref_known(v_c_u2083_x3f_3269_, 1);
v___x_3288_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_val_3287_, v_a_3264_, v_a_3265_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3289_);
lean_dec_ref_known(v___x_3288_, 1);
v_____do__lift_3278_ = v_a_3289_;
goto v___jp_3277_;
}
else
{
lean_del_object(v___x_3275_);
lean_dec(v_a_3273_);
lean_dec(v_a_3271_);
return v___x_3288_;
}
}
else
{
lean_object* v___x_3290_; 
lean_dec(v_c_u2083_x3f_3269_);
v___x_3290_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4);
v_____do__lift_3278_ = v___x_3290_;
goto v___jp_3277_;
}
v___jp_3277_:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3285_; 
v___x_3279_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3280_, 0, v_a_3271_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
v___x_3281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
lean_ctor_set(v___x_3281_, 1, v_a_3273_);
v___x_3282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
lean_ctor_set(v___x_3282_, 1, v___x_3279_);
v___x_3283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
lean_ctor_set(v___x_3283_, 1, v_____do__lift_3278_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 0, v___x_3283_);
v___x_3285_ = v___x_3275_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3283_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
else
{
lean_dec(v_a_3271_);
lean_dec(v_c_u2083_x3f_3269_);
return v___x_3272_;
}
}
else
{
lean_dec(v_c_u2083_x3f_3269_);
lean_dec_ref(v_c_u2082_3268_);
return v___x_3270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___boxed(lean_object* v_pred_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_3292_, v_a_3293_, v_a_3294_);
lean_dec_ref(v_a_3294_);
lean_dec(v_a_3293_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(lean_object* v_pred_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_3297_, v_a_3298_, v_a_3306_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___boxed(lean_object* v_pred_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(v_pred_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(lean_object* v_h_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_){
_start:
{
switch(lean_obj_tag(v_h_3323_))
{
case 0:
{
lean_object* v_c_3327_; lean_object* v___x_3328_; 
v_c_3327_ = lean_ctor_get(v_h_3323_, 0);
lean_inc_ref(v_c_3327_);
lean_dec_ref_known(v_h_3323_, 1);
v___x_3328_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_3327_, v_a_3324_, v_a_3325_);
return v___x_3328_;
}
case 1:
{
lean_object* v_c_3329_; lean_object* v___x_3330_; 
v_c_3329_ = lean_ctor_get(v_h_3323_, 0);
lean_inc_ref(v_c_3329_);
lean_dec_ref_known(v_h_3323_, 1);
v___x_3330_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3329_, v_a_3324_, v_a_3325_);
return v___x_3330_;
}
case 2:
{
lean_object* v_c_3331_; lean_object* v___x_3332_; 
v_c_3331_ = lean_ctor_get(v_h_3323_, 0);
lean_inc_ref(v_c_3331_);
lean_dec_ref_known(v_h_3323_, 1);
v___x_3332_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_3331_, v_a_3324_, v_a_3325_);
return v___x_3332_;
}
case 3:
{
lean_object* v_c_3333_; lean_object* v___x_3334_; 
v_c_3333_ = lean_ctor_get(v_h_3323_, 0);
lean_inc_ref(v_c_3333_);
lean_dec_ref_known(v_h_3323_, 1);
v___x_3334_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_3333_, v_a_3324_, v_a_3325_);
return v___x_3334_;
}
default: 
{
lean_object* v_c_u2081_3335_; lean_object* v_c_u2082_3336_; lean_object* v_c_u2083_3337_; lean_object* v___x_3338_; 
v_c_u2081_3335_ = lean_ctor_get(v_h_3323_, 0);
lean_inc_ref(v_c_u2081_3335_);
v_c_u2082_3336_ = lean_ctor_get(v_h_3323_, 1);
lean_inc_ref(v_c_u2082_3336_);
v_c_u2083_3337_ = lean_ctor_get(v_h_3323_, 2);
lean_inc_ref(v_c_u2083_3337_);
lean_dec_ref_known(v_h_3323_, 3);
v___x_3338_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3335_, v_a_3324_, v_a_3325_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v___x_3340_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref_known(v___x_3338_, 1);
v___x_3340_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3336_, v_a_3324_, v_a_3325_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; lean_object* v___x_3342_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref_known(v___x_3340_, 1);
v___x_3342_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2083_3337_, v_a_3324_, v_a_3325_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3355_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3345_ = v___x_3342_;
v_isShared_3346_ = v_isSharedCheck_3355_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3355_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3353_; 
v___x_3347_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3348_, 0, v_a_3339_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
v___x_3349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
lean_ctor_set(v___x_3349_, 1, v_a_3341_);
v___x_3350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
lean_ctor_set(v___x_3350_, 1, v___x_3347_);
v___x_3351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
lean_ctor_set(v___x_3351_, 1, v_a_3343_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 0, v___x_3351_);
v___x_3353_ = v___x_3345_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
else
{
lean_dec(v_a_3341_);
lean_dec(v_a_3339_);
return v___x_3342_;
}
}
else
{
lean_dec(v_a_3339_);
lean_dec_ref(v_c_u2083_3337_);
return v___x_3340_;
}
}
else
{
lean_dec_ref(v_c_u2083_3337_);
lean_dec_ref(v_c_u2082_3336_);
return v___x_3338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg___boxed(lean_object* v_h_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3356_, v_a_3357_, v_a_3358_);
lean_dec_ref(v_a_3358_);
lean_dec(v_a_3357_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(lean_object* v_h_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v___x_3373_; 
v___x_3373_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3361_, v_a_3362_, v_a_3370_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___boxed(lean_object* v_h_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(v_h_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
lean_dec(v_a_3384_);
lean_dec_ref(v_a_3383_);
lean_dec(v_a_3382_);
lean_dec_ref(v_a_3381_);
lean_dec(v_a_3380_);
lean_dec_ref(v_a_3379_);
lean_dec(v_a_3378_);
lean_dec_ref(v_a_3377_);
lean_dec(v_a_3376_);
lean_dec(v_a_3375_);
return v_res_3386_;
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
