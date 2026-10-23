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
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object* v_c_1221_){
_start:
{
lean_object* v_p_1222_; 
v_p_1222_ = lean_ctor_get(v_c_1221_, 1);
if (lean_obj_tag(v_p_1222_) == 0)
{
lean_object* v_d_1223_; lean_object* v_k_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; 
v_d_1223_ = lean_ctor_get(v_c_1221_, 0);
v_k_1224_ = lean_ctor_get(v_p_1222_, 0);
v___x_1225_ = lean_int_emod(v_k_1224_, v_d_1223_);
v___x_1226_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1227_ = lean_int_dec_eq(v___x_1225_, v___x_1226_);
lean_dec(v___x_1225_);
return v___x_1227_;
}
else
{
lean_object* v_d_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v_d_1228_ = lean_ctor_get(v_c_1221_, 0);
v___x_1229_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_1230_ = lean_int_dec_eq(v_d_1228_, v___x_1229_);
return v___x_1230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial___boxed(lean_object* v_c_1231_){
_start:
{
uint8_t v_res_1232_; lean_object* v_r_1233_; 
v_res_1232_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_c_1231_);
lean_dec_ref(v_c_1231_);
v_r_1233_ = lean_box(v_res_1232_);
return v_r_1233_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0));
v___x_1236_ = l_Lean_stringToMessageData(v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object* v_c_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v_d_1241_; lean_object* v_p_1242_; lean_object* v___x_1243_; 
v_d_1241_ = lean_ctor_get(v_c_1237_, 0);
lean_inc(v_d_1241_);
v_p_1242_ = lean_ctor_get(v_c_1237_, 1);
lean_inc_ref(v_p_1242_);
lean_dec_ref(v_c_1237_);
v___x_1243_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1242_, v_a_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1257_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1257_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1257_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1248_ = l_Int_repr(v_d_1241_);
lean_dec(v_d_1241_);
v___x_1249_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
v___x_1250_ = l_Lean_MessageData_ofFormat(v___x_1249_);
v___x_1251_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1);
v___x_1252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v_a_1244_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1253_);
v___x_1255_ = v___x_1246_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
else
{
lean_dec(v_d_1241_);
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___boxed(lean_object* v_c_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1258_, v_a_1259_, v_a_1260_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(lean_object* v_c_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1263_, v_a_1264_, v_a_1272_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___boxed(lean_object* v_c_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(v_c_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec(v_a_1277_);
return v_res_1288_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_unsigned_to_nat(0u);
v___x_1295_ = l_Lean_Level_ofNat(v___x_1294_);
return v___x_1295_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_box(0);
v___x_1297_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3);
v___x_1298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
lean_ctor_set(v___x_1298_, 1, v___x_1296_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4);
v___x_1300_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2));
v___x_1301_ = l_Lean_Expr_const___override(v___x_1300_, v___x_1299_);
return v___x_1301_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = lean_box(0);
v___x_1306_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7));
v___x_1307_ = l_Lean_Expr_const___override(v___x_1306_, v___x_1305_);
return v___x_1307_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = lean_box(0);
v___x_1313_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10));
v___x_1314_ = l_Lean_Expr_const___override(v___x_1313_, v___x_1312_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(lean_object* v_c_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_d_1319_; lean_object* v_p_1320_; lean_object* v___x_1321_; 
v_d_1319_ = lean_ctor_get(v_c_1315_, 0);
lean_inc(v_d_1319_);
v_p_1320_ = lean_ctor_get(v_c_1315_, 1);
lean_inc_ref(v_p_1320_);
lean_dec_ref(v_c_1315_);
v___x_1321_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1320_, v_a_1316_, v_a_1317_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1343_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1343_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1343_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___y_1327_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1333_ = lean_int_dec_le(v___x_1332_, v_d_1319_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1334_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5);
v___x_1335_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8);
v___x_1336_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11);
v___x_1337_ = lean_int_neg(v_d_1319_);
lean_dec(v_d_1319_);
v___x_1338_ = l_Int_toNat(v___x_1337_);
lean_dec(v___x_1337_);
v___x_1339_ = l_Lean_instToExprInt_mkNat(v___x_1338_);
v___x_1340_ = l_Lean_mkApp3(v___x_1334_, v___x_1335_, v___x_1336_, v___x_1339_);
v___y_1327_ = v___x_1340_;
goto v___jp_1326_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = l_Int_toNat(v_d_1319_);
lean_dec(v_d_1319_);
v___x_1342_ = l_Lean_instToExprInt_mkNat(v___x_1341_);
v___y_1327_ = v___x_1342_;
goto v___jp_1326_;
}
v___jp_1326_:
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1328_ = l_Lean_mkIntDvd(v___y_1327_, v_a_1322_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1328_);
v___x_1330_ = v___x_1324_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
lean_dec(v_d_1319_);
return v___x_1321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1344_, v_a_1345_, v_a_1346_);
lean_dec_ref(v_a_1346_);
lean_dec(v_a_1345_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(lean_object* v_c_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1349_, v_a_1350_, v_a_1358_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___boxed(lean_object* v_c_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(v_c_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec(v_a_1363_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(lean_object* v_msgData_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; lean_object* v_env_1382_; uint8_t v___x_1383_; lean_object* v_env_1384_; lean_object* v___x_1385_; lean_object* v_toCold_1386_; lean_object* v_mctx_1387_; lean_object* v_lctx_1388_; lean_object* v_options_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1381_ = lean_st_ref_get(v___y_1379_);
v_env_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc_ref(v_env_1382_);
lean_dec(v___x_1381_);
v___x_1383_ = 0;
v_env_1384_ = l_Lean_Environment_setRecordingDeps(v_env_1382_, v___x_1383_);
v___x_1385_ = lean_st_ref_get(v___y_1377_);
v_toCold_1386_ = lean_ctor_get(v___y_1378_, 0);
v_mctx_1387_ = lean_ctor_get(v___x_1385_, 0);
lean_inc_ref(v_mctx_1387_);
lean_dec(v___x_1385_);
v_lctx_1388_ = lean_ctor_get(v___y_1376_, 2);
v_options_1389_ = lean_ctor_get(v_toCold_1386_, 2);
lean_inc_ref(v_options_1389_);
lean_inc_ref(v_lctx_1388_);
v___x_1390_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1390_, 0, v_env_1384_);
lean_ctor_set(v___x_1390_, 1, v_mctx_1387_);
lean_ctor_set(v___x_1390_, 2, v_lctx_1388_);
lean_ctor_set(v___x_1390_, 3, v_options_1389_);
v___x_1391_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set(v___x_1391_, 1, v_msgData_1375_);
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object* v_msgData_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msgData_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(lean_object* v_msg_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_ref_1406_; lean_object* v___x_1407_; lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1416_; 
v_ref_1406_ = lean_ctor_get(v___y_1403_, 2);
v___x_1407_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msg_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1416_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1416_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
lean_inc(v_ref_1406_);
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v_ref_1406_);
lean_ctor_set(v___x_1412_, 1, v_a_1408_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set_tag(v___x_1410_, 1);
lean_ctor_set(v___x_1410_, 0, v___x_1412_);
v___x_1414_ = v___x_1410_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg___boxed(lean_object* v_msg_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
return v_res_1423_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0));
v___x_1426_ = l_Lean_stringToMessageData(v___x_1425_);
return v___x_1426_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2));
v___x_1429_ = l_Lean_stringToMessageData(v___x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object* v_c_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1430_, v_a_1431_, v_a_1439_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
lean_dec_ref_known(v___x_1442_, 1);
v___x_1444_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1445_ = l_Lean_indentD(v_a_1443_);
v___x_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1444_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3);
v___x_1448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1446_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
v___x_1449_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1448_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
return v___x_1449_;
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
v_a_1450_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1442_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1442_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec(v_a_1459_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(lean_object* v_00_u03b1_1471_, lean_object* v_c_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1485_, lean_object* v_c_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(v_00_u03b1_1485_, v_c_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec(v_a_1487_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(lean_object* v_00_u03b1_1499_, lean_object* v_msg_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1500_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___boxed(lean_object* v_00_u03b1_1513_, lean_object* v_msg_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(v_00_u03b1_1513_, v_msg_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec(v___y_1515_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial_spec__0(lean_object* v_a_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_nat_to_int(v_a_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(lean_object* v_c_1529_){
_start:
{
lean_object* v_p_1530_; 
v_p_1530_ = lean_ctor_get(v_c_1529_, 0);
if (lean_obj_tag(v_p_1530_) == 0)
{
lean_object* v_k_1531_; lean_object* v___x_1532_; uint8_t v___x_1533_; 
v_k_1531_ = lean_ctor_get(v_p_1530_, 0);
v___x_1532_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1533_ = lean_int_dec_eq(v_k_1531_, v___x_1532_);
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
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1536_ = l_Int_Internal_Linear_Poly_getConst(v_p_1530_);
v___x_1537_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v_p_1530_);
v___x_1538_ = lean_nat_to_int(v___x_1537_);
v___x_1539_ = lean_int_emod(v___x_1536_, v___x_1538_);
lean_dec(v___x_1538_);
lean_dec(v___x_1536_);
v___x_1540_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1541_ = lean_int_dec_eq(v___x_1539_, v___x_1540_);
lean_dec(v___x_1539_);
if (v___x_1541_ == 0)
{
uint8_t v___x_1542_; 
v___x_1542_ = 1;
return v___x_1542_;
}
else
{
uint8_t v___x_1543_; 
v___x_1543_ = 0;
return v___x_1543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial___boxed(lean_object* v_c_1544_){
_start:
{
uint8_t v_res_1545_; lean_object* v_r_1546_; 
v_res_1545_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(v_c_1544_);
lean_dec_ref(v_c_1544_);
v_r_1546_ = lean_box(v_res_1545_);
return v_r_1546_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0));
v___x_1549_ = l_Lean_stringToMessageData(v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(lean_object* v_c_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_){
_start:
{
lean_object* v_p_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1571_; 
v_p_1554_ = lean_ctor_get(v_c_1550_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_c_1550_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; 
v_unused_1572_ = lean_ctor_get(v_c_1550_, 1);
lean_dec(v_unused_1572_);
v___x_1556_ = v_c_1550_;
v_isShared_1557_ = v_isSharedCheck_1571_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_p_1554_);
lean_dec(v_c_1550_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1571_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1554_, v_a_1551_, v_a_1552_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1570_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1570_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1570_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1563_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1);
if (v_isShared_1557_ == 0)
{
lean_ctor_set_tag(v___x_1556_, 7);
lean_ctor_set(v___x_1556_, 1, v___x_1563_);
lean_ctor_set(v___x_1556_, 0, v_a_1559_);
v___x_1565_ = v___x_1556_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1559_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1567_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1565_);
v___x_1567_ = v___x_1561_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
else
{
lean_del_object(v___x_1556_);
return v___x_1558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___boxed(lean_object* v_c_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1573_, v_a_1574_, v_a_1575_);
lean_dec_ref(v_a_1575_);
lean_dec(v_a_1574_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(lean_object* v_c_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1578_, v_a_1579_, v_a_1587_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___boxed(lean_object* v_c_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(v_c_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(lean_object* v_c_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1604_, v_a_1605_, v_a_1608_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1611_, 1);
v___x_1613_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1614_ = l_Lean_indentD(v_a_1612_);
v___x_1615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1615_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_);
return v___x_1616_;
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
v_a_1617_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1611_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1611_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(lean_object* v_00_u03b1_1633_, lean_object* v_c_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1634_, v_a_1635_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1647_, lean_object* v_c_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(v_00_u03b1_1647_, v_c_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec(v_a_1649_);
return v_res_1660_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0(void){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1662_ = l_Lean_mkIntLit(v___x_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(lean_object* v_c_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_p_1667_; lean_object* v___x_1668_; 
v_p_1667_ = lean_ctor_get(v_c_1663_, 0);
lean_inc_ref(v_p_1667_);
lean_dec_ref(v_c_1663_);
v___x_1668_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1667_, v_a_1664_, v_a_1665_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1679_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1679_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1679_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1673_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1674_ = l_Lean_mkIntEq(v_a_1669_, v___x_1673_);
v___x_1675_ = l_Lean_mkNot(v___x_1674_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1675_);
v___x_1677_ = v___x_1671_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
else
{
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1680_, v_a_1681_, v_a_1682_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(lean_object* v_c_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1685_, v_a_1686_, v_a_1694_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___boxed(lean_object* v_c_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(v_c_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_);
lean_dec(v_a_1708_);
lean_dec_ref(v_a_1707_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec(v_a_1699_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert___boxed(lean_object* v_c_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_00___x40___internal___hyg_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = lean_grind_cutsat_assert_le(v_c_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
return v_res_1735_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(lean_object* v_c_1736_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial___boxed(lean_object* v_c_1742_){
_start:
{
uint8_t v_res_1743_; lean_object* v_r_1744_; 
v_res_1743_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_c_1742_);
lean_dec_ref(v_c_1742_);
v_r_1744_ = lean_box(v_res_1743_);
return v_r_1744_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1746_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0));
v___x_1747_ = l_Lean_stringToMessageData(v___x_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(lean_object* v_c_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v_p_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1769_; 
v_p_1752_ = lean_ctor_get(v_c_1748_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_c_1748_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v_c_1748_, 1);
lean_dec(v_unused_1770_);
v___x_1754_ = v_c_1748_;
v_isShared_1755_ = v_isSharedCheck_1769_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_p_1752_);
lean_dec(v_c_1748_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1769_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1752_, v_a_1749_, v_a_1750_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1768_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1768_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1768_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1761_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1);
if (v_isShared_1755_ == 0)
{
lean_ctor_set_tag(v___x_1754_, 7);
lean_ctor_set(v___x_1754_, 1, v___x_1761_);
lean_ctor_set(v___x_1754_, 0, v_a_1757_);
v___x_1763_ = v___x_1754_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1757_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
lean_object* v___x_1765_; 
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1763_);
v___x_1765_ = v___x_1759_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
else
{
lean_del_object(v___x_1754_);
return v___x_1756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___boxed(lean_object* v_c_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1771_, v_a_1772_, v_a_1773_);
lean_dec_ref(v_a_1773_);
lean_dec(v_a_1772_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(lean_object* v_c_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1776_, v_a_1777_, v_a_1785_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___boxed(lean_object* v_c_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(v_c_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec(v_a_1790_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(lean_object* v_c_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v_p_1806_; lean_object* v___x_1807_; 
v_p_1806_ = lean_ctor_get(v_c_1802_, 0);
lean_inc_ref(v_p_1806_);
lean_dec_ref(v_c_1802_);
v___x_1807_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1806_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1817_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1817_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1817_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1812_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1813_ = l_Lean_mkIntLE(v_a_1808_, v___x_1812_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v___x_1813_);
v___x_1815_ = v___x_1810_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
else
{
return v___x_1807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1818_, v_a_1819_, v_a_1820_);
lean_dec_ref(v_a_1820_);
lean_dec(v_a_1819_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(lean_object* v_c_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1823_, v_a_1824_, v_a_1832_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___boxed(lean_object* v_c_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(v_c_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(lean_object* v_c_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1849_, v_a_1850_, v_a_1853_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref_known(v___x_1856_, 1);
v___x_1858_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1859_ = l_Lean_indentD(v_a_1857_);
v___x_1860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1858_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1860_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
return v___x_1861_;
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
v_a_1862_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1856_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1856_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(lean_object* v_00_u03b1_1878_, lean_object* v_c_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1879_, v_a_1880_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1892_, lean_object* v_c_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(v_00_u03b1_1892_, v_c_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec(v_a_1894_);
return v_res_1905_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(lean_object* v_c_1906_){
_start:
{
lean_object* v_p_1907_; 
v_p_1907_ = lean_ctor_get(v_c_1906_, 0);
if (lean_obj_tag(v_p_1907_) == 0)
{
lean_object* v_k_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; 
v_k_1908_ = lean_ctor_get(v_p_1907_, 0);
v___x_1909_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1910_ = lean_int_dec_eq(v_k_1908_, v___x_1909_);
return v___x_1910_;
}
else
{
uint8_t v___x_1911_; 
v___x_1911_ = 0;
return v___x_1911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial___boxed(lean_object* v_c_1912_){
_start:
{
uint8_t v_res_1913_; lean_object* v_r_1914_; 
v_res_1913_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(v_c_1912_);
lean_dec_ref(v_c_1912_);
v_r_1914_ = lean_box(v_res_1913_);
return v_r_1914_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0));
v___x_1917_ = l_Lean_stringToMessageData(v___x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object* v_c_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_){
_start:
{
lean_object* v_p_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1939_; 
v_p_1922_ = lean_ctor_get(v_c_1918_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_c_1918_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v_c_1918_, 1);
lean_dec(v_unused_1940_);
v___x_1924_ = v_c_1918_;
v_isShared_1925_ = v_isSharedCheck_1939_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_p_1922_);
lean_dec(v_c_1918_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1939_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1922_, v_a_1919_, v_a_1920_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1938_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1929_ = v___x_1926_;
v_isShared_1930_ = v_isSharedCheck_1938_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1926_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1938_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1931_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1);
if (v_isShared_1925_ == 0)
{
lean_ctor_set_tag(v___x_1924_, 7);
lean_ctor_set(v___x_1924_, 1, v___x_1931_);
lean_ctor_set(v___x_1924_, 0, v_a_1927_);
v___x_1933_ = v___x_1924_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1927_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1935_; 
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 0, v___x_1933_);
v___x_1935_ = v___x_1929_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_del_object(v___x_1924_);
return v___x_1926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___boxed(lean_object* v_c_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1941_, v_a_1942_, v_a_1943_);
lean_dec_ref(v_a_1943_);
lean_dec(v_a_1942_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(lean_object* v_c_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1946_, v_a_1947_, v_a_1955_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___boxed(lean_object* v_c_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(v_c_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec(v_a_1960_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(lean_object* v_c_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v_p_1976_; lean_object* v___x_1977_; 
v_p_1976_ = lean_ctor_get(v_c_1972_, 0);
lean_inc_ref(v_p_1976_);
lean_dec_ref(v_c_1972_);
v___x_1977_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1976_, v_a_1973_, v_a_1974_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1987_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1987_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1987_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1982_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1983_ = l_Lean_mkIntEq(v_a_1978_, v___x_1982_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1983_);
v___x_1985_ = v___x_1980_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
else
{
return v___x_1977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1988_, v_a_1989_, v_a_1990_);
lean_dec_ref(v_a_1990_);
lean_dec(v_a_1989_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(lean_object* v_c_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1993_, v_a_1994_, v_a_2002_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___boxed(lean_object* v_c_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(v_c_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(lean_object* v_c_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_2019_, v_a_2020_, v_a_2023_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
v___x_2028_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_2029_ = l_Lean_indentD(v_a_2027_);
v___x_2030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2028_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2030_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
return v___x_2031_;
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
v_a_2032_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2026_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2026_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
lean_dec(v_a_2043_);
lean_dec_ref(v_a_2042_);
lean_dec(v_a_2041_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(lean_object* v_00_u03b1_2048_, lean_object* v_c_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_2049_, v_a_2050_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_2062_, lean_object* v_c_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(v_00_u03b1_2062_, v_c_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec(v_a_2065_);
lean_dec(v_a_2064_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(lean_object* v_x_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2097_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2097_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2097_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v_occurs_2085_; lean_object* v_size_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
v_occurs_2085_ = lean_ctor_get(v_a_2081_, 11);
lean_inc_ref(v_occurs_2085_);
lean_dec(v_a_2081_);
v_size_2086_ = lean_ctor_get(v_occurs_2085_, 2);
v___x_2087_ = lean_box(1);
v___x_2088_ = lean_nat_dec_lt(v_x_2076_, v_size_2086_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
lean_dec_ref(v_occurs_2085_);
v___x_2089_ = l_outOfBounds___redArg(v___x_2087_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2089_);
v___x_2091_ = v___x_2083_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
else
{
lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2093_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2087_, v_occurs_2085_, v_x_2076_);
lean_dec_ref(v_occurs_2085_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2093_);
v___x_2095_ = v___x_2083_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
v_a_2098_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2080_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2080_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg___boxed(lean_object* v_x_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2106_, v_a_2107_, v_a_2108_);
lean_dec_ref(v_a_2108_);
lean_dec(v_a_2107_);
lean_dec(v_x_2106_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(lean_object* v_x_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2111_, v_a_2112_, v_a_2120_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___boxed(lean_object* v_x_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(v_x_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
lean_dec(v_a_2128_);
lean_dec_ref(v_a_2127_);
lean_dec(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec(v_x_2124_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(lean_object* v_k_2137_, lean_object* v_v_2138_, lean_object* v_t_2139_){
_start:
{
if (lean_obj_tag(v_t_2139_) == 0)
{
lean_object* v_size_2140_; lean_object* v_k_2141_; lean_object* v_v_2142_; lean_object* v_l_2143_; lean_object* v_r_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2425_; 
v_size_2140_ = lean_ctor_get(v_t_2139_, 0);
v_k_2141_ = lean_ctor_get(v_t_2139_, 1);
v_v_2142_ = lean_ctor_get(v_t_2139_, 2);
v_l_2143_ = lean_ctor_get(v_t_2139_, 3);
v_r_2144_ = lean_ctor_get(v_t_2139_, 4);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_t_2139_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2146_ = v_t_2139_;
v_isShared_2147_ = v_isSharedCheck_2425_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_r_2144_);
lean_inc(v_l_2143_);
lean_inc(v_v_2142_);
lean_inc(v_k_2141_);
lean_inc(v_size_2140_);
lean_dec(v_t_2139_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2425_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
uint8_t v___x_2148_; 
v___x_2148_ = lean_nat_dec_lt(v_k_2137_, v_k_2141_);
if (v___x_2148_ == 0)
{
uint8_t v___x_2149_; 
v___x_2149_ = lean_nat_dec_eq(v_k_2137_, v_k_2141_);
if (v___x_2149_ == 0)
{
lean_object* v_impl_2150_; lean_object* v___x_2151_; 
lean_dec(v_size_2140_);
v_impl_2150_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2137_, v_v_2138_, v_r_2144_);
v___x_2151_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2143_) == 0)
{
lean_object* v_size_2152_; lean_object* v_size_2153_; lean_object* v_k_2154_; lean_object* v_v_2155_; lean_object* v_l_2156_; lean_object* v_r_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
v_size_2152_ = lean_ctor_get(v_l_2143_, 0);
v_size_2153_ = lean_ctor_get(v_impl_2150_, 0);
v_k_2154_ = lean_ctor_get(v_impl_2150_, 1);
v_v_2155_ = lean_ctor_get(v_impl_2150_, 2);
v_l_2156_ = lean_ctor_get(v_impl_2150_, 3);
lean_inc(v_l_2156_);
v_r_2157_ = lean_ctor_get(v_impl_2150_, 4);
v___x_2158_ = lean_unsigned_to_nat(3u);
v___x_2159_ = lean_nat_mul(v___x_2158_, v_size_2152_);
v___x_2160_ = lean_nat_dec_lt(v___x_2159_, v_size_2153_);
lean_dec(v___x_2159_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2164_; 
lean_dec(v_l_2156_);
v___x_2161_ = lean_nat_add(v___x_2151_, v_size_2152_);
v___x_2162_ = lean_nat_add(v___x_2161_, v_size_2153_);
lean_dec(v___x_2161_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 4, v_impl_2150_);
lean_ctor_set(v___x_2146_, 0, v___x_2162_);
v___x_2164_ = v___x_2146_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_k_2141_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v_v_2142_);
lean_ctor_set(v_reuseFailAlloc_2165_, 3, v_l_2143_);
lean_ctor_set(v_reuseFailAlloc_2165_, 4, v_impl_2150_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
else
{
lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2229_; 
lean_inc(v_r_2157_);
lean_inc(v_v_2155_);
lean_inc(v_k_2154_);
lean_inc(v_size_2153_);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_impl_2150_);
if (v_isSharedCheck_2229_ == 0)
{
lean_object* v_unused_2230_; lean_object* v_unused_2231_; lean_object* v_unused_2232_; lean_object* v_unused_2233_; lean_object* v_unused_2234_; 
v_unused_2230_ = lean_ctor_get(v_impl_2150_, 4);
lean_dec(v_unused_2230_);
v_unused_2231_ = lean_ctor_get(v_impl_2150_, 3);
lean_dec(v_unused_2231_);
v_unused_2232_ = lean_ctor_get(v_impl_2150_, 2);
lean_dec(v_unused_2232_);
v_unused_2233_ = lean_ctor_get(v_impl_2150_, 1);
lean_dec(v_unused_2233_);
v_unused_2234_ = lean_ctor_get(v_impl_2150_, 0);
lean_dec(v_unused_2234_);
v___x_2167_ = v_impl_2150_;
v_isShared_2168_ = v_isSharedCheck_2229_;
goto v_resetjp_2166_;
}
else
{
lean_dec(v_impl_2150_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2229_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v_size_2169_; lean_object* v_k_2170_; lean_object* v_v_2171_; lean_object* v_l_2172_; lean_object* v_r_2173_; lean_object* v_size_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v_size_2169_ = lean_ctor_get(v_l_2156_, 0);
v_k_2170_ = lean_ctor_get(v_l_2156_, 1);
v_v_2171_ = lean_ctor_get(v_l_2156_, 2);
v_l_2172_ = lean_ctor_get(v_l_2156_, 3);
v_r_2173_ = lean_ctor_get(v_l_2156_, 4);
v_size_2174_ = lean_ctor_get(v_r_2157_, 0);
v___x_2175_ = lean_unsigned_to_nat(2u);
v___x_2176_ = lean_nat_mul(v___x_2175_, v_size_2174_);
v___x_2177_ = lean_nat_dec_lt(v_size_2169_, v___x_2176_);
lean_dec(v___x_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2205_; 
lean_inc(v_r_2173_);
lean_inc(v_l_2172_);
lean_inc(v_v_2171_);
lean_inc(v_k_2170_);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_l_2156_);
if (v_isSharedCheck_2205_ == 0)
{
lean_object* v_unused_2206_; lean_object* v_unused_2207_; lean_object* v_unused_2208_; lean_object* v_unused_2209_; lean_object* v_unused_2210_; 
v_unused_2206_ = lean_ctor_get(v_l_2156_, 4);
lean_dec(v_unused_2206_);
v_unused_2207_ = lean_ctor_get(v_l_2156_, 3);
lean_dec(v_unused_2207_);
v_unused_2208_ = lean_ctor_get(v_l_2156_, 2);
lean_dec(v_unused_2208_);
v_unused_2209_ = lean_ctor_get(v_l_2156_, 1);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v_l_2156_, 0);
lean_dec(v_unused_2210_);
v___x_2179_ = v_l_2156_;
v_isShared_2180_ = v_isSharedCheck_2205_;
goto v_resetjp_2178_;
}
else
{
lean_dec(v_l_2156_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2205_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2195_; 
v___x_2181_ = lean_nat_add(v___x_2151_, v_size_2152_);
v___x_2182_ = lean_nat_add(v___x_2181_, v_size_2153_);
lean_dec(v_size_2153_);
if (lean_obj_tag(v_l_2172_) == 0)
{
lean_object* v_size_2203_; 
v_size_2203_ = lean_ctor_get(v_l_2172_, 0);
lean_inc(v_size_2203_);
v___y_2195_ = v_size_2203_;
goto v___jp_2194_;
}
else
{
lean_object* v___x_2204_; 
v___x_2204_ = lean_unsigned_to_nat(0u);
v___y_2195_ = v___x_2204_;
goto v___jp_2194_;
}
v___jp_2183_:
{
lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2187_ = lean_nat_add(v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec(v___y_2185_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 4, v_r_2157_);
lean_ctor_set(v___x_2179_, 3, v_r_2173_);
lean_ctor_set(v___x_2179_, 2, v_v_2155_);
lean_ctor_set(v___x_2179_, 1, v_k_2154_);
lean_ctor_set(v___x_2179_, 0, v___x_2187_);
v___x_2189_ = v___x_2179_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2187_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_k_2154_);
lean_ctor_set(v_reuseFailAlloc_2193_, 2, v_v_2155_);
lean_ctor_set(v_reuseFailAlloc_2193_, 3, v_r_2173_);
lean_ctor_set(v_reuseFailAlloc_2193_, 4, v_r_2157_);
v___x_2189_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2191_; 
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 4, v___x_2189_);
lean_ctor_set(v___x_2167_, 3, v___y_2184_);
lean_ctor_set(v___x_2167_, 2, v_v_2171_);
lean_ctor_set(v___x_2167_, 1, v_k_2170_);
lean_ctor_set(v___x_2167_, 0, v___x_2182_);
v___x_2191_ = v___x_2167_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_k_2170_);
lean_ctor_set(v_reuseFailAlloc_2192_, 2, v_v_2171_);
lean_ctor_set(v_reuseFailAlloc_2192_, 3, v___y_2184_);
lean_ctor_set(v_reuseFailAlloc_2192_, 4, v___x_2189_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
v___jp_2194_:
{
lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2196_ = lean_nat_add(v___x_2181_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec(v___x_2181_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 4, v_l_2172_);
lean_ctor_set(v___x_2146_, 0, v___x_2196_);
v___x_2198_ = v___x_2146_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_k_2141_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_v_2142_);
lean_ctor_set(v_reuseFailAlloc_2202_, 3, v_l_2143_);
lean_ctor_set(v_reuseFailAlloc_2202_, 4, v_l_2172_);
v___x_2198_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; 
v___x_2199_ = lean_nat_add(v___x_2151_, v_size_2174_);
if (lean_obj_tag(v_r_2173_) == 0)
{
lean_object* v_size_2200_; 
v_size_2200_ = lean_ctor_get(v_r_2173_, 0);
lean_inc(v_size_2200_);
v___y_2184_ = v___x_2198_;
v___y_2185_ = v___x_2199_;
v___y_2186_ = v_size_2200_;
goto v___jp_2183_;
}
else
{
lean_object* v___x_2201_; 
v___x_2201_ = lean_unsigned_to_nat(0u);
v___y_2184_ = v___x_2198_;
v___y_2185_ = v___x_2199_;
v___y_2186_ = v___x_2201_;
goto v___jp_2183_;
}
}
}
}
}
else
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2215_; 
lean_del_object(v___x_2146_);
v___x_2211_ = lean_nat_add(v___x_2151_, v_size_2152_);
v___x_2212_ = lean_nat_add(v___x_2211_, v_size_2153_);
lean_dec(v_size_2153_);
v___x_2213_ = lean_nat_add(v___x_2211_, v_size_2169_);
lean_dec(v___x_2211_);
lean_inc_ref(v_l_2143_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 4, v_l_2156_);
lean_ctor_set(v___x_2167_, 3, v_l_2143_);
lean_ctor_set(v___x_2167_, 2, v_v_2142_);
lean_ctor_set(v___x_2167_, 1, v_k_2141_);
lean_ctor_set(v___x_2167_, 0, v___x_2213_);
v___x_2215_ = v___x_2167_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_k_2141_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v_v_2142_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v_l_2143_);
lean_ctor_set(v_reuseFailAlloc_2228_, 4, v_l_2156_);
v___x_2215_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
v_isSharedCheck_2222_ = !lean_is_exclusive(v_l_2143_);
if (v_isSharedCheck_2222_ == 0)
{
lean_object* v_unused_2223_; lean_object* v_unused_2224_; lean_object* v_unused_2225_; lean_object* v_unused_2226_; lean_object* v_unused_2227_; 
v_unused_2223_ = lean_ctor_get(v_l_2143_, 4);
lean_dec(v_unused_2223_);
v_unused_2224_ = lean_ctor_get(v_l_2143_, 3);
lean_dec(v_unused_2224_);
v_unused_2225_ = lean_ctor_get(v_l_2143_, 2);
lean_dec(v_unused_2225_);
v_unused_2226_ = lean_ctor_get(v_l_2143_, 1);
lean_dec(v_unused_2226_);
v_unused_2227_ = lean_ctor_get(v_l_2143_, 0);
lean_dec(v_unused_2227_);
v___x_2217_ = v_l_2143_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_dec(v_l_2143_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 4, v_r_2157_);
lean_ctor_set(v___x_2217_, 3, v___x_2215_);
lean_ctor_set(v___x_2217_, 2, v_v_2155_);
lean_ctor_set(v___x_2217_, 1, v_k_2154_);
lean_ctor_set(v___x_2217_, 0, v___x_2212_);
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v_k_2154_);
lean_ctor_set(v_reuseFailAlloc_2221_, 2, v_v_2155_);
lean_ctor_set(v_reuseFailAlloc_2221_, 3, v___x_2215_);
lean_ctor_set(v_reuseFailAlloc_2221_, 4, v_r_2157_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2235_; 
v_l_2235_ = lean_ctor_get(v_impl_2150_, 3);
lean_inc(v_l_2235_);
if (lean_obj_tag(v_l_2235_) == 0)
{
lean_object* v_r_2236_; lean_object* v_k_2237_; lean_object* v_v_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2261_; 
v_r_2236_ = lean_ctor_get(v_impl_2150_, 4);
v_k_2237_ = lean_ctor_get(v_impl_2150_, 1);
v_v_2238_ = lean_ctor_get(v_impl_2150_, 2);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_impl_2150_);
if (v_isSharedCheck_2261_ == 0)
{
lean_object* v_unused_2262_; lean_object* v_unused_2263_; 
v_unused_2262_ = lean_ctor_get(v_impl_2150_, 3);
lean_dec(v_unused_2262_);
v_unused_2263_ = lean_ctor_get(v_impl_2150_, 0);
lean_dec(v_unused_2263_);
v___x_2240_ = v_impl_2150_;
v_isShared_2241_ = v_isSharedCheck_2261_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_r_2236_);
lean_inc(v_v_2238_);
lean_inc(v_k_2237_);
lean_dec(v_impl_2150_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2261_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v_k_2242_; lean_object* v_v_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2257_; 
v_k_2242_ = lean_ctor_get(v_l_2235_, 1);
v_v_2243_ = lean_ctor_get(v_l_2235_, 2);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_l_2235_);
if (v_isSharedCheck_2257_ == 0)
{
lean_object* v_unused_2258_; lean_object* v_unused_2259_; lean_object* v_unused_2260_; 
v_unused_2258_ = lean_ctor_get(v_l_2235_, 4);
lean_dec(v_unused_2258_);
v_unused_2259_ = lean_ctor_get(v_l_2235_, 3);
lean_dec(v_unused_2259_);
v_unused_2260_ = lean_ctor_get(v_l_2235_, 0);
lean_dec(v_unused_2260_);
v___x_2245_ = v_l_2235_;
v_isShared_2246_ = v_isSharedCheck_2257_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_v_2243_);
lean_inc(v_k_2242_);
lean_dec(v_l_2235_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2257_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; lean_object* v___x_2249_; 
v___x_2247_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2236_, 2);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 4, v_r_2236_);
lean_ctor_set(v___x_2245_, 3, v_r_2236_);
lean_ctor_set(v___x_2245_, 2, v_v_2142_);
lean_ctor_set(v___x_2245_, 1, v_k_2141_);
lean_ctor_set(v___x_2245_, 0, v___x_2151_);
v___x_2249_ = v___x_2245_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_k_2141_);
lean_ctor_set(v_reuseFailAlloc_2256_, 2, v_v_2142_);
lean_ctor_set(v_reuseFailAlloc_2256_, 3, v_r_2236_);
lean_ctor_set(v_reuseFailAlloc_2256_, 4, v_r_2236_);
v___x_2249_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2251_; 
lean_inc(v_r_2236_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 3, v_r_2236_);
lean_ctor_set(v___x_2240_, 0, v___x_2151_);
v___x_2251_ = v___x_2240_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_k_2237_);
lean_ctor_set(v_reuseFailAlloc_2255_, 2, v_v_2238_);
lean_ctor_set(v_reuseFailAlloc_2255_, 3, v_r_2236_);
lean_ctor_set(v_reuseFailAlloc_2255_, 4, v_r_2236_);
v___x_2251_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2253_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 4, v___x_2251_);
lean_ctor_set(v___x_2146_, 3, v___x_2249_);
lean_ctor_set(v___x_2146_, 2, v_v_2243_);
lean_ctor_set(v___x_2146_, 1, v_k_2242_);
lean_ctor_set(v___x_2146_, 0, v___x_2247_);
v___x_2253_ = v___x_2146_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2247_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_k_2242_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_v_2243_);
lean_ctor_set(v_reuseFailAlloc_2254_, 3, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2254_, 4, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
}
}
else
{
lean_object* v_r_2264_; 
v_r_2264_ = lean_ctor_get(v_impl_2150_, 4);
lean_inc(v_r_2264_);
if (lean_obj_tag(v_r_2264_) == 0)
{
lean_object* v_k_2265_; lean_object* v_v_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2277_; 
v_k_2265_ = lean_ctor_get(v_impl_2150_, 1);
v_v_2266_ = lean_ctor_get(v_impl_2150_, 2);
v_isSharedCheck_2277_ = !lean_is_exclusive(v_impl_2150_);
if (v_isSharedCheck_2277_ == 0)
{
lean_object* v_unused_2278_; lean_object* v_unused_2279_; lean_object* v_unused_2280_; 
v_unused_2278_ = lean_ctor_get(v_impl_2150_, 4);
lean_dec(v_unused_2278_);
v_unused_2279_ = lean_ctor_get(v_impl_2150_, 3);
lean_dec(v_unused_2279_);
v_unused_2280_ = lean_ctor_get(v_impl_2150_, 0);
lean_dec(v_unused_2280_);
v___x_2268_ = v_impl_2150_;
v_isShared_2269_ = v_isSharedCheck_2277_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_v_2266_);
lean_inc(v_k_2265_);
lean_dec(v_impl_2150_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2277_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v___x_2272_; 
v___x_2270_ = lean_unsigned_to_nat(3u);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 4, v_l_2235_);
lean_ctor_set(v___x_2268_, 2, v_v_2142_);
lean_ctor_set(v___x_2268_, 1, v_k_2141_);
lean_ctor_set(v___x_2268_, 0, v___x_2151_);
v___x_2272_ = v___x_2268_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_k_2141_);
lean_ctor_set(v_reuseFailAlloc_2276_, 2, v_v_2142_);
lean_ctor_set(v_reuseFailAlloc_2276_, 3, v_l_2235_);
lean_ctor_set(v_reuseFailAlloc_2276_, 4, v_l_2235_);
v___x_2272_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_object* v___x_2274_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 4, v_r_2264_);
lean_ctor_set(v___x_2146_, 3, v___x_2272_);
lean_ctor_set(v___x_2146_, 2, v_v_2266_);
lean_ctor_set(v___x_2146_, 1, v_k_2265_);
lean_ctor_set(v___x_2146_, 0, v___x_2270_);
v___x_2274_ = v___x_2146_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2270_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v_k_2265_);
lean_ctor_set(v_reuseFailAlloc_2275_, 2, v_v_2266_);
lean_ctor_set(v_reuseFailAlloc_2275_, 3, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2275_, 4, v_r_2264_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
else
{
lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2281_ = lean_unsigned_to_nat(2u);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 4, v_impl_2150_);
lean_ctor_set(v___x_2146_, 3, v_r_2264_);
lean_ctor_set(v___x_2146_, 0, v___x_2281_);
v___x_2283_ = v___x_2146_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_k_2141_);
lean_ctor_set(v_reuseFailAlloc_2284_, 2, v_v_2142_);
lean_ctor_set(v_reuseFailAlloc_2284_, 3, v_r_2264_);
lean_ctor_set(v_reuseFailAlloc_2284_, 4, v_impl_2150_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
else
{
lean_object* v___x_2286_; 
lean_dec(v_v_2142_);
lean_dec(v_k_2141_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 2, v_v_2138_);
lean_ctor_set(v___x_2146_, 1, v_k_2137_);
v___x_2286_ = v___x_2146_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_size_2140_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v_k_2137_);
lean_ctor_set(v_reuseFailAlloc_2287_, 2, v_v_2138_);
lean_ctor_set(v_reuseFailAlloc_2287_, 3, v_l_2143_);
lean_ctor_set(v_reuseFailAlloc_2287_, 4, v_r_2144_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
else
{
lean_object* v_impl_2288_; lean_object* v___x_2289_; 
lean_dec(v_size_2140_);
v_impl_2288_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2137_, v_v_2138_, v_l_2143_);
v___x_2289_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2144_) == 0)
{
lean_object* v_size_2290_; lean_object* v_size_2291_; lean_object* v_k_2292_; lean_object* v_v_2293_; lean_object* v_l_2294_; lean_object* v_r_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; uint8_t v___x_2298_; 
v_size_2290_ = lean_ctor_get(v_r_2144_, 0);
v_size_2291_ = lean_ctor_get(v_impl_2288_, 0);
v_k_2292_ = lean_ctor_get(v_impl_2288_, 1);
v_v_2293_ = lean_ctor_get(v_impl_2288_, 2);
v_l_2294_ = lean_ctor_get(v_impl_2288_, 3);
v_r_2295_ = lean_ctor_get(v_impl_2288_, 4);
lean_inc(v_r_2295_);
v___x_2296_ = lean_unsigned_to_nat(3u);
v___x_2297_ = lean_nat_mul(v___x_2296_, v_size_2290_);
v___x_2298_ = lean_nat_dec_lt(v___x_2297_, v_size_2291_);
lean_dec(v___x_2297_);
if (v___x_2298_ == 0)
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
lean_dec(v_r_2295_);
v___x_2299_ = lean_nat_add(v___x_2289_, v_size_2291_);
v___x_2300_ = lean_nat_add(v___x_2299_, v_size_2290_);
lean_dec(v___x_2299_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 3, v_impl_2288_);
lean_ctor_set(v___x_2146_, 0, v___x_2300_);
v___x_2302_ = v___x_2146_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2303_, 1, v_k_2141_);
lean_ctor_set(v_reuseFailAlloc_2303_, 2, v_v_2142_);
lean_ctor_set(v_reuseFailAlloc_2303_, 3, v_impl_2288_);
lean_ctor_set(v_reuseFailAlloc_2303_, 4, v_r_2144_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
else
{
lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2369_; 
lean_inc(v_l_2294_);
lean_inc(v_v_2293_);
lean_inc(v_k_2292_);
lean_inc(v_size_2291_);
v_isSharedCheck_2369_ = !lean_is_exclusive(v_impl_2288_);
if (v_isSharedCheck_2369_ == 0)
{
lean_object* v_unused_2370_; lean_object* v_unused_2371_; lean_object* v_unused_2372_; lean_object* v_unused_2373_; lean_object* v_unused_2374_; 
v_unused_2370_ = lean_ctor_get(v_impl_2288_, 4);
lean_dec(v_unused_2370_);
v_unused_2371_ = lean_ctor_get(v_impl_2288_, 3);
lean_dec(v_unused_2371_);
v_unused_2372_ = lean_ctor_get(v_impl_2288_, 2);
lean_dec(v_unused_2372_);
v_unused_2373_ = lean_ctor_get(v_impl_2288_, 1);
lean_dec(v_unused_2373_);
v_unused_2374_ = lean_ctor_get(v_impl_2288_, 0);
lean_dec(v_unused_2374_);
v___x_2305_ = v_impl_2288_;
v_isShared_2306_ = v_isSharedCheck_2369_;
goto v_resetjp_2304_;
}
else
{
lean_dec(v_impl_2288_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2369_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v_size_2307_; lean_object* v_size_2308_; lean_object* v_k_2309_; lean_object* v_v_2310_; lean_object* v_l_2311_; lean_object* v_r_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; 
v_size_2307_ = lean_ctor_get(v_l_2294_, 0);
v_size_2308_ = lean_ctor_get(v_r_2295_, 0);
v_k_2309_ = lean_ctor_get(v_r_2295_, 1);
v_v_2310_ = lean_ctor_get(v_r_2295_, 2);
v_l_2311_ = lean_ctor_get(v_r_2295_, 3);
v_r_2312_ = lean_ctor_get(v_r_2295_, 4);
v___x_2313_ = lean_unsigned_to_nat(2u);
v___x_2314_ = lean_nat_mul(v___x_2313_, v_size_2307_);
v___x_2315_ = lean_nat_dec_lt(v_size_2308_, v___x_2314_);
lean_dec(v___x_2314_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2344_; 
lean_inc(v_r_2312_);
lean_inc(v_l_2311_);
lean_inc(v_v_2310_);
lean_inc(v_k_2309_);
v_isSharedCheck_2344_ = !lean_is_exclusive(v_r_2295_);
if (v_isSharedCheck_2344_ == 0)
{
lean_object* v_unused_2345_; lean_object* v_unused_2346_; lean_object* v_unused_2347_; lean_object* v_unused_2348_; lean_object* v_unused_2349_; 
v_unused_2345_ = lean_ctor_get(v_r_2295_, 4);
lean_dec(v_unused_2345_);
v_unused_2346_ = lean_ctor_get(v_r_2295_, 3);
lean_dec(v_unused_2346_);
v_unused_2347_ = lean_ctor_get(v_r_2295_, 2);
lean_dec(v_unused_2347_);
v_unused_2348_ = lean_ctor_get(v_r_2295_, 1);
lean_dec(v_unused_2348_);
v_unused_2349_ = lean_ctor_get(v_r_2295_, 0);
lean_dec(v_unused_2349_);
v___x_2317_ = v_r_2295_;
v_isShared_2318_ = v_isSharedCheck_2344_;
goto v_resetjp_2316_;
}
else
{
lean_dec(v_r_2295_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2344_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___x_2332_; lean_object* v___y_2334_; 
v___x_2319_ = lean_nat_add(v___x_2289_, v_size_2291_);
lean_dec(v_size_2291_);
v___x_2320_ = lean_nat_add(v___x_2319_, v_size_2290_);
lean_dec(v___x_2319_);
v___x_2332_ = lean_nat_add(v___x_2289_, v_size_2307_);
if (lean_obj_tag(v_l_2311_) == 0)
{
lean_object* v_size_2342_; 
v_size_2342_ = lean_ctor_get(v_l_2311_, 0);
lean_inc(v_size_2342_);
v___y_2334_ = v_size_2342_;
goto v___jp_2333_;
}
else
{
lean_object* v___x_2343_; 
v___x_2343_ = lean_unsigned_to_nat(0u);
v___y_2334_ = v___x_2343_;
goto v___jp_2333_;
}
v___jp_2321_:
{
lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2325_ = lean_nat_add(v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec(v___y_2323_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 4, v_r_2144_);
lean_ctor_set(v___x_2317_, 3, v_r_2312_);
lean_ctor_set(v___x_2317_, 2, v_v_2142_);
lean_ctor_set(v___x_2317_, 1, v_k_2141_);
lean_ctor_set(v___x_2317_, 0, v___x_2325_);
v___x_2327_ = v___x_2317_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2325_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v_k_2141_);
lean_ctor_set(v_reuseFailAlloc_2331_, 2, v_v_2142_);
lean_ctor_set(v_reuseFailAlloc_2331_, 3, v_r_2312_);
lean_ctor_set(v_reuseFailAlloc_2331_, 4, v_r_2144_);
v___x_2327_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2329_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 4, v___x_2327_);
lean_ctor_set(v___x_2305_, 3, v___y_2322_);
lean_ctor_set(v___x_2305_, 2, v_v_2310_);
lean_ctor_set(v___x_2305_, 1, v_k_2309_);
lean_ctor_set(v___x_2305_, 0, v___x_2320_);
v___x_2329_ = v___x_2305_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2320_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_k_2309_);
lean_ctor_set(v_reuseFailAlloc_2330_, 2, v_v_2310_);
lean_ctor_set(v_reuseFailAlloc_2330_, 3, v___y_2322_);
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
v___jp_2333_:
{
lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2335_ = lean_nat_add(v___x_2332_, v___y_2334_);
lean_dec(v___y_2334_);
lean_dec(v___x_2332_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 4, v_l_2311_);
lean_ctor_set(v___x_2146_, 3, v_l_2294_);
lean_ctor_set(v___x_2146_, 2, v_v_2293_);
lean_ctor_set(v___x_2146_, 1, v_k_2292_);
lean_ctor_set(v___x_2146_, 0, v___x_2335_);
v___x_2337_ = v___x_2146_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_k_2292_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v_v_2293_);
lean_ctor_set(v_reuseFailAlloc_2341_, 3, v_l_2294_);
lean_ctor_set(v_reuseFailAlloc_2341_, 4, v_l_2311_);
v___x_2337_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_nat_add(v___x_2289_, v_size_2290_);
if (lean_obj_tag(v_r_2312_) == 0)
{
lean_object* v_size_2339_; 
v_size_2339_ = lean_ctor_get(v_r_2312_, 0);
lean_inc(v_size_2339_);
v___y_2322_ = v___x_2337_;
v___y_2323_ = v___x_2338_;
v___y_2324_ = v_size_2339_;
goto v___jp_2321_;
}
else
{
lean_object* v___x_2340_; 
v___x_2340_ = lean_unsigned_to_nat(0u);
v___y_2322_ = v___x_2337_;
v___y_2323_ = v___x_2338_;
v___y_2324_ = v___x_2340_;
goto v___jp_2321_;
}
}
}
}
}
else
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2355_; 
lean_del_object(v___x_2146_);
v___x_2350_ = lean_nat_add(v___x_2289_, v_size_2291_);
lean_dec(v_size_2291_);
v___x_2351_ = lean_nat_add(v___x_2350_, v_size_2290_);
lean_dec(v___x_2350_);
v___x_2352_ = lean_nat_add(v___x_2289_, v_size_2290_);
v___x_2353_ = lean_nat_add(v___x_2352_, v_size_2308_);
lean_dec(v___x_2352_);
lean_inc_ref(v_r_2144_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 4, v_r_2144_);
lean_ctor_set(v___x_2305_, 3, v_r_2295_);
lean_ctor_set(v___x_2305_, 2, v_v_2142_);
lean_ctor_set(v___x_2305_, 1, v_k_2141_);
lean_ctor_set(v___x_2305_, 0, v___x_2353_);
v___x_2355_ = v___x_2305_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2368_, 1, v_k_2141_);
lean_ctor_set(v_reuseFailAlloc_2368_, 2, v_v_2142_);
lean_ctor_set(v_reuseFailAlloc_2368_, 3, v_r_2295_);
lean_ctor_set(v_reuseFailAlloc_2368_, 4, v_r_2144_);
v___x_2355_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
v_isSharedCheck_2362_ = !lean_is_exclusive(v_r_2144_);
if (v_isSharedCheck_2362_ == 0)
{
lean_object* v_unused_2363_; lean_object* v_unused_2364_; lean_object* v_unused_2365_; lean_object* v_unused_2366_; lean_object* v_unused_2367_; 
v_unused_2363_ = lean_ctor_get(v_r_2144_, 4);
lean_dec(v_unused_2363_);
v_unused_2364_ = lean_ctor_get(v_r_2144_, 3);
lean_dec(v_unused_2364_);
v_unused_2365_ = lean_ctor_get(v_r_2144_, 2);
lean_dec(v_unused_2365_);
v_unused_2366_ = lean_ctor_get(v_r_2144_, 1);
lean_dec(v_unused_2366_);
v_unused_2367_ = lean_ctor_get(v_r_2144_, 0);
lean_dec(v_unused_2367_);
v___x_2357_ = v_r_2144_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_dec(v_r_2144_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 4, v___x_2355_);
lean_ctor_set(v___x_2357_, 3, v_l_2294_);
lean_ctor_set(v___x_2357_, 2, v_v_2293_);
lean_ctor_set(v___x_2357_, 1, v_k_2292_);
lean_ctor_set(v___x_2357_, 0, v___x_2351_);
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2351_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v_k_2292_);
lean_ctor_set(v_reuseFailAlloc_2361_, 2, v_v_2293_);
lean_ctor_set(v_reuseFailAlloc_2361_, 3, v_l_2294_);
lean_ctor_set(v_reuseFailAlloc_2361_, 4, v___x_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2375_; 
v_l_2375_ = lean_ctor_get(v_impl_2288_, 3);
if (lean_obj_tag(v_l_2375_) == 0)
{
lean_object* v_r_2376_; lean_object* v_k_2377_; lean_object* v_v_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2389_; 
lean_inc_ref(v_l_2375_);
v_r_2376_ = lean_ctor_get(v_impl_2288_, 4);
v_k_2377_ = lean_ctor_get(v_impl_2288_, 1);
v_v_2378_ = lean_ctor_get(v_impl_2288_, 2);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_impl_2288_);
if (v_isSharedCheck_2389_ == 0)
{
lean_object* v_unused_2390_; lean_object* v_unused_2391_; 
v_unused_2390_ = lean_ctor_get(v_impl_2288_, 3);
lean_dec(v_unused_2390_);
v_unused_2391_ = lean_ctor_get(v_impl_2288_, 0);
lean_dec(v_unused_2391_);
v___x_2380_ = v_impl_2288_;
v_isShared_2381_ = v_isSharedCheck_2389_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_r_2376_);
lean_inc(v_v_2378_);
lean_inc(v_k_2377_);
lean_dec(v_impl_2288_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2389_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2382_; lean_object* v___x_2384_; 
v___x_2382_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2376_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 3, v_r_2376_);
lean_ctor_set(v___x_2380_, 2, v_v_2142_);
lean_ctor_set(v___x_2380_, 1, v_k_2141_);
lean_ctor_set(v___x_2380_, 0, v___x_2289_);
v___x_2384_ = v___x_2380_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2289_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_k_2141_);
lean_ctor_set(v_reuseFailAlloc_2388_, 2, v_v_2142_);
lean_ctor_set(v_reuseFailAlloc_2388_, 3, v_r_2376_);
lean_ctor_set(v_reuseFailAlloc_2388_, 4, v_r_2376_);
v___x_2384_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2386_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 4, v___x_2384_);
lean_ctor_set(v___x_2146_, 3, v_l_2375_);
lean_ctor_set(v___x_2146_, 2, v_v_2378_);
lean_ctor_set(v___x_2146_, 1, v_k_2377_);
lean_ctor_set(v___x_2146_, 0, v___x_2382_);
v___x_2386_ = v___x_2146_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v_k_2377_);
lean_ctor_set(v_reuseFailAlloc_2387_, 2, v_v_2378_);
lean_ctor_set(v_reuseFailAlloc_2387_, 3, v_l_2375_);
lean_ctor_set(v_reuseFailAlloc_2387_, 4, v___x_2384_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
else
{
lean_object* v_r_2392_; 
v_r_2392_ = lean_ctor_get(v_impl_2288_, 4);
lean_inc(v_r_2392_);
if (lean_obj_tag(v_r_2392_) == 0)
{
lean_object* v_k_2393_; lean_object* v_v_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2417_; 
lean_inc(v_l_2375_);
v_k_2393_ = lean_ctor_get(v_impl_2288_, 1);
v_v_2394_ = lean_ctor_get(v_impl_2288_, 2);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_impl_2288_);
if (v_isSharedCheck_2417_ == 0)
{
lean_object* v_unused_2418_; lean_object* v_unused_2419_; lean_object* v_unused_2420_; 
v_unused_2418_ = lean_ctor_get(v_impl_2288_, 4);
lean_dec(v_unused_2418_);
v_unused_2419_ = lean_ctor_get(v_impl_2288_, 3);
lean_dec(v_unused_2419_);
v_unused_2420_ = lean_ctor_get(v_impl_2288_, 0);
lean_dec(v_unused_2420_);
v___x_2396_ = v_impl_2288_;
v_isShared_2397_ = v_isSharedCheck_2417_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_v_2394_);
lean_inc(v_k_2393_);
lean_dec(v_impl_2288_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2417_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v_k_2398_; lean_object* v_v_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2413_; 
v_k_2398_ = lean_ctor_get(v_r_2392_, 1);
v_v_2399_ = lean_ctor_get(v_r_2392_, 2);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_r_2392_);
if (v_isSharedCheck_2413_ == 0)
{
lean_object* v_unused_2414_; lean_object* v_unused_2415_; lean_object* v_unused_2416_; 
v_unused_2414_ = lean_ctor_get(v_r_2392_, 4);
lean_dec(v_unused_2414_);
v_unused_2415_ = lean_ctor_get(v_r_2392_, 3);
lean_dec(v_unused_2415_);
v_unused_2416_ = lean_ctor_get(v_r_2392_, 0);
lean_dec(v_unused_2416_);
v___x_2401_ = v_r_2392_;
v_isShared_2402_ = v_isSharedCheck_2413_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_v_2399_);
lean_inc(v_k_2398_);
lean_dec(v_r_2392_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2413_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2403_ = lean_unsigned_to_nat(3u);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 4, v_l_2375_);
lean_ctor_set(v___x_2401_, 3, v_l_2375_);
lean_ctor_set(v___x_2401_, 2, v_v_2394_);
lean_ctor_set(v___x_2401_, 1, v_k_2393_);
lean_ctor_set(v___x_2401_, 0, v___x_2289_);
v___x_2405_ = v___x_2401_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2289_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_k_2393_);
lean_ctor_set(v_reuseFailAlloc_2412_, 2, v_v_2394_);
lean_ctor_set(v_reuseFailAlloc_2412_, 3, v_l_2375_);
lean_ctor_set(v_reuseFailAlloc_2412_, 4, v_l_2375_);
v___x_2405_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2407_; 
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 4, v_l_2375_);
lean_ctor_set(v___x_2396_, 2, v_v_2142_);
lean_ctor_set(v___x_2396_, 1, v_k_2141_);
lean_ctor_set(v___x_2396_, 0, v___x_2289_);
v___x_2407_ = v___x_2396_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2289_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v_k_2141_);
lean_ctor_set(v_reuseFailAlloc_2411_, 2, v_v_2142_);
lean_ctor_set(v_reuseFailAlloc_2411_, 3, v_l_2375_);
lean_ctor_set(v_reuseFailAlloc_2411_, 4, v_l_2375_);
v___x_2407_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2409_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 4, v___x_2407_);
lean_ctor_set(v___x_2146_, 3, v___x_2405_);
lean_ctor_set(v___x_2146_, 2, v_v_2399_);
lean_ctor_set(v___x_2146_, 1, v_k_2398_);
lean_ctor_set(v___x_2146_, 0, v___x_2403_);
v___x_2409_ = v___x_2146_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2403_);
lean_ctor_set(v_reuseFailAlloc_2410_, 1, v_k_2398_);
lean_ctor_set(v_reuseFailAlloc_2410_, 2, v_v_2399_);
lean_ctor_set(v_reuseFailAlloc_2410_, 3, v___x_2405_);
lean_ctor_set(v_reuseFailAlloc_2410_, 4, v___x_2407_);
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
}
}
else
{
lean_object* v___x_2421_; lean_object* v___x_2423_; 
v___x_2421_ = lean_unsigned_to_nat(2u);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 4, v_r_2392_);
lean_ctor_set(v___x_2146_, 3, v_impl_2288_);
lean_ctor_set(v___x_2146_, 0, v___x_2421_);
v___x_2423_ = v___x_2146_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_k_2141_);
lean_ctor_set(v_reuseFailAlloc_2424_, 2, v_v_2142_);
lean_ctor_set(v_reuseFailAlloc_2424_, 3, v_impl_2288_);
lean_ctor_set(v_reuseFailAlloc_2424_, 4, v_r_2392_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = lean_unsigned_to_nat(1u);
v___x_2427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
lean_ctor_set(v___x_2427_, 1, v_k_2137_);
lean_ctor_set(v___x_2427_, 2, v_v_2138_);
lean_ctor_set(v___x_2427_, 3, v_t_2139_);
lean_ctor_set(v___x_2427_, 4, v_t_2139_);
return v___x_2427_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(lean_object* v_k_2428_, lean_object* v_t_2429_){
_start:
{
if (lean_obj_tag(v_t_2429_) == 0)
{
lean_object* v_k_2430_; lean_object* v_l_2431_; lean_object* v_r_2432_; uint8_t v___x_2433_; 
v_k_2430_ = lean_ctor_get(v_t_2429_, 1);
v_l_2431_ = lean_ctor_get(v_t_2429_, 3);
v_r_2432_ = lean_ctor_get(v_t_2429_, 4);
v___x_2433_ = lean_nat_dec_lt(v_k_2428_, v_k_2430_);
if (v___x_2433_ == 0)
{
uint8_t v___x_2434_; 
v___x_2434_ = lean_nat_dec_eq(v_k_2428_, v_k_2430_);
if (v___x_2434_ == 0)
{
v_t_2429_ = v_r_2432_;
goto _start;
}
else
{
return v___x_2434_;
}
}
else
{
v_t_2429_ = v_l_2431_;
goto _start;
}
}
else
{
uint8_t v___x_2437_; 
v___x_2437_ = 0;
return v___x_2437_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg___boxed(lean_object* v_k_2438_, lean_object* v_t_2439_){
_start:
{
uint8_t v_res_2440_; lean_object* v_r_2441_; 
v_res_2440_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2438_, v_t_2439_);
lean_dec(v_t_2439_);
lean_dec(v_k_2438_);
v_r_2441_ = lean_box(v_res_2440_);
return v_r_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(lean_object* v_y_2442_, lean_object* v_x_2443_, size_t v_x_2444_, size_t v_x_2445_){
_start:
{
if (lean_obj_tag(v_x_2443_) == 0)
{
lean_object* v_cs_2446_; size_t v_j_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; 
v_cs_2446_ = lean_ctor_get(v_x_2443_, 0);
v_j_2447_ = lean_usize_shift_right(v_x_2444_, v_x_2445_);
v___x_2448_ = lean_usize_to_nat(v_j_2447_);
v___x_2449_ = lean_array_get_size(v_cs_2446_);
v___x_2450_ = lean_nat_dec_lt(v___x_2448_, v___x_2449_);
if (v___x_2450_ == 0)
{
lean_dec(v___x_2448_);
lean_dec(v_y_2442_);
return v_x_2443_;
}
else
{
lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2468_; 
lean_inc_ref(v_cs_2446_);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_x_2443_);
if (v_isSharedCheck_2468_ == 0)
{
lean_object* v_unused_2469_; 
v_unused_2469_ = lean_ctor_get(v_x_2443_, 0);
lean_dec(v_unused_2469_);
v___x_2452_ = v_x_2443_;
v_isShared_2453_ = v_isSharedCheck_2468_;
goto v_resetjp_2451_;
}
else
{
lean_dec(v_x_2443_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2468_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
size_t v___x_2454_; size_t v___x_2455_; size_t v___x_2456_; size_t v_i_2457_; size_t v___x_2458_; size_t v_shift_2459_; lean_object* v_v_2460_; lean_object* v___x_2461_; lean_object* v_xs_x27_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2454_ = ((size_t)1ULL);
v___x_2455_ = lean_usize_shift_left(v___x_2454_, v_x_2445_);
v___x_2456_ = lean_usize_sub(v___x_2455_, v___x_2454_);
v_i_2457_ = lean_usize_land(v_x_2444_, v___x_2456_);
v___x_2458_ = ((size_t)5ULL);
v_shift_2459_ = lean_usize_sub(v_x_2445_, v___x_2458_);
v_v_2460_ = lean_array_fget(v_cs_2446_, v___x_2448_);
v___x_2461_ = lean_box(0);
v_xs_x27_2462_ = lean_array_fset(v_cs_2446_, v___x_2448_, v___x_2461_);
v___x_2463_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2442_, v_v_2460_, v_i_2457_, v_shift_2459_);
v___x_2464_ = lean_array_fset(v_xs_x27_2462_, v___x_2448_, v___x_2463_);
lean_dec(v___x_2448_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v___x_2464_);
v___x_2466_ = v___x_2452_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
else
{
lean_object* v_vs_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; uint8_t v___x_2473_; 
v_vs_2470_ = lean_ctor_get(v_x_2443_, 0);
v___x_2471_ = lean_usize_to_nat(v_x_2444_);
v___x_2472_ = lean_array_get_size(v_vs_2470_);
v___x_2473_ = lean_nat_dec_lt(v___x_2471_, v___x_2472_);
if (v___x_2473_ == 0)
{
lean_dec(v___x_2471_);
lean_dec(v_y_2442_);
return v_x_2443_;
}
else
{
lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2488_; 
lean_inc_ref(v_vs_2470_);
v_isSharedCheck_2488_ = !lean_is_exclusive(v_x_2443_);
if (v_isSharedCheck_2488_ == 0)
{
lean_object* v_unused_2489_; 
v_unused_2489_ = lean_ctor_get(v_x_2443_, 0);
lean_dec(v_unused_2489_);
v___x_2475_ = v_x_2443_;
v_isShared_2476_ = v_isSharedCheck_2488_;
goto v_resetjp_2474_;
}
else
{
lean_dec(v_x_2443_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2488_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v_v_2477_; lean_object* v___x_2478_; lean_object* v_xs_x27_2479_; lean_object* v___y_2481_; uint8_t v___x_2486_; 
v_v_2477_ = lean_array_fget(v_vs_2470_, v___x_2471_);
v___x_2478_ = lean_box(0);
v_xs_x27_2479_ = lean_array_fset(v_vs_2470_, v___x_2471_, v___x_2478_);
v___x_2486_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2442_, v_v_2477_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2442_, v___x_2478_, v_v_2477_);
v___y_2481_ = v___x_2487_;
goto v___jp_2480_;
}
else
{
lean_dec(v_y_2442_);
v___y_2481_ = v_v_2477_;
goto v___jp_2480_;
}
v___jp_2480_:
{
lean_object* v___x_2482_; lean_object* v___x_2484_; 
v___x_2482_ = lean_array_fset(v_xs_x27_2479_, v___x_2471_, v___y_2481_);
lean_dec(v___x_2471_);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v___x_2482_);
v___x_2484_ = v___x_2475_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2482_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2490_, lean_object* v_x_2491_, lean_object* v_x_2492_, lean_object* v_x_2493_){
_start:
{
size_t v_x_3936__boxed_2494_; size_t v_x_3937__boxed_2495_; lean_object* v_res_2496_; 
v_x_3936__boxed_2494_ = lean_unbox_usize(v_x_2492_);
lean_dec(v_x_2492_);
v_x_3937__boxed_2495_ = lean_unbox_usize(v_x_2493_);
lean_dec(v_x_2493_);
v_res_2496_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2490_, v_x_2491_, v_x_3936__boxed_2494_, v_x_3937__boxed_2495_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(lean_object* v_y_2497_, lean_object* v_t_2498_, lean_object* v_i_2499_){
_start:
{
lean_object* v_root_2500_; lean_object* v_tail_2501_; lean_object* v_size_2502_; size_t v_shift_2503_; lean_object* v_tailOff_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2531_; 
v_root_2500_ = lean_ctor_get(v_t_2498_, 0);
v_tail_2501_ = lean_ctor_get(v_t_2498_, 1);
v_size_2502_ = lean_ctor_get(v_t_2498_, 2);
v_shift_2503_ = lean_ctor_get_usize(v_t_2498_, 4);
v_tailOff_2504_ = lean_ctor_get(v_t_2498_, 3);
v_isSharedCheck_2531_ = !lean_is_exclusive(v_t_2498_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2506_ = v_t_2498_;
v_isShared_2507_ = v_isSharedCheck_2531_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_tailOff_2504_);
lean_inc(v_size_2502_);
lean_inc(v_tail_2501_);
lean_inc(v_root_2500_);
lean_dec(v_t_2498_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2531_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
uint8_t v___x_2508_; 
v___x_2508_ = lean_nat_dec_le(v_tailOff_2504_, v_i_2499_);
if (v___x_2508_ == 0)
{
size_t v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2509_ = lean_usize_of_nat(v_i_2499_);
v___x_2510_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2497_, v_root_2500_, v___x_2509_, v_shift_2503_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___x_2510_);
v___x_2512_ = v___x_2506_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_tail_2501_);
lean_ctor_set(v_reuseFailAlloc_2513_, 2, v_size_2502_);
lean_ctor_set(v_reuseFailAlloc_2513_, 3, v_tailOff_2504_);
lean_ctor_set_usize(v_reuseFailAlloc_2513_, 4, v_shift_2503_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2514_ = lean_nat_sub(v_i_2499_, v_tailOff_2504_);
v___x_2515_ = lean_array_get_size(v_tail_2501_);
v___x_2516_ = lean_nat_dec_lt(v___x_2514_, v___x_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2518_; 
lean_dec(v___x_2514_);
lean_dec(v_y_2497_);
if (v_isShared_2507_ == 0)
{
v___x_2518_ = v___x_2506_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_root_2500_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_tail_2501_);
lean_ctor_set(v_reuseFailAlloc_2519_, 2, v_size_2502_);
lean_ctor_set(v_reuseFailAlloc_2519_, 3, v_tailOff_2504_);
lean_ctor_set_usize(v_reuseFailAlloc_2519_, 4, v_shift_2503_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
else
{
lean_object* v_v_2520_; lean_object* v___x_2521_; lean_object* v_xs_x27_2522_; lean_object* v___y_2524_; uint8_t v___x_2529_; 
v_v_2520_ = lean_array_fget(v_tail_2501_, v___x_2514_);
v___x_2521_ = lean_box(0);
v_xs_x27_2522_ = lean_array_fset(v_tail_2501_, v___x_2514_, v___x_2521_);
v___x_2529_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2497_, v_v_2520_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2497_, v___x_2521_, v_v_2520_);
v___y_2524_ = v___x_2530_;
goto v___jp_2523_;
}
else
{
lean_dec(v_y_2497_);
v___y_2524_ = v_v_2520_;
goto v___jp_2523_;
}
v___jp_2523_:
{
lean_object* v___x_2525_; lean_object* v___x_2527_; 
v___x_2525_ = lean_array_fset(v_xs_x27_2522_, v___x_2514_, v___y_2524_);
lean_dec(v___x_2514_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 1, v___x_2525_);
v___x_2527_ = v___x_2506_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_root_2500_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v___x_2525_);
lean_ctor_set(v_reuseFailAlloc_2528_, 2, v_size_2502_);
lean_ctor_set(v_reuseFailAlloc_2528_, 3, v_tailOff_2504_);
lean_ctor_set_usize(v_reuseFailAlloc_2528_, 4, v_shift_2503_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2___boxed(lean_object* v_y_2532_, lean_object* v_t_2533_, lean_object* v_i_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2532_, v_t_2533_, v_i_2534_);
lean_dec(v_i_2534_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(lean_object* v_y_2536_, lean_object* v_x_2537_, lean_object* v_s_2538_){
_start:
{
lean_object* v_vars_2539_; lean_object* v_varMap_2540_; lean_object* v_varsHistory_2541_; lean_object* v_natToIntMap_2542_; lean_object* v_natDef_2543_; lean_object* v_dvds_2544_; lean_object* v_lowers_2545_; lean_object* v_uppers_2546_; lean_object* v_diseqs_2547_; lean_object* v_elimEqs_2548_; lean_object* v_elimStack_2549_; lean_object* v_occurs_2550_; lean_object* v_assignment_2551_; lean_object* v_nextCnstrId_2552_; uint8_t v_caseSplits_2553_; lean_object* v_steps_2554_; lean_object* v_penalties_2555_; lean_object* v_numReorderRequests_2556_; lean_object* v_conflict_x3f_2557_; lean_object* v_diseqSplits_2558_; lean_object* v_divMod_2559_; uint8_t v_usedCommRing_2560_; lean_object* v_nonlinearOccs_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2569_; 
v_vars_2539_ = lean_ctor_get(v_s_2538_, 0);
v_varMap_2540_ = lean_ctor_get(v_s_2538_, 1);
v_varsHistory_2541_ = lean_ctor_get(v_s_2538_, 2);
v_natToIntMap_2542_ = lean_ctor_get(v_s_2538_, 3);
v_natDef_2543_ = lean_ctor_get(v_s_2538_, 4);
v_dvds_2544_ = lean_ctor_get(v_s_2538_, 5);
v_lowers_2545_ = lean_ctor_get(v_s_2538_, 6);
v_uppers_2546_ = lean_ctor_get(v_s_2538_, 7);
v_diseqs_2547_ = lean_ctor_get(v_s_2538_, 8);
v_elimEqs_2548_ = lean_ctor_get(v_s_2538_, 9);
v_elimStack_2549_ = lean_ctor_get(v_s_2538_, 10);
v_occurs_2550_ = lean_ctor_get(v_s_2538_, 11);
v_assignment_2551_ = lean_ctor_get(v_s_2538_, 12);
v_nextCnstrId_2552_ = lean_ctor_get(v_s_2538_, 13);
v_caseSplits_2553_ = lean_ctor_get_uint8(v_s_2538_, sizeof(void*)*21);
v_steps_2554_ = lean_ctor_get(v_s_2538_, 14);
v_penalties_2555_ = lean_ctor_get(v_s_2538_, 15);
v_numReorderRequests_2556_ = lean_ctor_get(v_s_2538_, 16);
v_conflict_x3f_2557_ = lean_ctor_get(v_s_2538_, 17);
v_diseqSplits_2558_ = lean_ctor_get(v_s_2538_, 18);
v_divMod_2559_ = lean_ctor_get(v_s_2538_, 19);
v_usedCommRing_2560_ = lean_ctor_get_uint8(v_s_2538_, sizeof(void*)*21 + 1);
v_nonlinearOccs_2561_ = lean_ctor_get(v_s_2538_, 20);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_s_2538_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2563_ = v_s_2538_;
v_isShared_2564_ = v_isSharedCheck_2569_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_nonlinearOccs_2561_);
lean_inc(v_divMod_2559_);
lean_inc(v_diseqSplits_2558_);
lean_inc(v_conflict_x3f_2557_);
lean_inc(v_numReorderRequests_2556_);
lean_inc(v_penalties_2555_);
lean_inc(v_steps_2554_);
lean_inc(v_nextCnstrId_2552_);
lean_inc(v_assignment_2551_);
lean_inc(v_occurs_2550_);
lean_inc(v_elimStack_2549_);
lean_inc(v_elimEqs_2548_);
lean_inc(v_diseqs_2547_);
lean_inc(v_uppers_2546_);
lean_inc(v_lowers_2545_);
lean_inc(v_dvds_2544_);
lean_inc(v_natDef_2543_);
lean_inc(v_natToIntMap_2542_);
lean_inc(v_varsHistory_2541_);
lean_inc(v_varMap_2540_);
lean_inc(v_vars_2539_);
lean_dec(v_s_2538_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2569_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2565_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2536_, v_occurs_2550_, v_x_2537_);
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 11, v___x_2565_);
v___x_2567_ = v___x_2563_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_vars_2539_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_varMap_2540_);
lean_ctor_set(v_reuseFailAlloc_2568_, 2, v_varsHistory_2541_);
lean_ctor_set(v_reuseFailAlloc_2568_, 3, v_natToIntMap_2542_);
lean_ctor_set(v_reuseFailAlloc_2568_, 4, v_natDef_2543_);
lean_ctor_set(v_reuseFailAlloc_2568_, 5, v_dvds_2544_);
lean_ctor_set(v_reuseFailAlloc_2568_, 6, v_lowers_2545_);
lean_ctor_set(v_reuseFailAlloc_2568_, 7, v_uppers_2546_);
lean_ctor_set(v_reuseFailAlloc_2568_, 8, v_diseqs_2547_);
lean_ctor_set(v_reuseFailAlloc_2568_, 9, v_elimEqs_2548_);
lean_ctor_set(v_reuseFailAlloc_2568_, 10, v_elimStack_2549_);
lean_ctor_set(v_reuseFailAlloc_2568_, 11, v___x_2565_);
lean_ctor_set(v_reuseFailAlloc_2568_, 12, v_assignment_2551_);
lean_ctor_set(v_reuseFailAlloc_2568_, 13, v_nextCnstrId_2552_);
lean_ctor_set(v_reuseFailAlloc_2568_, 14, v_steps_2554_);
lean_ctor_set(v_reuseFailAlloc_2568_, 15, v_penalties_2555_);
lean_ctor_set(v_reuseFailAlloc_2568_, 16, v_numReorderRequests_2556_);
lean_ctor_set(v_reuseFailAlloc_2568_, 17, v_conflict_x3f_2557_);
lean_ctor_set(v_reuseFailAlloc_2568_, 18, v_diseqSplits_2558_);
lean_ctor_set(v_reuseFailAlloc_2568_, 19, v_divMod_2559_);
lean_ctor_set(v_reuseFailAlloc_2568_, 20, v_nonlinearOccs_2561_);
lean_ctor_set_uint8(v_reuseFailAlloc_2568_, sizeof(void*)*21, v_caseSplits_2553_);
lean_ctor_set_uint8(v_reuseFailAlloc_2568_, sizeof(void*)*21 + 1, v_usedCommRing_2560_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed(lean_object* v_y_2570_, lean_object* v_x_2571_, lean_object* v_s_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(v_y_2570_, v_x_2571_, v_s_2572_);
lean_dec(v_x_2571_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(lean_object* v_x_2574_, lean_object* v_y_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v___f_2579_; lean_object* v___x_2580_; 
lean_inc(v_x_2574_);
lean_inc(v_y_2575_);
v___f_2579_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2579_, 0, v_y_2575_);
lean_closure_set(v___f_2579_, 1, v_x_2574_);
v___x_2580_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2574_, v_a_2576_, v_a_2577_);
lean_dec(v_x_2574_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2592_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2592_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2592_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
uint8_t v___x_2585_; 
v___x_2585_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2575_, v_a_2581_);
lean_dec(v_a_2581_);
lean_dec(v_y_2575_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
lean_del_object(v___x_2583_);
v___x_2586_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2587_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2586_, v___f_2579_, v_a_2576_);
return v___x_2587_;
}
else
{
lean_object* v___x_2588_; lean_object* v___x_2590_; 
lean_dec_ref(v___f_2579_);
v___x_2588_ = lean_box(0);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v___x_2588_);
v___x_2590_ = v___x_2583_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec_ref(v___f_2579_);
lean_dec(v_y_2575_);
v_a_2593_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2580_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2580_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___boxed(lean_object* v_x_2601_, lean_object* v_y_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2601_, v_y_2602_, v_a_2603_, v_a_2604_);
lean_dec_ref(v_a_2604_);
lean_dec(v_a_2603_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc(lean_object* v_x_2607_, lean_object* v_y_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2607_, v_y_2608_, v_a_2609_, v_a_2617_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___boxed(lean_object* v_x_2621_, lean_object* v_y_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc(v_x_2621_, v_y_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
lean_dec(v_a_2624_);
lean_dec(v_a_2623_);
return v_res_2634_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(lean_object* v_00_u03b2_2635_, lean_object* v_k_2636_, lean_object* v_t_2637_){
_start:
{
uint8_t v___x_2638_; 
v___x_2638_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2636_, v_t_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2639_, lean_object* v_k_2640_, lean_object* v_t_2641_){
_start:
{
uint8_t v_res_2642_; lean_object* v_r_2643_; 
v_res_2642_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(v_00_u03b2_2639_, v_k_2640_, v_t_2641_);
lean_dec(v_t_2641_);
lean_dec(v_k_2640_);
v_r_2643_ = lean_box(v_res_2642_);
return v_r_2643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1(lean_object* v_00_u03b2_2644_, lean_object* v_k_2645_, lean_object* v_v_2646_, lean_object* v_t_2647_, lean_object* v_hl_2648_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2645_, v_v_2646_, v_t_2647_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(lean_object* v_y_2650_, lean_object* v_p_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
if (lean_obj_tag(v_p_2651_) == 1)
{
lean_object* v_v_2655_; lean_object* v_p_2656_; lean_object* v___x_2657_; 
v_v_2655_ = lean_ctor_get(v_p_2651_, 1);
lean_inc(v_v_2655_);
v_p_2656_ = lean_ctor_get(v_p_2651_, 2);
lean_inc_ref(v_p_2656_);
lean_dec_ref_known(v_p_2651_, 3);
lean_inc(v_y_2650_);
v___x_2657_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_v_2655_, v_y_2650_, v_a_2652_, v_a_2653_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_dec_ref_known(v___x_2657_, 1);
v_p_2651_ = v_p_2656_;
goto _start;
}
else
{
lean_dec_ref(v_p_2656_);
lean_dec(v_y_2650_);
return v___x_2657_;
}
}
else
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
lean_dec_ref(v_p_2651_);
lean_dec(v_y_2650_);
v___x_2659_ = lean_box(0);
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
return v___x_2660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg___boxed(lean_object* v_y_2661_, lean_object* v_p_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2661_, v_p_2662_, v_a_2663_, v_a_2664_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(lean_object* v_y_2667_, lean_object* v_p_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2667_, v_p_2668_, v_a_2669_, v_a_2677_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___boxed(lean_object* v_y_2681_, lean_object* v_p_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(v_y_2681_, v_p_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec(v_a_2683_);
return v_res_2694_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = ((lean_object*)(l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__0));
v___x_2697_ = l_Lean_stringToMessageData(v___x_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg(lean_object* v_p_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
if (lean_obj_tag(v_p_2698_) == 1)
{
lean_object* v_v_2705_; lean_object* v_p_2706_; lean_object* v___x_2707_; 
v_v_2705_ = lean_ctor_get(v_p_2698_, 1);
lean_inc(v_v_2705_);
v_p_2706_ = lean_ctor_get(v_p_2698_, 2);
lean_inc_ref(v_p_2706_);
lean_dec_ref_known(v_p_2698_, 3);
v___x_2707_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_v_2705_, v_p_2706_, v_a_2699_, v_a_2702_);
return v___x_2707_;
}
else
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_dec_ref(v_p_2698_);
v___x_2708_ = lean_obj_once(&l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1, &l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1_once, _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1);
v___x_2709_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2708_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
return v___x_2709_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg___boxed(lean_object* v_p_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_a_2711_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs(lean_object* v_p_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2718_, v_a_2719_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___boxed(lean_object* v_p_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Int_Internal_Linear_Poly_updateOccs(v_p_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
lean_dec(v_a_2741_);
lean_dec_ref(v_a_2740_);
lean_dec(v_a_2739_);
lean_dec_ref(v_a_2738_);
lean_dec(v_a_2737_);
lean_dec_ref(v_a_2736_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
lean_dec(v_a_2733_);
lean_dec(v_a_2732_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go_spec__0(lean_object* v_a_2744_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Rat_ofInt(v_a_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(lean_object* v_a_2746_, lean_object* v_v_2747_, lean_object* v_a_2748_){
_start:
{
if (lean_obj_tag(v_a_2748_) == 0)
{
lean_object* v_k_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2758_; 
v_k_2749_ = lean_ctor_get(v_a_2748_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v_a_2748_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2751_ = v_a_2748_;
v_isShared_2752_ = v_isSharedCheck_2758_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_k_2749_);
lean_dec(v_a_2748_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2758_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2756_; 
v___x_2753_ = l_Rat_ofInt(v_k_2749_);
v___x_2754_ = l_Rat_add(v_v_2747_, v___x_2753_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set_tag(v___x_2751_, 1);
lean_ctor_set(v___x_2751_, 0, v___x_2754_);
v___x_2756_ = v___x_2751_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2754_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
else
{
lean_object* v_k_2759_; lean_object* v_v_2760_; lean_object* v_p_2761_; lean_object* v_size_2762_; uint8_t v___x_2763_; 
v_k_2759_ = lean_ctor_get(v_a_2748_, 0);
lean_inc(v_k_2759_);
v_v_2760_ = lean_ctor_get(v_a_2748_, 1);
lean_inc(v_v_2760_);
v_p_2761_ = lean_ctor_get(v_a_2748_, 2);
lean_inc_ref(v_p_2761_);
lean_dec_ref_known(v_a_2748_, 3);
v_size_2762_ = lean_ctor_get(v_a_2746_, 2);
v___x_2763_ = lean_nat_dec_lt(v_v_2760_, v_size_2762_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; 
lean_dec_ref(v_p_2761_);
lean_dec(v_v_2760_);
lean_dec(v_k_2759_);
lean_dec_ref(v_v_2747_);
v___x_2764_ = lean_box(0);
return v___x_2764_;
}
else
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2765_ = l_instInhabitedRat;
v___x_2766_ = l_Rat_ofInt(v_k_2759_);
v___x_2767_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2765_, v_a_2746_, v_v_2760_);
lean_dec(v_v_2760_);
v___x_2768_ = l_Rat_mul(v___x_2766_, v___x_2767_);
lean_dec_ref(v___x_2766_);
v___x_2769_ = l_Rat_add(v_v_2747_, v___x_2768_);
v_v_2747_ = v___x_2769_;
v_a_2748_ = v_p_2761_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go___boxed(lean_object* v_a_2771_, lean_object* v_v_2772_, lean_object* v_a_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_a_2771_, v_v_2772_, v_a_2773_);
lean_dec_ref(v_a_2771_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(lean_object* v_a_2775_){
_start:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = lean_nat_to_int(v_a_2775_);
v___x_2777_ = l_Rat_ofInt(v___x_2776_);
return v___x_2777_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2778_ = lean_unsigned_to_nat(0u);
v___x_2779_ = l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(v___x_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg(lean_object* v_p_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2781_, v_a_2782_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2795_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2787_ = v___x_2784_;
v_isShared_2788_ = v_isSharedCheck_2795_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2784_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2795_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v_assignment_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2793_; 
v_assignment_2789_ = lean_ctor_get(v_a_2785_, 12);
lean_inc_ref(v_assignment_2789_);
lean_dec(v_a_2785_);
v___x_2790_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2791_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_assignment_2789_, v___x_2790_, v_p_2780_);
lean_dec_ref(v_assignment_2789_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2791_);
v___x_2793_ = v___x_2787_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2791_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref(v_p_2780_);
v_a_2796_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2784_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2784_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg___boxed(lean_object* v_p_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2804_, v_a_2805_, v_a_2806_);
lean_dec_ref(v_a_2806_);
lean_dec(v_a_2805_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f(lean_object* v_p_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2809_, v_a_2810_, v_a_2818_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___boxed(lean_object* v_p_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Int_Internal_Linear_Poly_eval_x3f(v_p_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
lean_dec(v_a_2828_);
lean_dec_ref(v_a_2827_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
lean_dec(v_a_2824_);
lean_dec(v_a_2823_);
return v_res_2834_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(lean_object* v_c_2835_){
_start:
{
lean_object* v_p_2836_; uint8_t v___x_2837_; 
v_p_2836_ = lean_ctor_get(v_c_2835_, 0);
v___x_2837_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat___boxed(lean_object* v_c_2838_){
_start:
{
uint8_t v_res_2839_; lean_object* v_r_2840_; 
v_res_2839_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(v_c_2838_);
lean_dec_ref(v_c_2838_);
v_r_2840_ = lean_box(v_res_2839_);
return v_r_2840_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(lean_object* v_c_2841_){
_start:
{
lean_object* v_d_2842_; lean_object* v_p_2843_; uint8_t v___x_2844_; 
v_d_2842_ = lean_ctor_get(v_c_2841_, 0);
lean_inc(v_d_2842_);
v_p_2843_ = lean_ctor_get(v_c_2841_, 1);
lean_inc_ref(v_p_2843_);
lean_dec_ref(v_c_2841_);
v___x_2844_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_2842_, v_p_2843_);
lean_dec_ref(v_p_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat___boxed(lean_object* v_c_2845_){
_start:
{
uint8_t v_res_2846_; lean_object* v_r_2847_; 
v_res_2846_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(v_c_2845_);
v_r_2847_ = lean_box(v_res_2846_);
return v_r_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object* v_c_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v_d_2852_; lean_object* v_p_2853_; lean_object* v___x_2854_; 
v_d_2852_ = lean_ctor_get(v_c_2848_, 0);
lean_inc(v_d_2852_);
v_p_2853_ = lean_ctor_get(v_c_2848_, 1);
lean_inc_ref(v_p_2853_);
lean_dec_ref(v_c_2848_);
v___x_2854_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2853_, v_a_2849_, v_a_2850_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2882_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_2882_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2882_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
if (lean_obj_tag(v_a_2855_) == 1)
{
lean_object* v_val_2859_; lean_object* v_num_2860_; lean_object* v_den_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v_val_2859_ = lean_ctor_get(v_a_2855_, 0);
lean_inc(v_val_2859_);
lean_dec_ref_known(v_a_2855_, 1);
v_num_2860_ = lean_ctor_get(v_val_2859_, 0);
lean_inc(v_num_2860_);
v_den_2861_ = lean_ctor_get(v_val_2859_, 1);
lean_inc(v_den_2861_);
lean_dec(v_val_2859_);
v___x_2862_ = lean_unsigned_to_nat(1u);
v___x_2863_ = lean_nat_dec_eq(v_den_2861_, v___x_2862_);
lean_dec(v_den_2861_);
if (v___x_2863_ == 0)
{
uint8_t v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2867_; 
lean_dec(v_num_2860_);
lean_dec(v_d_2852_);
v___x_2864_ = 0;
v___x_2865_ = lean_box(v___x_2864_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2865_);
v___x_2867_ = v___x_2857_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2865_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
else
{
lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; uint8_t v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2875_; 
v___x_2869_ = lean_int_emod(v_num_2860_, v_d_2852_);
lean_dec(v_d_2852_);
lean_dec(v_num_2860_);
v___x_2870_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_2871_ = lean_int_dec_eq(v___x_2869_, v___x_2870_);
lean_dec(v___x_2869_);
v___x_2872_ = l_Lean_Bool_toLBool(v___x_2871_);
v___x_2873_ = lean_box(v___x_2872_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2873_);
v___x_2875_ = v___x_2857_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2873_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
else
{
uint8_t v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2880_; 
lean_dec(v_a_2855_);
lean_dec(v_d_2852_);
v___x_2877_ = 2;
v___x_2878_ = lean_box(v___x_2877_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2878_);
v___x_2880_ = v___x_2857_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
lean_dec(v_d_2852_);
v_a_2883_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___x_2854_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2854_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg___boxed(lean_object* v_c_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2891_, v_a_2892_, v_a_2893_);
lean_dec_ref(v_a_2893_);
lean_dec(v_a_2892_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(lean_object* v_c_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2896_, v_a_2897_, v_a_2905_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___boxed(lean_object* v_c_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(v_c_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
lean_dec(v_a_2917_);
lean_dec_ref(v_a_2916_);
lean_dec(v_a_2915_);
lean_dec_ref(v_a_2914_);
lean_dec(v_a_2913_);
lean_dec_ref(v_a_2912_);
lean_dec(v_a_2911_);
lean_dec(v_a_2910_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg(lean_object* v_p_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2922_, v_a_2923_, v_a_2924_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2944_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2929_ = v___x_2926_;
v_isShared_2930_ = v_isSharedCheck_2944_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2926_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2944_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
if (lean_obj_tag(v_a_2927_) == 1)
{
lean_object* v_val_2931_; lean_object* v___x_2932_; uint8_t v___x_2933_; uint8_t v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2937_; 
v_val_2931_ = lean_ctor_get(v_a_2927_, 0);
lean_inc(v_val_2931_);
lean_dec_ref_known(v_a_2927_, 1);
v___x_2932_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2933_ = l_Rat_instDecidableLe(v_val_2931_, v___x_2932_);
v___x_2934_ = l_Lean_Bool_toLBool(v___x_2933_);
v___x_2935_ = lean_box(v___x_2934_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 0, v___x_2935_);
v___x_2937_ = v___x_2929_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2935_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
else
{
uint8_t v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2942_; 
lean_dec(v_a_2927_);
v___x_2939_ = 2;
v___x_2940_ = lean_box(v___x_2939_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 0, v___x_2940_);
v___x_2942_ = v___x_2929_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
v_a_2945_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2926_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2926_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg___boxed(lean_object* v_p_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2953_, v_a_2954_, v_a_2955_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe(lean_object* v_p_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2958_, v_a_2959_, v_a_2967_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___boxed(lean_object* v_p_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_Int_Internal_Linear_Poly_satisfiedLe(v_p_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_);
lean_dec(v_a_2981_);
lean_dec_ref(v_a_2980_);
lean_dec(v_a_2979_);
lean_dec_ref(v_a_2978_);
lean_dec(v_a_2977_);
lean_dec_ref(v_a_2976_);
lean_dec(v_a_2975_);
lean_dec_ref(v_a_2974_);
lean_dec(v_a_2973_);
lean_dec(v_a_2972_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(lean_object* v_c_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_){
_start:
{
lean_object* v_p_2988_; lean_object* v___x_2989_; 
v_p_2988_ = lean_ctor_get(v_c_2984_, 0);
lean_inc_ref(v_p_2988_);
lean_dec_ref(v_c_2984_);
v___x_2989_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2988_, v_a_2985_, v_a_2986_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg___boxed(lean_object* v_c_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2990_, v_a_2991_, v_a_2992_);
lean_dec_ref(v_a_2992_);
lean_dec(v_a_2991_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(lean_object* v_c_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2995_, v_a_2996_, v_a_3004_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___boxed(lean_object* v_c_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(v_c_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
lean_dec(v_a_3018_);
lean_dec_ref(v_a_3017_);
lean_dec(v_a_3016_);
lean_dec_ref(v_a_3015_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec(v_a_3009_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(lean_object* v_c_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v_p_3025_; lean_object* v___x_3026_; 
v_p_3025_ = lean_ctor_get(v_c_3021_, 0);
lean_inc_ref(v_p_3025_);
lean_dec_ref(v_c_3021_);
v___x_3026_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3025_, v_a_3022_, v_a_3023_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3046_; 
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3029_ = v___x_3026_;
v_isShared_3030_ = v_isSharedCheck_3046_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3026_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3046_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
uint8_t v___y_3032_; 
if (lean_obj_tag(v_a_3027_) == 1)
{
lean_object* v_val_3038_; lean_object* v___x_3039_; uint8_t v___x_3040_; 
v_val_3038_ = lean_ctor_get(v_a_3027_, 0);
lean_inc(v_val_3038_);
lean_dec_ref_known(v_a_3027_, 1);
v___x_3039_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_3040_ = l_instDecidableEqRat_decEq(v_val_3038_, v___x_3039_);
lean_dec(v_val_3038_);
if (v___x_3040_ == 0)
{
uint8_t v___x_3041_; 
v___x_3041_ = 1;
v___y_3032_ = v___x_3041_;
goto v___jp_3031_;
}
else
{
uint8_t v___x_3042_; 
v___x_3042_ = 0;
v___y_3032_ = v___x_3042_;
goto v___jp_3031_;
}
}
else
{
uint8_t v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
lean_del_object(v___x_3029_);
lean_dec(v_a_3027_);
v___x_3043_ = 2;
v___x_3044_ = lean_box(v___x_3043_);
v___x_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
return v___x_3045_;
}
v___jp_3031_:
{
uint8_t v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3036_; 
v___x_3033_ = l_Lean_Bool_toLBool(v___y_3032_);
v___x_3034_ = lean_box(v___x_3033_);
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 0, v___x_3034_);
v___x_3036_ = v___x_3029_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3034_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
v_a_3047_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_3026_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3026_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg___boxed(lean_object* v_c_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_3055_, v_a_3056_, v_a_3057_);
lean_dec_ref(v_a_3057_);
lean_dec(v_a_3056_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(lean_object* v_c_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_3060_, v_a_3061_, v_a_3069_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___boxed(lean_object* v_c_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(v_c_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_);
lean_dec(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec(v_a_3075_);
lean_dec(v_a_3074_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(lean_object* v_c_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_){
_start:
{
lean_object* v_p_3090_; lean_object* v___x_3091_; 
v_p_3090_ = lean_ctor_get(v_c_3086_, 0);
lean_inc_ref(v_p_3090_);
lean_dec_ref(v_c_3086_);
v___x_3091_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_3090_, v_a_3087_, v_a_3088_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3109_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3094_ = v___x_3091_;
v_isShared_3095_ = v_isSharedCheck_3109_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3091_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3109_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
if (lean_obj_tag(v_a_3092_) == 1)
{
lean_object* v_val_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; uint8_t v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3102_; 
v_val_3096_ = lean_ctor_get(v_a_3092_, 0);
lean_inc(v_val_3096_);
lean_dec_ref_known(v_a_3092_, 1);
v___x_3097_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_3098_ = l_instDecidableEqRat_decEq(v_val_3096_, v___x_3097_);
lean_dec(v_val_3096_);
v___x_3099_ = l_Lean_Bool_toLBool(v___x_3098_);
v___x_3100_ = lean_box(v___x_3099_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3100_);
v___x_3102_ = v___x_3094_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3100_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
else
{
uint8_t v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3107_; 
lean_dec(v_a_3092_);
v___x_3104_ = 2;
v___x_3105_ = lean_box(v___x_3104_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3105_);
v___x_3107_ = v___x_3094_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3105_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
v_a_3110_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3091_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3091_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg___boxed(lean_object* v_c_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_3118_, v_a_3119_, v_a_3120_);
lean_dec_ref(v_a_3120_);
lean_dec(v_a_3119_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(lean_object* v_c_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v___x_3135_; 
v___x_3135_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_3123_, v_a_3124_, v_a_3132_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___boxed(lean_object* v_c_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(v_c_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg(lean_object* v_p_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_){
_start:
{
if (lean_obj_tag(v_p_3149_) == 0)
{
lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3160_; 
v_isSharedCheck_3160_ = !lean_is_exclusive(v_p_3149_);
if (v_isSharedCheck_3160_ == 0)
{
lean_object* v_unused_3161_; 
v_unused_3161_ = lean_ctor_get(v_p_3149_, 0);
lean_dec(v_unused_3161_);
v___x_3154_ = v_p_3149_;
v_isShared_3155_ = v_isSharedCheck_3160_;
goto v_resetjp_3153_;
}
else
{
lean_dec(v_p_3149_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3160_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3156_; lean_object* v___x_3158_; 
v___x_3156_ = lean_box(0);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 0, v___x_3156_);
v___x_3158_ = v___x_3154_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3156_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
else
{
lean_object* v_k_3162_; lean_object* v_v_3163_; lean_object* v_p_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v_k_3162_ = lean_ctor_get(v_p_3149_, 0);
lean_inc(v_k_3162_);
v_v_3163_ = lean_ctor_get(v_p_3149_, 1);
lean_inc(v_v_3163_);
v_p_3164_ = lean_ctor_get(v_p_3149_, 2);
lean_inc_ref(v_p_3164_);
lean_dec_ref_known(v_p_3149_, 3);
v___x_3165_ = lean_box(0);
v___x_3166_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3150_, v_a_3151_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3192_; 
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3169_ = v___x_3166_;
v_isShared_3170_ = v_isSharedCheck_3192_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3166_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3192_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___y_3172_; lean_object* v_elimEqs_3187_; lean_object* v_size_3188_; uint8_t v___x_3189_; 
v_elimEqs_3187_ = lean_ctor_get(v_a_3167_, 9);
lean_inc_ref(v_elimEqs_3187_);
lean_dec(v_a_3167_);
v_size_3188_ = lean_ctor_get(v_elimEqs_3187_, 2);
v___x_3189_ = lean_nat_dec_lt(v_v_3163_, v_size_3188_);
if (v___x_3189_ == 0)
{
lean_object* v___x_3190_; 
lean_dec_ref(v_elimEqs_3187_);
v___x_3190_ = l_outOfBounds___redArg(v___x_3165_);
v___y_3172_ = v___x_3190_;
goto v___jp_3171_;
}
else
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3165_, v_elimEqs_3187_, v_v_3163_);
lean_dec_ref(v_elimEqs_3187_);
v___y_3172_ = v___x_3191_;
goto v___jp_3171_;
}
v___jp_3171_:
{
if (lean_obj_tag(v___y_3172_) == 1)
{
lean_object* v_val_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3185_; 
lean_dec_ref(v_p_3164_);
v_val_3173_ = lean_ctor_get(v___y_3172_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___y_3172_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3175_ = v___y_3172_;
v_isShared_3176_ = v_isSharedCheck_3185_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_val_3173_);
lean_dec(v___y_3172_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3185_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3180_; 
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v_v_3163_);
lean_ctor_set(v___x_3177_, 1, v_val_3173_);
v___x_3178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3178_, 0, v_k_3162_);
lean_ctor_set(v___x_3178_, 1, v___x_3177_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 0, v___x_3178_);
v___x_3180_ = v___x_3175_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3178_);
v___x_3180_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3182_; 
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 0, v___x_3180_);
v___x_3182_ = v___x_3169_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
else
{
lean_dec(v___y_3172_);
lean_del_object(v___x_3169_);
lean_dec(v_v_3163_);
lean_dec(v_k_3162_);
v_p_3149_ = v_p_3164_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec_ref(v_p_3164_);
lean_dec(v_v_3163_);
lean_dec(v_k_3162_);
v_a_3193_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3166_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3166_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg___boxed(lean_object* v_p_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_3201_, v_a_3202_, v_a_3203_);
lean_dec_ref(v_a_3203_);
lean_dec(v_a_3202_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst(lean_object* v_p_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_3206_, v_a_3207_, v_a_3215_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___boxed(lean_object* v_p_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_Int_Internal_Linear_Poly_findVarToSubst(v_p_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_);
lean_dec(v_a_3229_);
lean_dec_ref(v_a_3228_);
lean_dec(v_a_3227_);
lean_dec_ref(v_a_3226_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec(v_a_3220_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(lean_object* v_pred_3232_){
_start:
{
lean_object* v_c_u2081_3233_; lean_object* v_c_u2082_3234_; uint8_t v_left_3235_; lean_object* v_c_u2083_x3f_3236_; lean_object* v_p_3237_; lean_object* v_p_3238_; lean_object* v_a_3239_; lean_object* v_b_3240_; 
v_c_u2081_3233_ = lean_ctor_get(v_pred_3232_, 0);
v_c_u2082_3234_ = lean_ctor_get(v_pred_3232_, 1);
v_left_3235_ = lean_ctor_get_uint8(v_pred_3232_, sizeof(void*)*3);
v_c_u2083_x3f_3236_ = lean_ctor_get(v_pred_3232_, 2);
v_p_3237_ = lean_ctor_get(v_c_u2081_3233_, 0);
v_p_3238_ = lean_ctor_get(v_c_u2082_3234_, 0);
v_a_3239_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3237_);
v_b_3240_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3238_);
if (lean_obj_tag(v_c_u2083_x3f_3236_) == 0)
{
if (v_left_3235_ == 0)
{
lean_object* v___x_3241_; 
lean_dec(v_a_3239_);
v___x_3241_ = lean_nat_abs(v_b_3240_);
lean_dec(v_b_3240_);
return v___x_3241_;
}
else
{
lean_object* v___x_3242_; 
lean_dec(v_b_3240_);
v___x_3242_ = lean_nat_abs(v_a_3239_);
lean_dec(v_a_3239_);
return v___x_3242_;
}
}
else
{
lean_object* v_val_3243_; lean_object* v_d_3244_; lean_object* v_p_3245_; lean_object* v_c_3246_; 
v_val_3243_ = lean_ctor_get(v_c_u2083_x3f_3236_, 0);
v_d_3244_ = lean_ctor_get(v_val_3243_, 0);
v_p_3245_ = lean_ctor_get(v_val_3243_, 1);
v_c_3246_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_3245_);
if (v_left_3235_ == 0)
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
lean_dec(v_a_3239_);
v___x_3247_ = lean_int_mul(v_b_3240_, v_d_3244_);
v___x_3248_ = l_Int_gcd(v___x_3247_, v_c_3246_);
lean_dec(v_c_3246_);
v___x_3249_ = lean_nat_to_int(v___x_3248_);
v___x_3250_ = lean_int_ediv(v___x_3247_, v___x_3249_);
lean_dec(v___x_3249_);
lean_dec(v___x_3247_);
v___x_3251_ = l_Int_lcm(v_b_3240_, v___x_3250_);
lean_dec(v___x_3250_);
lean_dec(v_b_3240_);
return v___x_3251_;
}
else
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
lean_dec(v_b_3240_);
v___x_3252_ = lean_int_mul(v_a_3239_, v_d_3244_);
v___x_3253_ = l_Int_gcd(v___x_3252_, v_c_3246_);
lean_dec(v_c_3246_);
v___x_3254_ = lean_nat_to_int(v___x_3253_);
v___x_3255_ = lean_int_ediv(v___x_3252_, v___x_3254_);
lean_dec(v___x_3254_);
lean_dec(v___x_3252_);
v___x_3256_ = l_Int_lcm(v_a_3239_, v___x_3255_);
lean_dec(v___x_3255_);
lean_dec(v_a_3239_);
return v___x_3256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases___boxed(lean_object* v_pred_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(v_pred_3257_);
lean_dec_ref(v_pred_3257_);
return v_res_3258_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3260_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0));
v___x_3261_ = l_Lean_stringToMessageData(v___x_3260_);
return v___x_3261_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3265_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3));
v___x_3266_ = l_Lean_MessageData_ofFormat(v___x_3265_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(lean_object* v_pred_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v_c_u2081_3271_; lean_object* v_c_u2082_3272_; lean_object* v_c_u2083_x3f_3273_; lean_object* v___x_3274_; 
v_c_u2081_3271_ = lean_ctor_get(v_pred_3267_, 0);
lean_inc_ref(v_c_u2081_3271_);
v_c_u2082_3272_ = lean_ctor_get(v_pred_3267_, 1);
lean_inc_ref(v_c_u2082_3272_);
v_c_u2083_x3f_3273_ = lean_ctor_get(v_pred_3267_, 2);
lean_inc(v_c_u2083_x3f_3273_);
lean_dec_ref(v_pred_3267_);
v___x_3274_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3271_, v_a_3268_, v_a_3269_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v___x_3276_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3272_, v_a_3268_, v_a_3269_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3295_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3279_ = v___x_3276_;
v_isShared_3280_ = v_isSharedCheck_3295_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3276_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3295_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v_____do__lift_3282_; 
if (lean_obj_tag(v_c_u2083_x3f_3273_) == 1)
{
lean_object* v_val_3291_; lean_object* v___x_3292_; 
v_val_3291_ = lean_ctor_get(v_c_u2083_x3f_3273_, 0);
lean_inc(v_val_3291_);
lean_dec_ref_known(v_c_u2083_x3f_3273_, 1);
v___x_3292_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_val_3291_, v_a_3268_, v_a_3269_);
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v_a_3293_; 
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
lean_inc(v_a_3293_);
lean_dec_ref_known(v___x_3292_, 1);
v_____do__lift_3282_ = v_a_3293_;
goto v___jp_3281_;
}
else
{
lean_del_object(v___x_3279_);
lean_dec(v_a_3277_);
lean_dec(v_a_3275_);
return v___x_3292_;
}
}
else
{
lean_object* v___x_3294_; 
lean_dec(v_c_u2083_x3f_3273_);
v___x_3294_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4);
v_____do__lift_3282_ = v___x_3294_;
goto v___jp_3281_;
}
v___jp_3281_:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3289_; 
v___x_3283_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3284_, 0, v_a_3275_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
lean_ctor_set(v___x_3285_, 1, v_a_3277_);
v___x_3286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3285_);
lean_ctor_set(v___x_3286_, 1, v___x_3283_);
v___x_3287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3286_);
lean_ctor_set(v___x_3287_, 1, v_____do__lift_3282_);
if (v_isShared_3280_ == 0)
{
lean_ctor_set(v___x_3279_, 0, v___x_3287_);
v___x_3289_ = v___x_3279_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3287_);
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
else
{
lean_dec(v_a_3275_);
lean_dec(v_c_u2083_x3f_3273_);
return v___x_3276_;
}
}
else
{
lean_dec(v_c_u2083_x3f_3273_);
lean_dec_ref(v_c_u2082_3272_);
return v___x_3274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___boxed(lean_object* v_pred_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_3296_, v_a_3297_, v_a_3298_);
lean_dec_ref(v_a_3298_);
lean_dec(v_a_3297_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(lean_object* v_pred_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_3301_, v_a_3302_, v_a_3310_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___boxed(lean_object* v_pred_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(v_pred_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_);
lean_dec(v_a_3324_);
lean_dec_ref(v_a_3323_);
lean_dec(v_a_3322_);
lean_dec_ref(v_a_3321_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
lean_dec(v_a_3318_);
lean_dec_ref(v_a_3317_);
lean_dec(v_a_3316_);
lean_dec(v_a_3315_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(lean_object* v_h_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_){
_start:
{
switch(lean_obj_tag(v_h_3327_))
{
case 0:
{
lean_object* v_c_3331_; lean_object* v___x_3332_; 
v_c_3331_ = lean_ctor_get(v_h_3327_, 0);
lean_inc_ref(v_c_3331_);
lean_dec_ref_known(v_h_3327_, 1);
v___x_3332_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_3331_, v_a_3328_, v_a_3329_);
return v___x_3332_;
}
case 1:
{
lean_object* v_c_3333_; lean_object* v___x_3334_; 
v_c_3333_ = lean_ctor_get(v_h_3327_, 0);
lean_inc_ref(v_c_3333_);
lean_dec_ref_known(v_h_3327_, 1);
v___x_3334_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3333_, v_a_3328_, v_a_3329_);
return v___x_3334_;
}
case 2:
{
lean_object* v_c_3335_; lean_object* v___x_3336_; 
v_c_3335_ = lean_ctor_get(v_h_3327_, 0);
lean_inc_ref(v_c_3335_);
lean_dec_ref_known(v_h_3327_, 1);
v___x_3336_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_3335_, v_a_3328_, v_a_3329_);
return v___x_3336_;
}
case 3:
{
lean_object* v_c_3337_; lean_object* v___x_3338_; 
v_c_3337_ = lean_ctor_get(v_h_3327_, 0);
lean_inc_ref(v_c_3337_);
lean_dec_ref_known(v_h_3327_, 1);
v___x_3338_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_3337_, v_a_3328_, v_a_3329_);
return v___x_3338_;
}
default: 
{
lean_object* v_c_u2081_3339_; lean_object* v_c_u2082_3340_; lean_object* v_c_u2083_3341_; lean_object* v___x_3342_; 
v_c_u2081_3339_ = lean_ctor_get(v_h_3327_, 0);
lean_inc_ref(v_c_u2081_3339_);
v_c_u2082_3340_ = lean_ctor_get(v_h_3327_, 1);
lean_inc_ref(v_c_u2082_3340_);
v_c_u2083_3341_ = lean_ctor_get(v_h_3327_, 2);
lean_inc_ref(v_c_u2083_3341_);
lean_dec_ref_known(v_h_3327_, 3);
v___x_3342_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3339_, v_a_3328_, v_a_3329_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3344_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_a_3343_);
lean_dec_ref_known(v___x_3342_, 1);
v___x_3344_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3340_, v_a_3328_, v_a_3329_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; lean_object* v___x_3346_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_a_3345_);
lean_dec_ref_known(v___x_3344_, 1);
v___x_3346_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2083_3341_, v_a_3328_, v_a_3329_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3359_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3349_ = v___x_3346_;
v_isShared_3350_ = v_isSharedCheck_3359_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3346_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3359_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3357_; 
v___x_3351_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3352_, 0, v_a_3343_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
v___x_3353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
lean_ctor_set(v___x_3353_, 1, v_a_3345_);
v___x_3354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
lean_ctor_set(v___x_3354_, 1, v___x_3351_);
v___x_3355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
lean_ctor_set(v___x_3355_, 1, v_a_3347_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 0, v___x_3355_);
v___x_3357_ = v___x_3349_;
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
}
else
{
lean_dec(v_a_3345_);
lean_dec(v_a_3343_);
return v___x_3346_;
}
}
else
{
lean_dec(v_a_3343_);
lean_dec_ref(v_c_u2083_3341_);
return v___x_3344_;
}
}
else
{
lean_dec_ref(v_c_u2083_3341_);
lean_dec_ref(v_c_u2082_3340_);
return v___x_3342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg___boxed(lean_object* v_h_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3360_, v_a_3361_, v_a_3362_);
lean_dec_ref(v_a_3362_);
lean_dec(v_a_3361_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(lean_object* v_h_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_){
_start:
{
lean_object* v___x_3377_; 
v___x_3377_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3365_, v_a_3366_, v_a_3374_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___boxed(lean_object* v_h_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(v_h_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
lean_dec(v_a_3386_);
lean_dec_ref(v_a_3385_);
lean_dec(v_a_3384_);
lean_dec_ref(v_a_3383_);
lean_dec(v_a_3382_);
lean_dec_ref(v_a_3381_);
lean_dec(v_a_3380_);
lean_dec(v_a_3379_);
return v_res_3390_;
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
