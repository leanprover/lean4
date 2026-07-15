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
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
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
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
extern lean_object* l_instInhabitedRat;
lean_object* l_Rat_mul(lean_object*, lean_object*);
uint8_t l_Rat_instDecidableLe(lean_object*, lean_object*);
uint8_t l_Lean_Bool_toLBool(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Int_decidableDvd(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_109_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; uint8_t v___x_114_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_a_113_);
v___x_114_ = lean_unbox(v_a_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
lean_dec_ref_known(v___x_112_, 1);
v___x_115_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_109_, v_a_110_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_129_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_129_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_129_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_129_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v_conflict_x3f_120_; 
v_conflict_x3f_120_ = lean_ctor_get(v_a_116_, 15);
lean_inc(v_conflict_x3f_120_);
lean_dec(v_a_116_);
if (lean_obj_tag(v_conflict_x3f_120_) == 0)
{
lean_object* v___x_122_; 
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v_a_113_);
v___x_122_ = v___x_118_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_a_113_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
else
{
uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
lean_dec_ref_known(v_conflict_x3f_120_, 1);
lean_dec(v_a_113_);
v___x_124_ = 1;
v___x_125_ = lean_box(v___x_124_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 0, v___x_125_);
v___x_127_ = v___x_118_;
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
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
lean_dec(v_a_113_);
v_a_130_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_115_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_115_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
else
{
lean_dec(v_a_113_);
return v___x_112_;
}
}
else
{
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg___boxed(lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_138_, v_a_139_);
lean_dec_ref(v_a_139_);
lean_dec(v_a_138_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_142_, v_a_150_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___boxed(lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec(v_a_155_);
lean_dec(v_a_154_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVar___boxed(lean_object* v_e_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_00___x40___internal___hyg_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = lean_grind_cutsat_mk_var(v_e_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_191_, v_a_192_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_203_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_203_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v_vars_199_; lean_object* v___x_201_; 
v_vars_199_ = lean_ctor_get(v_a_195_, 0);
lean_inc_ref(v_vars_199_);
lean_dec(v_a_195_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v_vars_199_);
v___x_201_ = v___x_197_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_vars_199_);
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
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
v_a_204_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_194_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_194_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg___boxed(lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_212_, v_a_213_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars(lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_216_, v_a_224_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVars___boxed(lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars(v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec(v_a_233_);
lean_dec_ref(v_a_232_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
lean_dec(v_a_228_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object* v_x_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_241_, v_a_242_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_261_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_261_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_261_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_261_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v_vars_249_; lean_object* v_size_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v_vars_249_ = lean_ctor_get(v_a_245_, 0);
lean_inc_ref(v_vars_249_);
lean_dec(v_a_245_);
v_size_250_ = lean_ctor_get(v_vars_249_, 2);
v___x_251_ = l_Lean_instInhabitedExpr;
v___x_252_ = lean_nat_dec_lt(v_x_240_, v_size_250_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_255_; 
lean_dec_ref(v_vars_249_);
v___x_253_ = l_outOfBounds___redArg(v___x_251_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_253_);
v___x_255_ = v___x_247_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
else
{
lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_257_ = l_Lean_PersistentArray_get_x21___redArg(v___x_251_, v_vars_249_, v_x_240_);
lean_dec_ref(v_vars_249_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_257_);
v___x_259_ = v___x_247_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
v_a_262_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_244_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_244_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg___boxed(lean_object* v_x_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_270_, v_a_271_, v_a_272_);
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_dec(v_x_270_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar(lean_object* v_x_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_275_, v_a_276_, v_a_284_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___boxed(lean_object* v_x_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar(v_x_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec(v_a_289_);
lean_dec(v_x_288_);
return v_res_300_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_301_, lean_object* v_i_302_, lean_object* v_k_303_){
_start:
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = lean_array_get_size(v_keys_301_);
v___x_305_ = lean_nat_dec_lt(v_i_302_, v___x_304_);
if (v___x_305_ == 0)
{
lean_dec(v_i_302_);
return v___x_305_;
}
else
{
lean_object* v_k_x27_306_; size_t v___x_307_; size_t v___x_308_; uint8_t v___x_309_; 
v_k_x27_306_ = lean_array_fget_borrowed(v_keys_301_, v_i_302_);
v___x_307_ = lean_ptr_addr(v_k_303_);
v___x_308_ = lean_ptr_addr(v_k_x27_306_);
v___x_309_ = lean_usize_dec_eq(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_unsigned_to_nat(1u);
v___x_311_ = lean_nat_add(v_i_302_, v___x_310_);
lean_dec(v_i_302_);
v_i_302_ = v___x_311_;
goto _start;
}
else
{
lean_dec(v_i_302_);
return v___x_309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_313_, lean_object* v_i_314_, lean_object* v_k_315_){
_start:
{
uint8_t v_res_316_; lean_object* v_r_317_; 
v_res_316_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_313_, v_i_314_, v_k_315_);
lean_dec_ref(v_k_315_);
lean_dec_ref(v_keys_313_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(lean_object* v_x_318_, size_t v_x_319_, lean_object* v_x_320_){
_start:
{
if (lean_obj_tag(v_x_318_) == 0)
{
lean_object* v_es_321_; lean_object* v___x_322_; size_t v___x_323_; size_t v___x_324_; lean_object* v_j_325_; lean_object* v___x_326_; 
v_es_321_ = lean_ctor_get(v_x_318_, 0);
v___x_322_ = lean_box(2);
v___x_323_ = ((size_t)31ULL);
v___x_324_ = lean_usize_land(v_x_319_, v___x_323_);
v_j_325_ = lean_usize_to_nat(v___x_324_);
v___x_326_ = lean_array_get_borrowed(v___x_322_, v_es_321_, v_j_325_);
lean_dec(v_j_325_);
switch(lean_obj_tag(v___x_326_))
{
case 0:
{
lean_object* v_key_327_; size_t v___x_328_; size_t v___x_329_; uint8_t v___x_330_; 
v_key_327_ = lean_ctor_get(v___x_326_, 0);
v___x_328_ = lean_ptr_addr(v_x_320_);
v___x_329_ = lean_ptr_addr(v_key_327_);
v___x_330_ = lean_usize_dec_eq(v___x_328_, v___x_329_);
return v___x_330_;
}
case 1:
{
lean_object* v_node_331_; size_t v___x_332_; size_t v___x_333_; 
v_node_331_ = lean_ctor_get(v___x_326_, 0);
v___x_332_ = ((size_t)5ULL);
v___x_333_ = lean_usize_shift_right(v_x_319_, v___x_332_);
v_x_318_ = v_node_331_;
v_x_319_ = v___x_333_;
goto _start;
}
default: 
{
uint8_t v___x_335_; 
v___x_335_ = 0;
return v___x_335_;
}
}
}
else
{
lean_object* v_ks_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v_ks_336_ = lean_ctor_get(v_x_318_, 0);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_ks_336_, v___x_337_, v_x_320_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___boxed(lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
size_t v_x_876__boxed_342_; uint8_t v_res_343_; lean_object* v_r_344_; 
v_x_876__boxed_342_ = lean_unbox_usize(v_x_340_);
lean_dec(v_x_340_);
v_res_343_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_339_, v_x_876__boxed_342_, v_x_341_);
lean_dec_ref(v_x_341_);
lean_dec_ref(v_x_339_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; uint64_t v___x_350_; size_t v___x_351_; uint8_t v___x_352_; 
v___x_347_ = lean_ptr_addr(v_x_346_);
v___x_348_ = ((size_t)3ULL);
v___x_349_ = lean_usize_shift_right(v___x_347_, v___x_348_);
v___x_350_ = lean_usize_to_uint64(v___x_349_);
v___x_351_ = lean_uint64_to_usize(v___x_350_);
v___x_352_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_345_, v___x_351_, v_x_346_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg___boxed(lean_object* v_x_353_, lean_object* v_x_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_353_, v_x_354_);
lean_dec_ref(v_x_354_);
lean_dec_ref(v_x_353_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(lean_object* v_e_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_358_, v_a_359_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_372_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_372_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_372_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_372_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v_varMap_366_; uint8_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v_varMap_366_ = lean_ctor_get(v_a_362_, 1);
lean_inc_ref(v_varMap_366_);
lean_dec(v_a_362_);
v___x_367_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_varMap_366_, v_e_357_);
lean_dec_ref(v_varMap_366_);
v___x_368_ = lean_box(v___x_367_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_368_);
v___x_370_ = v___x_364_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
v_a_373_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_361_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_361_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg___boxed(lean_object* v_e_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_381_, v_a_382_, v_a_383_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_e_381_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar(lean_object* v_e_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_386_, v_a_387_, v_a_395_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___boxed(lean_object* v_e_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar(v_e_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec(v_a_400_);
lean_dec_ref(v_e_399_);
return v_res_411_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(lean_object* v_00_u03b2_412_, lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
uint8_t v___x_415_; 
v___x_415_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_413_, v_x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___boxed(lean_object* v_00_u03b2_416_, lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
uint8_t v_res_419_; lean_object* v_r_420_; 
v_res_419_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(v_00_u03b2_416_, v_x_417_, v_x_418_);
lean_dec_ref(v_x_418_);
lean_dec_ref(v_x_417_);
v_r_420_ = lean_box(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(lean_object* v_00_u03b2_421_, lean_object* v_x_422_, size_t v_x_423_, lean_object* v_x_424_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_422_, v_x_423_, v_x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_426_, lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
size_t v_x_993__boxed_430_; uint8_t v_res_431_; lean_object* v_r_432_; 
v_x_993__boxed_430_ = lean_unbox_usize(v_x_428_);
lean_dec(v_x_428_);
v_res_431_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(v_00_u03b2_426_, v_x_427_, v_x_993__boxed_430_, v_x_429_);
lean_dec_ref(v_x_429_);
lean_dec_ref(v_x_427_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_433_, lean_object* v_keys_434_, lean_object* v_vals_435_, lean_object* v_heq_436_, lean_object* v_i_437_, lean_object* v_k_438_){
_start:
{
uint8_t v___x_439_; 
v___x_439_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_434_, v_i_437_, v_k_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_440_, lean_object* v_keys_441_, lean_object* v_vals_442_, lean_object* v_heq_443_, lean_object* v_i_444_, lean_object* v_k_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(v_00_u03b2_440_, v_keys_441_, v_vals_442_, v_heq_443_, v_i_444_, v_k_445_);
lean_dec_ref(v_k_445_);
lean_dec_ref(v_vals_442_);
lean_dec_ref(v_keys_441_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(lean_object* v_e_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_448_, v_a_449_, v_a_450_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg___boxed(lean_object* v_e_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(v_e_453_, v_a_454_, v_a_455_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_e_453_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(lean_object* v_e_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_458_, v_a_459_, v_a_467_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___boxed(lean_object* v_e_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(v_e_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_e_471_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(lean_object* v_x_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_511_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_511_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_511_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_511_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___y_494_; lean_object* v_elimEqs_505_; lean_object* v_size_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_elimEqs_505_ = lean_ctor_get(v_a_489_, 10);
lean_inc_ref(v_elimEqs_505_);
lean_dec(v_a_489_);
v_size_506_ = lean_ctor_get(v_elimEqs_505_, 2);
v___x_507_ = lean_box(0);
v___x_508_ = lean_nat_dec_lt(v_x_484_, v_size_506_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
lean_dec_ref(v_elimEqs_505_);
v___x_509_ = l_outOfBounds___redArg(v___x_507_);
v___y_494_ = v___x_509_;
goto v___jp_493_;
}
else
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_PersistentArray_get_x21___redArg(v___x_507_, v_elimEqs_505_, v_x_484_);
lean_dec_ref(v_elimEqs_505_);
v___y_494_ = v___x_510_;
goto v___jp_493_;
}
v___jp_493_:
{
if (lean_obj_tag(v___y_494_) == 0)
{
uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_495_ = 0;
v___x_496_ = lean_box(v___x_495_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_496_);
v___x_498_ = v___x_491_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
else
{
uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
lean_dec_ref_known(v___y_494_, 1);
v___x_500_ = 1;
v___x_501_ = lean_box(v___x_500_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_501_);
v___x_503_ = v___x_491_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
v_a_512_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_488_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_488_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg___boxed(lean_object* v_x_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_520_, v_a_521_, v_a_522_);
lean_dec_ref(v_a_522_);
lean_dec(v_a_521_);
lean_dec(v_x_520_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated(lean_object* v_x_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_525_, v_a_526_, v_a_534_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___boxed(lean_object* v_x_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated(v_x_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec(v_a_539_);
lean_dec(v_x_538_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_assert___boxed(lean_object* v_c_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_00___x40___internal___hyg_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = lean_grind_cutsat_assert_eq(v_c_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(lean_object* v_x_576_, lean_object* v_s_577_){
_start:
{
lean_object* v_vars_578_; lean_object* v_varMap_579_; lean_object* v_vars_x27_580_; lean_object* v_varMap_x27_581_; lean_object* v_natToIntMap_582_; lean_object* v_natDef_583_; lean_object* v_dvds_584_; lean_object* v_lowers_585_; lean_object* v_uppers_586_; lean_object* v_diseqs_587_; lean_object* v_elimEqs_588_; lean_object* v_elimStack_589_; lean_object* v_occurs_590_; lean_object* v_assignment_591_; lean_object* v_nextCnstrId_592_; uint8_t v_caseSplits_593_; lean_object* v_conflict_x3f_594_; lean_object* v_diseqSplits_595_; lean_object* v_divMod_596_; lean_object* v_toIntIds_597_; lean_object* v_toIntInfos_598_; lean_object* v_toIntTermMap_599_; lean_object* v_toIntVarMap_600_; uint8_t v_usedCommRing_601_; lean_object* v_nonlinearOccs_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_610_; 
v_vars_578_ = lean_ctor_get(v_s_577_, 0);
v_varMap_579_ = lean_ctor_get(v_s_577_, 1);
v_vars_x27_580_ = lean_ctor_get(v_s_577_, 2);
v_varMap_x27_581_ = lean_ctor_get(v_s_577_, 3);
v_natToIntMap_582_ = lean_ctor_get(v_s_577_, 4);
v_natDef_583_ = lean_ctor_get(v_s_577_, 5);
v_dvds_584_ = lean_ctor_get(v_s_577_, 6);
v_lowers_585_ = lean_ctor_get(v_s_577_, 7);
v_uppers_586_ = lean_ctor_get(v_s_577_, 8);
v_diseqs_587_ = lean_ctor_get(v_s_577_, 9);
v_elimEqs_588_ = lean_ctor_get(v_s_577_, 10);
v_elimStack_589_ = lean_ctor_get(v_s_577_, 11);
v_occurs_590_ = lean_ctor_get(v_s_577_, 12);
v_assignment_591_ = lean_ctor_get(v_s_577_, 13);
v_nextCnstrId_592_ = lean_ctor_get(v_s_577_, 14);
v_caseSplits_593_ = lean_ctor_get_uint8(v_s_577_, sizeof(void*)*23);
v_conflict_x3f_594_ = lean_ctor_get(v_s_577_, 15);
v_diseqSplits_595_ = lean_ctor_get(v_s_577_, 16);
v_divMod_596_ = lean_ctor_get(v_s_577_, 17);
v_toIntIds_597_ = lean_ctor_get(v_s_577_, 18);
v_toIntInfos_598_ = lean_ctor_get(v_s_577_, 19);
v_toIntTermMap_599_ = lean_ctor_get(v_s_577_, 20);
v_toIntVarMap_600_ = lean_ctor_get(v_s_577_, 21);
v_usedCommRing_601_ = lean_ctor_get_uint8(v_s_577_, sizeof(void*)*23 + 1);
v_nonlinearOccs_602_ = lean_ctor_get(v_s_577_, 22);
v_isSharedCheck_610_ = !lean_is_exclusive(v_s_577_);
if (v_isSharedCheck_610_ == 0)
{
v___x_604_ = v_s_577_;
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_nonlinearOccs_602_);
lean_inc(v_toIntVarMap_600_);
lean_inc(v_toIntTermMap_599_);
lean_inc(v_toIntInfos_598_);
lean_inc(v_toIntIds_597_);
lean_inc(v_divMod_596_);
lean_inc(v_diseqSplits_595_);
lean_inc(v_conflict_x3f_594_);
lean_inc(v_nextCnstrId_592_);
lean_inc(v_assignment_591_);
lean_inc(v_occurs_590_);
lean_inc(v_elimStack_589_);
lean_inc(v_elimEqs_588_);
lean_inc(v_diseqs_587_);
lean_inc(v_uppers_586_);
lean_inc(v_lowers_585_);
lean_inc(v_dvds_584_);
lean_inc(v_natDef_583_);
lean_inc(v_natToIntMap_582_);
lean_inc(v_varMap_x27_581_);
lean_inc(v_vars_x27_580_);
lean_inc(v_varMap_579_);
lean_inc(v_vars_578_);
lean_dec(v_s_577_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_591_, v_x_576_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 13, v___x_606_);
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_vars_578_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_varMap_579_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_vars_x27_580_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_varMap_x27_581_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v_natToIntMap_582_);
lean_ctor_set(v_reuseFailAlloc_609_, 5, v_natDef_583_);
lean_ctor_set(v_reuseFailAlloc_609_, 6, v_dvds_584_);
lean_ctor_set(v_reuseFailAlloc_609_, 7, v_lowers_585_);
lean_ctor_set(v_reuseFailAlloc_609_, 8, v_uppers_586_);
lean_ctor_set(v_reuseFailAlloc_609_, 9, v_diseqs_587_);
lean_ctor_set(v_reuseFailAlloc_609_, 10, v_elimEqs_588_);
lean_ctor_set(v_reuseFailAlloc_609_, 11, v_elimStack_589_);
lean_ctor_set(v_reuseFailAlloc_609_, 12, v_occurs_590_);
lean_ctor_set(v_reuseFailAlloc_609_, 13, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_609_, 14, v_nextCnstrId_592_);
lean_ctor_set(v_reuseFailAlloc_609_, 15, v_conflict_x3f_594_);
lean_ctor_set(v_reuseFailAlloc_609_, 16, v_diseqSplits_595_);
lean_ctor_set(v_reuseFailAlloc_609_, 17, v_divMod_596_);
lean_ctor_set(v_reuseFailAlloc_609_, 18, v_toIntIds_597_);
lean_ctor_set(v_reuseFailAlloc_609_, 19, v_toIntInfos_598_);
lean_ctor_set(v_reuseFailAlloc_609_, 20, v_toIntTermMap_599_);
lean_ctor_set(v_reuseFailAlloc_609_, 21, v_toIntVarMap_600_);
lean_ctor_set(v_reuseFailAlloc_609_, 22, v_nonlinearOccs_602_);
lean_ctor_set_uint8(v_reuseFailAlloc_609_, sizeof(void*)*23, v_caseSplits_593_);
lean_ctor_set_uint8(v_reuseFailAlloc_609_, sizeof(void*)*23 + 1, v_usedCommRing_601_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_x_611_, lean_object* v_s_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(v_x_611_, v_s_612_);
lean_dec(v_x_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object* v_x_614_, lean_object* v_a_615_){
_start:
{
lean_object* v___f_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___f_617_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_617_, 0, v_x_614_);
v___x_618_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_619_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_618_, v___f_617_, v_a_615_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___boxed(lean_object* v_x_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_620_, v_a_621_);
lean_dec(v_a_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(lean_object* v_x_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_624_, v_a_625_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___boxed(lean_object* v_x_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(v_x_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec(v_a_638_);
return v_res_649_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__0));
v___x_652_ = l_Lean_stringToMessageData(v___x_651_);
return v___x_652_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_nat_to_int(v___x_653_);
return v___x_654_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__3));
v___x_657_ = l_Lean_stringToMessageData(v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(lean_object* v_r_658_, lean_object* v_p_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
if (lean_obj_tag(v_p_659_) == 0)
{
lean_object* v_k_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_681_; 
v_k_663_ = lean_ctor_get(v_p_659_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v_p_659_);
if (v_isSharedCheck_681_ == 0)
{
v___x_665_ = v_p_659_;
v_isShared_666_ = v_isSharedCheck_681_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_k_663_);
lean_dec(v_p_659_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_681_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_667_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_668_ = lean_int_dec_eq(v_k_663_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_669_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_670_, 0, v_r_658_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = l_Int_repr(v_k_663_);
lean_dec(v_k_663_);
if (v_isShared_666_ == 0)
{
lean_ctor_set_tag(v___x_665_, 3);
lean_ctor_set(v___x_665_, 0, v___x_671_);
v___x_673_ = v___x_665_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_677_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = l_Lean_MessageData_ofFormat(v___x_673_);
v___x_675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_670_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
else
{
lean_object* v___x_679_; 
lean_dec(v_k_663_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v_r_658_);
v___x_679_ = v___x_665_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_r_658_);
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
else
{
lean_object* v_k_682_; lean_object* v_v_683_; lean_object* v_p_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v_k_682_ = lean_ctor_get(v_p_659_, 0);
lean_inc(v_k_682_);
v_v_683_ = lean_ctor_get(v_p_659_, 1);
lean_inc(v_v_683_);
v_p_684_ = lean_ctor_get(v_p_659_, 2);
lean_inc_ref(v_p_684_);
lean_dec_ref_known(v_p_659_, 3);
v___x_685_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_686_ = lean_int_dec_eq(v_k_682_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_683_, v_a_660_, v_a_661_);
lean_dec(v_v_683_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
v___x_689_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_690_, 0, v_r_658_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = l_Int_repr(v_k_682_);
lean_dec(v_k_682_);
v___x_692_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
v___x_693_ = l_Lean_MessageData_ofFormat(v___x_692_);
v___x_694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_690_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4);
v___x_696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_694_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_688_);
v___x_698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_696_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v_r_658_ = v___x_698_;
v_p_659_ = v_p_684_;
goto _start;
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec_ref(v_p_684_);
lean_dec(v_k_682_);
lean_dec_ref(v_r_658_);
v_a_700_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_687_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_687_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v___x_708_; 
lean_dec(v_k_682_);
v___x_708_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_683_, v_a_660_, v_a_661_);
lean_dec(v_v_683_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v___x_710_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v_r_658_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_709_);
v___x_713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v_r_658_ = v___x_713_;
v_p_659_ = v_p_684_;
goto _start;
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec_ref(v_p_684_);
lean_dec_ref(v_r_658_);
v_a_715_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_708_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_708_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___boxed(lean_object* v_r_723_, lean_object* v_p_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v_r_723_, v_p_724_, v_a_725_, v_a_726_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(lean_object* v_r_729_, lean_object* v_p_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v_r_729_, v_p_730_, v_a_731_, v_a_739_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___boxed(lean_object* v_r_743_, lean_object* v_p_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(v_r_743_, v_p_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec(v_a_745_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___redArg(lean_object* v_p_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
if (lean_obj_tag(v_p_757_) == 0)
{
lean_object* v_k_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_771_; 
v_k_761_ = lean_ctor_get(v_p_757_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v_p_757_);
if (v_isSharedCheck_771_ == 0)
{
v___x_763_ = v_p_757_;
v_isShared_764_ = v_isSharedCheck_771_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_k_761_);
lean_dec(v_p_757_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_771_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_765_ = l_Int_repr(v_k_761_);
lean_dec(v_k_761_);
if (v_isShared_764_ == 0)
{
lean_ctor_set_tag(v___x_763_, 3);
lean_ctor_set(v___x_763_, 0, v___x_765_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_765_);
v___x_767_ = v_reuseFailAlloc_770_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = l_Lean_MessageData_ofFormat(v___x_767_);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
return v___x_769_;
}
}
}
else
{
lean_object* v_k_772_; lean_object* v_v_773_; lean_object* v_p_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v_k_772_ = lean_ctor_get(v_p_757_, 0);
lean_inc(v_k_772_);
v_v_773_ = lean_ctor_get(v_p_757_, 1);
lean_inc(v_v_773_);
v_p_774_ = lean_ctor_get(v_p_757_, 2);
lean_inc_ref(v_p_774_);
lean_dec_ref_known(v_p_757_, 3);
v___x_775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_776_ = lean_int_dec_eq(v_k_772_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_773_, v_a_758_, v_a_759_);
lean_dec(v_v_773_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v___x_777_, 1);
v___x_779_ = l_Int_repr(v_k_772_);
lean_dec(v_k_772_);
v___x_780_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
v___x_781_ = l_Lean_MessageData_ofFormat(v___x_780_);
v___x_782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4);
v___x_783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_778_);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v___x_785_, v_p_774_, v_a_758_, v_a_759_);
return v___x_786_;
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec_ref(v_p_774_);
lean_dec(v_k_772_);
v_a_787_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_777_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_777_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v___x_795_; 
lean_dec(v_k_772_);
v___x_795_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_773_, v_a_758_, v_a_759_);
lean_dec(v_v_773_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_795_, 1);
v___x_797_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_796_);
v___x_798_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v___x_797_, v_p_774_, v_a_758_, v_a_759_);
return v___x_798_;
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v_p_774_);
v_a_799_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_795_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_795_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___redArg___boxed(lean_object* v_p_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_807_, v_a_808_, v_a_809_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp(lean_object* v_p_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_812_, v_a_813_, v_a_821_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___boxed(lean_object* v_p_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Int_Internal_Linear_Poly_pp(v_p_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec(v_a_826_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0(lean_object* v_a_838_, lean_object* v___x_839_, lean_object* v_x_840_){
_start:
{
lean_object* v_size_841_; uint8_t v___x_842_; 
v_size_841_ = lean_ctor_get(v_a_838_, 2);
v___x_842_ = lean_nat_dec_lt(v_x_840_, v_size_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; 
v___x_843_ = l_outOfBounds___redArg(v___x_839_);
return v___x_843_;
}
else
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_PersistentArray_get_x21___redArg(v___x_839_, v_a_838_, v_x_840_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed(lean_object* v_a_845_, lean_object* v___x_846_, lean_object* v_x_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0(v_a_845_, v___x_846_, v_x_847_);
lean_dec(v_x_847_);
lean_dec_ref(v___x_846_);
lean_dec_ref(v_a_845_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(lean_object* v_p_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_850_, v_a_851_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; lean_object* v___f_856_; lean_object* v___x_857_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v___x_855_ = l_Lean_instInhabitedExpr;
v___f_856_ = lean_alloc_closure((void*)(l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_856_, 0, v_a_854_);
lean_closure_set(v___f_856_, 1, v___x_855_);
v___x_857_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_856_, v_p_849_);
return v___x_857_;
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec_ref(v_p_849_);
v_a_858_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_853_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_853_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___boxed(lean_object* v_p_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_866_, v_a_867_, v_a_868_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27(lean_object* v_p_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_871_, v_a_872_, v_a_880_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___boxed(lean_object* v_p_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Int_Internal_Linear_Poly_denoteExpr_x27(v_p_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
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
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object* v_c_897_){
_start:
{
lean_object* v_p_898_; 
v_p_898_ = lean_ctor_get(v_c_897_, 1);
if (lean_obj_tag(v_p_898_) == 0)
{
lean_object* v_d_899_; lean_object* v_k_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v_d_899_ = lean_ctor_get(v_c_897_, 0);
v_k_900_ = lean_ctor_get(v_p_898_, 0);
v___x_901_ = lean_int_emod(v_k_900_, v_d_899_);
v___x_902_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_903_ = lean_int_dec_eq(v___x_901_, v___x_902_);
lean_dec(v___x_901_);
return v___x_903_;
}
else
{
lean_object* v_d_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v_d_904_ = lean_ctor_get(v_c_897_, 0);
v___x_905_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_906_ = lean_int_dec_eq(v_d_904_, v___x_905_);
return v___x_906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial___boxed(lean_object* v_c_907_){
_start:
{
uint8_t v_res_908_; lean_object* v_r_909_; 
v_res_908_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_c_907_);
lean_dec_ref(v_c_907_);
v_r_909_ = lean_box(v_res_908_);
return v_r_909_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0));
v___x_912_ = l_Lean_stringToMessageData(v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object* v_c_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_d_917_; lean_object* v_p_918_; lean_object* v___x_919_; 
v_d_917_ = lean_ctor_get(v_c_913_, 0);
lean_inc(v_d_917_);
v_p_918_ = lean_ctor_get(v_c_913_, 1);
lean_inc_ref(v_p_918_);
lean_dec_ref(v_c_913_);
v___x_919_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_918_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_933_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_933_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_933_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_933_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_924_ = l_Int_repr(v_d_917_);
lean_dec(v_d_917_);
v___x_925_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
v___x_926_ = l_Lean_MessageData_ofFormat(v___x_925_);
v___x_927_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1);
v___x_928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v_a_920_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_929_);
v___x_931_ = v___x_922_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
else
{
lean_dec(v_d_917_);
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___boxed(lean_object* v_c_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_934_, v_a_935_, v_a_936_);
lean_dec_ref(v_a_936_);
lean_dec(v_a_935_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(lean_object* v_c_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_939_, v_a_940_, v_a_948_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___boxed(lean_object* v_c_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(v_c_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec(v_a_953_);
return v_res_964_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_unsigned_to_nat(0u);
v___x_971_ = l_Lean_Level_ofNat(v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = lean_box(0);
v___x_973_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3);
v___x_974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
lean_ctor_set(v___x_974_, 1, v___x_972_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4);
v___x_976_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2));
v___x_977_ = l_Lean_Expr_const___override(v___x_976_, v___x_975_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_981_ = lean_box(0);
v___x_982_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7));
v___x_983_ = l_Lean_Expr_const___override(v___x_982_, v___x_981_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_988_ = lean_box(0);
v___x_989_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10));
v___x_990_ = l_Lean_Expr_const___override(v___x_989_, v___x_988_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(lean_object* v_c_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_d_995_; lean_object* v_p_996_; lean_object* v___x_997_; 
v_d_995_ = lean_ctor_get(v_c_991_, 0);
lean_inc(v_d_995_);
v_p_996_ = lean_ctor_get(v_c_991_, 1);
lean_inc_ref(v_p_996_);
lean_dec_ref(v_c_991_);
v___x_997_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_996_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1019_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1019_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1019_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___y_1003_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1008_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1009_ = lean_int_dec_le(v___x_1008_, v_d_995_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1010_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5);
v___x_1011_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8);
v___x_1012_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11);
v___x_1013_ = lean_int_neg(v_d_995_);
lean_dec(v_d_995_);
v___x_1014_ = l_Int_toNat(v___x_1013_);
lean_dec(v___x_1013_);
v___x_1015_ = l_Lean_instToExprInt_mkNat(v___x_1014_);
v___x_1016_ = l_Lean_mkApp3(v___x_1010_, v___x_1011_, v___x_1012_, v___x_1015_);
v___y_1003_ = v___x_1016_;
goto v___jp_1002_;
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = l_Int_toNat(v_d_995_);
lean_dec(v_d_995_);
v___x_1018_ = l_Lean_instToExprInt_mkNat(v___x_1017_);
v___y_1003_ = v___x_1018_;
goto v___jp_1002_;
}
v___jp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1004_ = l_Lean_mkIntDvd(v___y_1003_, v_a_998_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1004_);
v___x_1006_ = v___x_1000_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
else
{
lean_dec(v_d_995_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1020_, v_a_1021_, v_a_1022_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(lean_object* v_c_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1025_, v_a_1026_, v_a_1034_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___boxed(lean_object* v_c_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(v_c_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec(v_a_1039_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(lean_object* v_msgData_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___x_1057_; lean_object* v_env_1058_; lean_object* v___x_1059_; lean_object* v_mctx_1060_; lean_object* v_lctx_1061_; lean_object* v_options_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1057_ = lean_st_ref_get(v___y_1055_);
v_env_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc_ref(v_env_1058_);
lean_dec(v___x_1057_);
v___x_1059_ = lean_st_ref_get(v___y_1053_);
v_mctx_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc_ref(v_mctx_1060_);
lean_dec(v___x_1059_);
v_lctx_1061_ = lean_ctor_get(v___y_1052_, 2);
v_options_1062_ = lean_ctor_get(v___y_1054_, 2);
lean_inc_ref(v_options_1062_);
lean_inc_ref(v_lctx_1061_);
v___x_1063_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1063_, 0, v_env_1058_);
lean_ctor_set(v___x_1063_, 1, v_mctx_1060_);
lean_ctor_set(v___x_1063_, 2, v_lctx_1061_);
lean_ctor_set(v___x_1063_, 3, v_options_1062_);
v___x_1064_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v_msgData_1051_);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object* v_msgData_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msgData_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(lean_object* v_msg_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_ref_1079_; lean_object* v___x_1080_; lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1089_; 
v_ref_1079_ = lean_ctor_get(v___y_1076_, 5);
v___x_1080_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msg_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1089_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1089_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
lean_inc(v_ref_1079_);
v___x_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1085_, 0, v_ref_1079_);
lean_ctor_set(v___x_1085_, 1, v_a_1081_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set_tag(v___x_1083_, 1);
lean_ctor_set(v___x_1083_, 0, v___x_1085_);
v___x_1087_ = v___x_1083_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg___boxed(lean_object* v_msg_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
return v_res_1096_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0));
v___x_1099_ = l_Lean_stringToMessageData(v___x_1098_);
return v___x_1099_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2));
v___x_1102_ = l_Lean_stringToMessageData(v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object* v_c_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1103_, v_a_1104_, v_a_1112_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1117_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1118_ = l_Lean_indentD(v_a_1116_);
v___x_1119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3);
v___x_1121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1121_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
return v___x_1122_;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
v_a_1123_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1115_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1115_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec(v_a_1132_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(lean_object* v_00_u03b1_1144_, lean_object* v_c_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1158_, lean_object* v_c_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(v_00_u03b1_1158_, v_c_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec(v_a_1160_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(lean_object* v_00_u03b1_1172_, lean_object* v_msg_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1173_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___boxed(lean_object* v_00_u03b1_1186_, lean_object* v_msg_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(v_00_u03b1_1186_, v_msg_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec(v___y_1188_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial_spec__0(lean_object* v_a_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_nat_to_int(v_a_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(lean_object* v_c_1202_){
_start:
{
lean_object* v_p_1203_; 
v_p_1203_ = lean_ctor_get(v_c_1202_, 0);
if (lean_obj_tag(v_p_1203_) == 0)
{
lean_object* v_k_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; 
v_k_1204_ = lean_ctor_get(v_p_1203_, 0);
v___x_1205_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1206_ = lean_int_dec_eq(v_k_1204_, v___x_1205_);
if (v___x_1206_ == 0)
{
uint8_t v___x_1207_; 
v___x_1207_ = 1;
return v___x_1207_;
}
else
{
uint8_t v___x_1208_; 
v___x_1208_ = 0;
return v___x_1208_;
}
}
else
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1209_ = l_Int_Internal_Linear_Poly_getConst(v_p_1203_);
v___x_1210_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v_p_1203_);
v___x_1211_ = lean_nat_to_int(v___x_1210_);
v___x_1212_ = lean_int_emod(v___x_1209_, v___x_1211_);
lean_dec(v___x_1211_);
lean_dec(v___x_1209_);
v___x_1213_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1214_ = lean_int_dec_eq(v___x_1212_, v___x_1213_);
lean_dec(v___x_1212_);
if (v___x_1214_ == 0)
{
uint8_t v___x_1215_; 
v___x_1215_ = 1;
return v___x_1215_;
}
else
{
uint8_t v___x_1216_; 
v___x_1216_ = 0;
return v___x_1216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial___boxed(lean_object* v_c_1217_){
_start:
{
uint8_t v_res_1218_; lean_object* v_r_1219_; 
v_res_1218_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(v_c_1217_);
lean_dec_ref(v_c_1217_);
v_r_1219_ = lean_box(v_res_1218_);
return v_r_1219_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0));
v___x_1222_ = l_Lean_stringToMessageData(v___x_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(lean_object* v_c_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v_p_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1244_; 
v_p_1227_ = lean_ctor_get(v_c_1223_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_c_1223_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; 
v_unused_1245_ = lean_ctor_get(v_c_1223_, 1);
lean_dec(v_unused_1245_);
v___x_1229_ = v_c_1223_;
v_isShared_1230_ = v_isSharedCheck_1244_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_p_1227_);
lean_dec(v_c_1223_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1244_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1227_, v_a_1224_, v_a_1225_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1243_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1234_ = v___x_1231_;
v_isShared_1235_ = v_isSharedCheck_1243_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1231_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1243_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1236_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1);
if (v_isShared_1230_ == 0)
{
lean_ctor_set_tag(v___x_1229_, 7);
lean_ctor_set(v___x_1229_, 1, v___x_1236_);
lean_ctor_set(v___x_1229_, 0, v_a_1232_);
v___x_1238_ = v___x_1229_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1232_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1240_; 
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1238_);
v___x_1240_ = v___x_1234_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
else
{
lean_del_object(v___x_1229_);
return v___x_1231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___boxed(lean_object* v_c_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1246_, v_a_1247_, v_a_1248_);
lean_dec_ref(v_a_1248_);
lean_dec(v_a_1247_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(lean_object* v_c_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1251_, v_a_1252_, v_a_1260_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___boxed(lean_object* v_c_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(v_c_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec(v_a_1265_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(lean_object* v_c_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1277_, v_a_1278_, v_a_1281_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1287_ = l_Lean_indentD(v_a_1285_);
v___x_1288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1286_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1288_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
return v___x_1289_;
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
v_a_1290_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1284_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1284_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(lean_object* v_00_u03b1_1306_, lean_object* v_c_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1307_, v_a_1308_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1320_, lean_object* v_c_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(v_00_u03b1_1320_, v_c_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec(v_a_1323_);
lean_dec(v_a_1322_);
return v_res_1333_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1335_ = l_Lean_mkIntLit(v___x_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(lean_object* v_c_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v_p_1340_; lean_object* v___x_1341_; 
v_p_1340_ = lean_ctor_get(v_c_1336_, 0);
lean_inc_ref(v_p_1340_);
lean_dec_ref(v_c_1336_);
v___x_1341_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1340_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1352_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1346_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1347_ = l_Lean_mkIntEq(v_a_1342_, v___x_1346_);
v___x_1348_ = l_Lean_mkNot(v___x_1347_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1348_);
v___x_1350_ = v___x_1344_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
else
{
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1353_, v_a_1354_, v_a_1355_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(lean_object* v_c_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1358_, v_a_1359_, v_a_1367_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___boxed(lean_object* v_c_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(v_c_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
lean_dec(v_a_1379_);
lean_dec_ref(v_a_1378_);
lean_dec(v_a_1377_);
lean_dec_ref(v_a_1376_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec(v_a_1372_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert___boxed(lean_object* v_c_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_00___x40___internal___hyg_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = lean_grind_cutsat_assert_le(v_c_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
return v_res_1408_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(lean_object* v_c_1409_){
_start:
{
lean_object* v_p_1410_; 
v_p_1410_ = lean_ctor_get(v_c_1409_, 0);
if (lean_obj_tag(v_p_1410_) == 0)
{
lean_object* v_k_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v_k_1411_ = lean_ctor_get(v_p_1410_, 0);
v___x_1412_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1413_ = lean_int_dec_le(v_k_1411_, v___x_1412_);
return v___x_1413_;
}
else
{
uint8_t v___x_1414_; 
v___x_1414_ = 0;
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial___boxed(lean_object* v_c_1415_){
_start:
{
uint8_t v_res_1416_; lean_object* v_r_1417_; 
v_res_1416_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_c_1415_);
lean_dec_ref(v_c_1415_);
v_r_1417_ = lean_box(v_res_1416_);
return v_r_1417_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0));
v___x_1420_ = l_Lean_stringToMessageData(v___x_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(lean_object* v_c_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_p_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1442_; 
v_p_1425_ = lean_ctor_get(v_c_1421_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_c_1421_);
if (v_isSharedCheck_1442_ == 0)
{
lean_object* v_unused_1443_; 
v_unused_1443_ = lean_ctor_get(v_c_1421_, 1);
lean_dec(v_unused_1443_);
v___x_1427_ = v_c_1421_;
v_isShared_1428_ = v_isSharedCheck_1442_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_p_1425_);
lean_dec(v_c_1421_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1442_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1425_, v_a_1422_, v_a_1423_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1441_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1441_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1441_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1434_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1);
if (v_isShared_1428_ == 0)
{
lean_ctor_set_tag(v___x_1427_, 7);
lean_ctor_set(v___x_1427_, 1, v___x_1434_);
lean_ctor_set(v___x_1427_, 0, v_a_1430_);
v___x_1436_ = v___x_1427_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1430_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1438_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1436_);
v___x_1438_ = v___x_1432_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
else
{
lean_del_object(v___x_1427_);
return v___x_1429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___boxed(lean_object* v_c_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1444_, v_a_1445_, v_a_1446_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(lean_object* v_c_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1449_, v_a_1450_, v_a_1458_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___boxed(lean_object* v_c_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(v_c_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
lean_dec(v_a_1470_);
lean_dec_ref(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec(v_a_1463_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(lean_object* v_c_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_p_1479_; lean_object* v___x_1480_; 
v_p_1479_ = lean_ctor_get(v_c_1475_, 0);
lean_inc_ref(v_p_1479_);
lean_dec_ref(v_c_1475_);
v___x_1480_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1479_, v_a_1476_, v_a_1477_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1490_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1490_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1490_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1485_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1486_ = l_Lean_mkIntLE(v_a_1481_, v___x_1485_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1486_);
v___x_1488_ = v___x_1483_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
else
{
return v___x_1480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1491_, v_a_1492_, v_a_1493_);
lean_dec_ref(v_a_1493_);
lean_dec(v_a_1492_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(lean_object* v_c_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1496_, v_a_1497_, v_a_1505_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___boxed(lean_object* v_c_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(v_c_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
lean_dec(v_a_1513_);
lean_dec_ref(v_a_1512_);
lean_dec(v_a_1511_);
lean_dec(v_a_1510_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(lean_object* v_c_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1522_, v_a_1523_, v_a_1526_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v___x_1531_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1532_ = l_Lean_indentD(v_a_1530_);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1533_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_);
return v___x_1534_;
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
v_a_1535_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1529_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1529_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_);
lean_dec(v_a_1548_);
lean_dec_ref(v_a_1547_);
lean_dec(v_a_1546_);
lean_dec_ref(v_a_1545_);
lean_dec(v_a_1544_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(lean_object* v_00_u03b1_1551_, lean_object* v_c_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1552_, v_a_1553_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1565_, lean_object* v_c_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(v_00_u03b1_1565_, v_c_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_);
lean_dec(v_a_1576_);
lean_dec_ref(v_a_1575_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
lean_dec(v_a_1568_);
lean_dec(v_a_1567_);
return v_res_1578_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(lean_object* v_c_1579_){
_start:
{
lean_object* v_p_1580_; 
v_p_1580_ = lean_ctor_get(v_c_1579_, 0);
if (lean_obj_tag(v_p_1580_) == 0)
{
lean_object* v_k_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v_k_1581_ = lean_ctor_get(v_p_1580_, 0);
v___x_1582_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1583_ = lean_int_dec_eq(v_k_1581_, v___x_1582_);
return v___x_1583_;
}
else
{
uint8_t v___x_1584_; 
v___x_1584_ = 0;
return v___x_1584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial___boxed(lean_object* v_c_1585_){
_start:
{
uint8_t v_res_1586_; lean_object* v_r_1587_; 
v_res_1586_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(v_c_1585_);
lean_dec_ref(v_c_1585_);
v_r_1587_ = lean_box(v_res_1586_);
return v_r_1587_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0));
v___x_1590_ = l_Lean_stringToMessageData(v___x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object* v_c_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_p_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1612_; 
v_p_1595_ = lean_ctor_get(v_c_1591_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_c_1591_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; 
v_unused_1613_ = lean_ctor_get(v_c_1591_, 1);
lean_dec(v_unused_1613_);
v___x_1597_ = v_c_1591_;
v_isShared_1598_ = v_isSharedCheck_1612_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_p_1595_);
lean_dec(v_c_1591_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1612_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1595_, v_a_1592_, v_a_1593_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1611_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1602_ = v___x_1599_;
v_isShared_1603_ = v_isSharedCheck_1611_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1611_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1604_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1);
if (v_isShared_1598_ == 0)
{
lean_ctor_set_tag(v___x_1597_, 7);
lean_ctor_set(v___x_1597_, 1, v___x_1604_);
lean_ctor_set(v___x_1597_, 0, v_a_1600_);
v___x_1606_ = v___x_1597_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1600_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1608_; 
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v___x_1606_);
v___x_1608_ = v___x_1602_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
lean_del_object(v___x_1597_);
return v___x_1599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___boxed(lean_object* v_c_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1614_, v_a_1615_, v_a_1616_);
lean_dec_ref(v_a_1616_);
lean_dec(v_a_1615_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(lean_object* v_c_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1619_, v_a_1620_, v_a_1628_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___boxed(lean_object* v_c_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(v_c_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
lean_dec(v_a_1634_);
lean_dec(v_a_1633_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(lean_object* v_c_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_p_1649_; lean_object* v___x_1650_; 
v_p_1649_ = lean_ctor_get(v_c_1645_, 0);
lean_inc_ref(v_p_1649_);
lean_dec_ref(v_c_1645_);
v___x_1650_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1649_, v_a_1646_, v_a_1647_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1660_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1660_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1660_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1655_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1656_ = l_Lean_mkIntEq(v_a_1651_, v___x_1655_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1656_);
v___x_1658_ = v___x_1653_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
else
{
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1661_, v_a_1662_, v_a_1663_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(lean_object* v_c_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1666_, v_a_1667_, v_a_1675_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___boxed(lean_object* v_c_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(v_c_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec(v_a_1680_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(lean_object* v_c_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1692_, v_a_1693_, v_a_1696_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1699_, 1);
v___x_1701_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1702_ = l_Lean_indentD(v_a_1700_);
v___x_1703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1703_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
return v___x_1704_;
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
v_a_1705_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1699_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1699_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_);
lean_dec(v_a_1718_);
lean_dec_ref(v_a_1717_);
lean_dec(v_a_1716_);
lean_dec_ref(v_a_1715_);
lean_dec(v_a_1714_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(lean_object* v_00_u03b1_1721_, lean_object* v_c_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_1722_, v_a_1723_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1735_, lean_object* v_c_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(v_00_u03b1_1735_, v_c_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec(v_a_1737_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(lean_object* v_x_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1770_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1770_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1770_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v_occurs_1758_; lean_object* v_size_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v_occurs_1758_ = lean_ctor_get(v_a_1754_, 12);
lean_inc_ref(v_occurs_1758_);
lean_dec(v_a_1754_);
v_size_1759_ = lean_ctor_get(v_occurs_1758_, 2);
v___x_1760_ = lean_box(1);
v___x_1761_ = lean_nat_dec_lt(v_x_1749_, v_size_1759_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
lean_dec_ref(v_occurs_1758_);
v___x_1762_ = l_outOfBounds___redArg(v___x_1760_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1762_);
v___x_1764_ = v___x_1756_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
v___x_1766_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1760_, v_occurs_1758_, v_x_1749_);
lean_dec_ref(v_occurs_1758_);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1766_);
v___x_1768_ = v___x_1756_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
v_a_1771_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1753_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1753_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg___boxed(lean_object* v_x_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_1779_, v_a_1780_, v_a_1781_);
lean_dec_ref(v_a_1781_);
lean_dec(v_a_1780_);
lean_dec(v_x_1779_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(lean_object* v_x_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_1784_, v_a_1785_, v_a_1793_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___boxed(lean_object* v_x_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(v_x_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
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
lean_dec(v_x_1797_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(lean_object* v_k_1810_, lean_object* v_v_1811_, lean_object* v_t_1812_){
_start:
{
if (lean_obj_tag(v_t_1812_) == 0)
{
lean_object* v_size_1813_; lean_object* v_k_1814_; lean_object* v_v_1815_; lean_object* v_l_1816_; lean_object* v_r_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_2098_; 
v_size_1813_ = lean_ctor_get(v_t_1812_, 0);
v_k_1814_ = lean_ctor_get(v_t_1812_, 1);
v_v_1815_ = lean_ctor_get(v_t_1812_, 2);
v_l_1816_ = lean_ctor_get(v_t_1812_, 3);
v_r_1817_ = lean_ctor_get(v_t_1812_, 4);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_t_1812_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_1819_ = v_t_1812_;
v_isShared_1820_ = v_isSharedCheck_2098_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_r_1817_);
lean_inc(v_l_1816_);
lean_inc(v_v_1815_);
lean_inc(v_k_1814_);
lean_inc(v_size_1813_);
lean_dec(v_t_1812_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_2098_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_nat_dec_lt(v_k_1810_, v_k_1814_);
if (v___x_1821_ == 0)
{
uint8_t v___x_1822_; 
v___x_1822_ = lean_nat_dec_eq(v_k_1810_, v_k_1814_);
if (v___x_1822_ == 0)
{
lean_object* v_impl_1823_; lean_object* v___x_1824_; 
lean_dec(v_size_1813_);
v_impl_1823_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_1810_, v_v_1811_, v_r_1817_);
v___x_1824_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1816_) == 0)
{
lean_object* v_size_1825_; lean_object* v_size_1826_; lean_object* v_k_1827_; lean_object* v_v_1828_; lean_object* v_l_1829_; lean_object* v_r_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v_size_1825_ = lean_ctor_get(v_l_1816_, 0);
v_size_1826_ = lean_ctor_get(v_impl_1823_, 0);
lean_inc(v_size_1826_);
v_k_1827_ = lean_ctor_get(v_impl_1823_, 1);
lean_inc(v_k_1827_);
v_v_1828_ = lean_ctor_get(v_impl_1823_, 2);
lean_inc(v_v_1828_);
v_l_1829_ = lean_ctor_get(v_impl_1823_, 3);
lean_inc(v_l_1829_);
v_r_1830_ = lean_ctor_get(v_impl_1823_, 4);
lean_inc(v_r_1830_);
v___x_1831_ = lean_unsigned_to_nat(3u);
v___x_1832_ = lean_nat_mul(v___x_1831_, v_size_1825_);
v___x_1833_ = lean_nat_dec_lt(v___x_1832_, v_size_1826_);
lean_dec(v___x_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; 
lean_dec(v_r_1830_);
lean_dec(v_l_1829_);
lean_dec(v_v_1828_);
lean_dec(v_k_1827_);
v___x_1834_ = lean_nat_add(v___x_1824_, v_size_1825_);
v___x_1835_ = lean_nat_add(v___x_1834_, v_size_1826_);
lean_dec(v_size_1826_);
lean_dec(v___x_1834_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 4, v_impl_1823_);
lean_ctor_set(v___x_1819_, 0, v___x_1835_);
v___x_1837_ = v___x_1819_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_k_1814_);
lean_ctor_set(v_reuseFailAlloc_1838_, 2, v_v_1815_);
lean_ctor_set(v_reuseFailAlloc_1838_, 3, v_l_1816_);
lean_ctor_set(v_reuseFailAlloc_1838_, 4, v_impl_1823_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
else
{
lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1902_; 
v_isSharedCheck_1902_ = !lean_is_exclusive(v_impl_1823_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; lean_object* v_unused_1904_; lean_object* v_unused_1905_; lean_object* v_unused_1906_; lean_object* v_unused_1907_; 
v_unused_1903_ = lean_ctor_get(v_impl_1823_, 4);
lean_dec(v_unused_1903_);
v_unused_1904_ = lean_ctor_get(v_impl_1823_, 3);
lean_dec(v_unused_1904_);
v_unused_1905_ = lean_ctor_get(v_impl_1823_, 2);
lean_dec(v_unused_1905_);
v_unused_1906_ = lean_ctor_get(v_impl_1823_, 1);
lean_dec(v_unused_1906_);
v_unused_1907_ = lean_ctor_get(v_impl_1823_, 0);
lean_dec(v_unused_1907_);
v___x_1840_ = v_impl_1823_;
v_isShared_1841_ = v_isSharedCheck_1902_;
goto v_resetjp_1839_;
}
else
{
lean_dec(v_impl_1823_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1902_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v_size_1842_; lean_object* v_k_1843_; lean_object* v_v_1844_; lean_object* v_l_1845_; lean_object* v_r_1846_; lean_object* v_size_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; 
v_size_1842_ = lean_ctor_get(v_l_1829_, 0);
v_k_1843_ = lean_ctor_get(v_l_1829_, 1);
v_v_1844_ = lean_ctor_get(v_l_1829_, 2);
v_l_1845_ = lean_ctor_get(v_l_1829_, 3);
v_r_1846_ = lean_ctor_get(v_l_1829_, 4);
v_size_1847_ = lean_ctor_get(v_r_1830_, 0);
v___x_1848_ = lean_unsigned_to_nat(2u);
v___x_1849_ = lean_nat_mul(v___x_1848_, v_size_1847_);
v___x_1850_ = lean_nat_dec_lt(v_size_1842_, v___x_1849_);
lean_dec(v___x_1849_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1878_; 
lean_inc(v_r_1846_);
lean_inc(v_l_1845_);
lean_inc(v_v_1844_);
lean_inc(v_k_1843_);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_l_1829_);
if (v_isSharedCheck_1878_ == 0)
{
lean_object* v_unused_1879_; lean_object* v_unused_1880_; lean_object* v_unused_1881_; lean_object* v_unused_1882_; lean_object* v_unused_1883_; 
v_unused_1879_ = lean_ctor_get(v_l_1829_, 4);
lean_dec(v_unused_1879_);
v_unused_1880_ = lean_ctor_get(v_l_1829_, 3);
lean_dec(v_unused_1880_);
v_unused_1881_ = lean_ctor_get(v_l_1829_, 2);
lean_dec(v_unused_1881_);
v_unused_1882_ = lean_ctor_get(v_l_1829_, 1);
lean_dec(v_unused_1882_);
v_unused_1883_ = lean_ctor_get(v_l_1829_, 0);
lean_dec(v_unused_1883_);
v___x_1852_ = v_l_1829_;
v_isShared_1853_ = v_isSharedCheck_1878_;
goto v_resetjp_1851_;
}
else
{
lean_dec(v_l_1829_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1878_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1868_; 
v___x_1854_ = lean_nat_add(v___x_1824_, v_size_1825_);
v___x_1855_ = lean_nat_add(v___x_1854_, v_size_1826_);
lean_dec(v_size_1826_);
if (lean_obj_tag(v_l_1845_) == 0)
{
lean_object* v_size_1876_; 
v_size_1876_ = lean_ctor_get(v_l_1845_, 0);
lean_inc(v_size_1876_);
v___y_1868_ = v_size_1876_;
goto v___jp_1867_;
}
else
{
lean_object* v___x_1877_; 
v___x_1877_ = lean_unsigned_to_nat(0u);
v___y_1868_ = v___x_1877_;
goto v___jp_1867_;
}
v___jp_1856_:
{
lean_object* v___x_1860_; lean_object* v___x_1862_; 
v___x_1860_ = lean_nat_add(v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
lean_dec(v___y_1858_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 4, v_r_1830_);
lean_ctor_set(v___x_1852_, 3, v_r_1846_);
lean_ctor_set(v___x_1852_, 2, v_v_1828_);
lean_ctor_set(v___x_1852_, 1, v_k_1827_);
lean_ctor_set(v___x_1852_, 0, v___x_1860_);
v___x_1862_ = v___x_1852_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1860_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_k_1827_);
lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_v_1828_);
lean_ctor_set(v_reuseFailAlloc_1866_, 3, v_r_1846_);
lean_ctor_set(v_reuseFailAlloc_1866_, 4, v_r_1830_);
v___x_1862_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1864_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 4, v___x_1862_);
lean_ctor_set(v___x_1840_, 3, v___y_1857_);
lean_ctor_set(v___x_1840_, 2, v_v_1844_);
lean_ctor_set(v___x_1840_, 1, v_k_1843_);
lean_ctor_set(v___x_1840_, 0, v___x_1855_);
v___x_1864_ = v___x_1840_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1855_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_k_1843_);
lean_ctor_set(v_reuseFailAlloc_1865_, 2, v_v_1844_);
lean_ctor_set(v_reuseFailAlloc_1865_, 3, v___y_1857_);
lean_ctor_set(v_reuseFailAlloc_1865_, 4, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
v___jp_1867_:
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1869_ = lean_nat_add(v___x_1854_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec(v___x_1854_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 4, v_l_1845_);
lean_ctor_set(v___x_1819_, 0, v___x_1869_);
v___x_1871_ = v___x_1819_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_k_1814_);
lean_ctor_set(v_reuseFailAlloc_1875_, 2, v_v_1815_);
lean_ctor_set(v_reuseFailAlloc_1875_, 3, v_l_1816_);
lean_ctor_set(v_reuseFailAlloc_1875_, 4, v_l_1845_);
v___x_1871_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_nat_add(v___x_1824_, v_size_1847_);
if (lean_obj_tag(v_r_1846_) == 0)
{
lean_object* v_size_1873_; 
v_size_1873_ = lean_ctor_get(v_r_1846_, 0);
lean_inc(v_size_1873_);
v___y_1857_ = v___x_1871_;
v___y_1858_ = v___x_1872_;
v___y_1859_ = v_size_1873_;
goto v___jp_1856_;
}
else
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_unsigned_to_nat(0u);
v___y_1857_ = v___x_1871_;
v___y_1858_ = v___x_1872_;
v___y_1859_ = v___x_1874_;
goto v___jp_1856_;
}
}
}
}
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
lean_del_object(v___x_1819_);
v___x_1884_ = lean_nat_add(v___x_1824_, v_size_1825_);
v___x_1885_ = lean_nat_add(v___x_1884_, v_size_1826_);
lean_dec(v_size_1826_);
v___x_1886_ = lean_nat_add(v___x_1884_, v_size_1842_);
lean_dec(v___x_1884_);
lean_inc_ref(v_l_1816_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 4, v_l_1829_);
lean_ctor_set(v___x_1840_, 3, v_l_1816_);
lean_ctor_set(v___x_1840_, 2, v_v_1815_);
lean_ctor_set(v___x_1840_, 1, v_k_1814_);
lean_ctor_set(v___x_1840_, 0, v___x_1886_);
v___x_1888_ = v___x_1840_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_k_1814_);
lean_ctor_set(v_reuseFailAlloc_1901_, 2, v_v_1815_);
lean_ctor_set(v_reuseFailAlloc_1901_, 3, v_l_1816_);
lean_ctor_set(v_reuseFailAlloc_1901_, 4, v_l_1829_);
v___x_1888_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
v_isSharedCheck_1895_ = !lean_is_exclusive(v_l_1816_);
if (v_isSharedCheck_1895_ == 0)
{
lean_object* v_unused_1896_; lean_object* v_unused_1897_; lean_object* v_unused_1898_; lean_object* v_unused_1899_; lean_object* v_unused_1900_; 
v_unused_1896_ = lean_ctor_get(v_l_1816_, 4);
lean_dec(v_unused_1896_);
v_unused_1897_ = lean_ctor_get(v_l_1816_, 3);
lean_dec(v_unused_1897_);
v_unused_1898_ = lean_ctor_get(v_l_1816_, 2);
lean_dec(v_unused_1898_);
v_unused_1899_ = lean_ctor_get(v_l_1816_, 1);
lean_dec(v_unused_1899_);
v_unused_1900_ = lean_ctor_get(v_l_1816_, 0);
lean_dec(v_unused_1900_);
v___x_1890_ = v_l_1816_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_dec(v_l_1816_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 4, v_r_1830_);
lean_ctor_set(v___x_1890_, 3, v___x_1888_);
lean_ctor_set(v___x_1890_, 2, v_v_1828_);
lean_ctor_set(v___x_1890_, 1, v_k_1827_);
lean_ctor_set(v___x_1890_, 0, v___x_1885_);
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_k_1827_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_v_1828_);
lean_ctor_set(v_reuseFailAlloc_1894_, 3, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1894_, 4, v_r_1830_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1908_; 
v_l_1908_ = lean_ctor_get(v_impl_1823_, 3);
lean_inc(v_l_1908_);
if (lean_obj_tag(v_l_1908_) == 0)
{
lean_object* v_r_1909_; lean_object* v_k_1910_; lean_object* v_v_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1934_; 
v_r_1909_ = lean_ctor_get(v_impl_1823_, 4);
v_k_1910_ = lean_ctor_get(v_impl_1823_, 1);
v_v_1911_ = lean_ctor_get(v_impl_1823_, 2);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_impl_1823_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; lean_object* v_unused_1936_; 
v_unused_1935_ = lean_ctor_get(v_impl_1823_, 3);
lean_dec(v_unused_1935_);
v_unused_1936_ = lean_ctor_get(v_impl_1823_, 0);
lean_dec(v_unused_1936_);
v___x_1913_ = v_impl_1823_;
v_isShared_1914_ = v_isSharedCheck_1934_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_r_1909_);
lean_inc(v_v_1911_);
lean_inc(v_k_1910_);
lean_dec(v_impl_1823_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1934_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v_k_1915_; lean_object* v_v_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1930_; 
v_k_1915_ = lean_ctor_get(v_l_1908_, 1);
v_v_1916_ = lean_ctor_get(v_l_1908_, 2);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_l_1908_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; lean_object* v_unused_1932_; lean_object* v_unused_1933_; 
v_unused_1931_ = lean_ctor_get(v_l_1908_, 4);
lean_dec(v_unused_1931_);
v_unused_1932_ = lean_ctor_get(v_l_1908_, 3);
lean_dec(v_unused_1932_);
v_unused_1933_ = lean_ctor_get(v_l_1908_, 0);
lean_dec(v_unused_1933_);
v___x_1918_ = v_l_1908_;
v_isShared_1919_ = v_isSharedCheck_1930_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_v_1916_);
lean_inc(v_k_1915_);
lean_dec(v_l_1908_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1930_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; lean_object* v___x_1922_; 
v___x_1920_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1909_, 2);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 4, v_r_1909_);
lean_ctor_set(v___x_1918_, 3, v_r_1909_);
lean_ctor_set(v___x_1918_, 2, v_v_1815_);
lean_ctor_set(v___x_1918_, 1, v_k_1814_);
lean_ctor_set(v___x_1918_, 0, v___x_1824_);
v___x_1922_ = v___x_1918_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_k_1814_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v_v_1815_);
lean_ctor_set(v_reuseFailAlloc_1929_, 3, v_r_1909_);
lean_ctor_set(v_reuseFailAlloc_1929_, 4, v_r_1909_);
v___x_1922_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1924_; 
lean_inc(v_r_1909_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 3, v_r_1909_);
lean_ctor_set(v___x_1913_, 0, v___x_1824_);
v___x_1924_ = v___x_1913_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_k_1910_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v_v_1911_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v_r_1909_);
lean_ctor_set(v_reuseFailAlloc_1928_, 4, v_r_1909_);
v___x_1924_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1926_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 4, v___x_1924_);
lean_ctor_set(v___x_1819_, 3, v___x_1922_);
lean_ctor_set(v___x_1819_, 2, v_v_1916_);
lean_ctor_set(v___x_1819_, 1, v_k_1915_);
lean_ctor_set(v___x_1819_, 0, v___x_1920_);
v___x_1926_ = v___x_1819_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_k_1915_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v_v_1916_);
lean_ctor_set(v_reuseFailAlloc_1927_, 3, v___x_1922_);
lean_ctor_set(v_reuseFailAlloc_1927_, 4, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
}
else
{
lean_object* v_r_1937_; 
v_r_1937_ = lean_ctor_get(v_impl_1823_, 4);
lean_inc(v_r_1937_);
if (lean_obj_tag(v_r_1937_) == 0)
{
lean_object* v_k_1938_; lean_object* v_v_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1950_; 
v_k_1938_ = lean_ctor_get(v_impl_1823_, 1);
v_v_1939_ = lean_ctor_get(v_impl_1823_, 2);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_impl_1823_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; lean_object* v_unused_1952_; lean_object* v_unused_1953_; 
v_unused_1951_ = lean_ctor_get(v_impl_1823_, 4);
lean_dec(v_unused_1951_);
v_unused_1952_ = lean_ctor_get(v_impl_1823_, 3);
lean_dec(v_unused_1952_);
v_unused_1953_ = lean_ctor_get(v_impl_1823_, 0);
lean_dec(v_unused_1953_);
v___x_1941_ = v_impl_1823_;
v_isShared_1942_ = v_isSharedCheck_1950_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_v_1939_);
lean_inc(v_k_1938_);
lean_dec(v_impl_1823_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1950_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1943_ = lean_unsigned_to_nat(3u);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 4, v_l_1908_);
lean_ctor_set(v___x_1941_, 2, v_v_1815_);
lean_ctor_set(v___x_1941_, 1, v_k_1814_);
lean_ctor_set(v___x_1941_, 0, v___x_1824_);
v___x_1945_ = v___x_1941_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_k_1814_);
lean_ctor_set(v_reuseFailAlloc_1949_, 2, v_v_1815_);
lean_ctor_set(v_reuseFailAlloc_1949_, 3, v_l_1908_);
lean_ctor_set(v_reuseFailAlloc_1949_, 4, v_l_1908_);
v___x_1945_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1947_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 4, v_r_1937_);
lean_ctor_set(v___x_1819_, 3, v___x_1945_);
lean_ctor_set(v___x_1819_, 2, v_v_1939_);
lean_ctor_set(v___x_1819_, 1, v_k_1938_);
lean_ctor_set(v___x_1819_, 0, v___x_1943_);
v___x_1947_ = v___x_1819_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_k_1938_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v_v_1939_);
lean_ctor_set(v_reuseFailAlloc_1948_, 3, v___x_1945_);
lean_ctor_set(v_reuseFailAlloc_1948_, 4, v_r_1937_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1954_ = lean_unsigned_to_nat(2u);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 4, v_impl_1823_);
lean_ctor_set(v___x_1819_, 3, v_r_1937_);
lean_ctor_set(v___x_1819_, 0, v___x_1954_);
v___x_1956_ = v___x_1819_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1954_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_k_1814_);
lean_ctor_set(v_reuseFailAlloc_1957_, 2, v_v_1815_);
lean_ctor_set(v_reuseFailAlloc_1957_, 3, v_r_1937_);
lean_ctor_set(v_reuseFailAlloc_1957_, 4, v_impl_1823_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
else
{
lean_object* v___x_1959_; 
lean_dec(v_v_1815_);
lean_dec(v_k_1814_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 2, v_v_1811_);
lean_ctor_set(v___x_1819_, 1, v_k_1810_);
v___x_1959_ = v___x_1819_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_size_1813_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_k_1810_);
lean_ctor_set(v_reuseFailAlloc_1960_, 2, v_v_1811_);
lean_ctor_set(v_reuseFailAlloc_1960_, 3, v_l_1816_);
lean_ctor_set(v_reuseFailAlloc_1960_, 4, v_r_1817_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
else
{
lean_object* v_impl_1961_; lean_object* v___x_1962_; 
lean_dec(v_size_1813_);
v_impl_1961_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_1810_, v_v_1811_, v_l_1816_);
v___x_1962_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1817_) == 0)
{
lean_object* v_size_1963_; lean_object* v_size_1964_; lean_object* v_k_1965_; lean_object* v_v_1966_; lean_object* v_l_1967_; lean_object* v_r_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v_size_1963_ = lean_ctor_get(v_r_1817_, 0);
v_size_1964_ = lean_ctor_get(v_impl_1961_, 0);
lean_inc(v_size_1964_);
v_k_1965_ = lean_ctor_get(v_impl_1961_, 1);
lean_inc(v_k_1965_);
v_v_1966_ = lean_ctor_get(v_impl_1961_, 2);
lean_inc(v_v_1966_);
v_l_1967_ = lean_ctor_get(v_impl_1961_, 3);
lean_inc(v_l_1967_);
v_r_1968_ = lean_ctor_get(v_impl_1961_, 4);
lean_inc(v_r_1968_);
v___x_1969_ = lean_unsigned_to_nat(3u);
v___x_1970_ = lean_nat_mul(v___x_1969_, v_size_1963_);
v___x_1971_ = lean_nat_dec_lt(v___x_1970_, v_size_1964_);
lean_dec(v___x_1970_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1975_; 
lean_dec(v_r_1968_);
lean_dec(v_l_1967_);
lean_dec(v_v_1966_);
lean_dec(v_k_1965_);
v___x_1972_ = lean_nat_add(v___x_1962_, v_size_1964_);
lean_dec(v_size_1964_);
v___x_1973_ = lean_nat_add(v___x_1972_, v_size_1963_);
lean_dec(v___x_1972_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 3, v_impl_1961_);
lean_ctor_set(v___x_1819_, 0, v___x_1973_);
v___x_1975_ = v___x_1819_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_k_1814_);
lean_ctor_set(v_reuseFailAlloc_1976_, 2, v_v_1815_);
lean_ctor_set(v_reuseFailAlloc_1976_, 3, v_impl_1961_);
lean_ctor_set(v_reuseFailAlloc_1976_, 4, v_r_1817_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
else
{
lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2042_; 
v_isSharedCheck_2042_ = !lean_is_exclusive(v_impl_1961_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; lean_object* v_unused_2044_; lean_object* v_unused_2045_; lean_object* v_unused_2046_; lean_object* v_unused_2047_; 
v_unused_2043_ = lean_ctor_get(v_impl_1961_, 4);
lean_dec(v_unused_2043_);
v_unused_2044_ = lean_ctor_get(v_impl_1961_, 3);
lean_dec(v_unused_2044_);
v_unused_2045_ = lean_ctor_get(v_impl_1961_, 2);
lean_dec(v_unused_2045_);
v_unused_2046_ = lean_ctor_get(v_impl_1961_, 1);
lean_dec(v_unused_2046_);
v_unused_2047_ = lean_ctor_get(v_impl_1961_, 0);
lean_dec(v_unused_2047_);
v___x_1978_ = v_impl_1961_;
v_isShared_1979_ = v_isSharedCheck_2042_;
goto v_resetjp_1977_;
}
else
{
lean_dec(v_impl_1961_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2042_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v_size_1980_; lean_object* v_size_1981_; lean_object* v_k_1982_; lean_object* v_v_1983_; lean_object* v_l_1984_; lean_object* v_r_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v_size_1980_ = lean_ctor_get(v_l_1967_, 0);
v_size_1981_ = lean_ctor_get(v_r_1968_, 0);
v_k_1982_ = lean_ctor_get(v_r_1968_, 1);
v_v_1983_ = lean_ctor_get(v_r_1968_, 2);
v_l_1984_ = lean_ctor_get(v_r_1968_, 3);
v_r_1985_ = lean_ctor_get(v_r_1968_, 4);
v___x_1986_ = lean_unsigned_to_nat(2u);
v___x_1987_ = lean_nat_mul(v___x_1986_, v_size_1980_);
v___x_1988_ = lean_nat_dec_lt(v_size_1981_, v___x_1987_);
lean_dec(v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2017_; 
lean_inc(v_r_1985_);
lean_inc(v_l_1984_);
lean_inc(v_v_1983_);
lean_inc(v_k_1982_);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_r_1968_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; lean_object* v_unused_2019_; lean_object* v_unused_2020_; lean_object* v_unused_2021_; lean_object* v_unused_2022_; 
v_unused_2018_ = lean_ctor_get(v_r_1968_, 4);
lean_dec(v_unused_2018_);
v_unused_2019_ = lean_ctor_get(v_r_1968_, 3);
lean_dec(v_unused_2019_);
v_unused_2020_ = lean_ctor_get(v_r_1968_, 2);
lean_dec(v_unused_2020_);
v_unused_2021_ = lean_ctor_get(v_r_1968_, 1);
lean_dec(v_unused_2021_);
v_unused_2022_ = lean_ctor_get(v_r_1968_, 0);
lean_dec(v_unused_2022_);
v___x_1990_ = v_r_1968_;
v_isShared_1991_ = v_isSharedCheck_2017_;
goto v_resetjp_1989_;
}
else
{
lean_dec(v_r_1968_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2017_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___x_2005_; lean_object* v___y_2007_; 
v___x_1992_ = lean_nat_add(v___x_1962_, v_size_1964_);
lean_dec(v_size_1964_);
v___x_1993_ = lean_nat_add(v___x_1992_, v_size_1963_);
lean_dec(v___x_1992_);
v___x_2005_ = lean_nat_add(v___x_1962_, v_size_1980_);
if (lean_obj_tag(v_l_1984_) == 0)
{
lean_object* v_size_2015_; 
v_size_2015_ = lean_ctor_get(v_l_1984_, 0);
lean_inc(v_size_2015_);
v___y_2007_ = v_size_2015_;
goto v___jp_2006_;
}
else
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_unsigned_to_nat(0u);
v___y_2007_ = v___x_2016_;
goto v___jp_2006_;
}
v___jp_1994_:
{
lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1998_ = lean_nat_add(v___y_1996_, v___y_1997_);
lean_dec(v___y_1997_);
lean_dec(v___y_1996_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 4, v_r_1817_);
lean_ctor_set(v___x_1990_, 3, v_r_1985_);
lean_ctor_set(v___x_1990_, 2, v_v_1815_);
lean_ctor_set(v___x_1990_, 1, v_k_1814_);
lean_ctor_set(v___x_1990_, 0, v___x_1998_);
v___x_2000_ = v___x_1990_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_k_1814_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v_v_1815_);
lean_ctor_set(v_reuseFailAlloc_2004_, 3, v_r_1985_);
lean_ctor_set(v_reuseFailAlloc_2004_, 4, v_r_1817_);
v___x_2000_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2002_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 4, v___x_2000_);
lean_ctor_set(v___x_1978_, 3, v___y_1995_);
lean_ctor_set(v___x_1978_, 2, v_v_1983_);
lean_ctor_set(v___x_1978_, 1, v_k_1982_);
lean_ctor_set(v___x_1978_, 0, v___x_1993_);
v___x_2002_ = v___x_1978_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_k_1982_);
lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_v_1983_);
lean_ctor_set(v_reuseFailAlloc_2003_, 3, v___y_1995_);
lean_ctor_set(v_reuseFailAlloc_2003_, 4, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
v___jp_2006_:
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2008_ = lean_nat_add(v___x_2005_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec(v___x_2005_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 4, v_l_1984_);
lean_ctor_set(v___x_1819_, 3, v_l_1967_);
lean_ctor_set(v___x_1819_, 2, v_v_1966_);
lean_ctor_set(v___x_1819_, 1, v_k_1965_);
lean_ctor_set(v___x_1819_, 0, v___x_2008_);
v___x_2010_ = v___x_1819_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_k_1965_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_v_1966_);
lean_ctor_set(v_reuseFailAlloc_2014_, 3, v_l_1967_);
lean_ctor_set(v_reuseFailAlloc_2014_, 4, v_l_1984_);
v___x_2010_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_nat_add(v___x_1962_, v_size_1963_);
if (lean_obj_tag(v_r_1985_) == 0)
{
lean_object* v_size_2012_; 
v_size_2012_ = lean_ctor_get(v_r_1985_, 0);
lean_inc(v_size_2012_);
v___y_1995_ = v___x_2010_;
v___y_1996_ = v___x_2011_;
v___y_1997_ = v_size_2012_;
goto v___jp_1994_;
}
else
{
lean_object* v___x_2013_; 
v___x_2013_ = lean_unsigned_to_nat(0u);
v___y_1995_ = v___x_2010_;
v___y_1996_ = v___x_2011_;
v___y_1997_ = v___x_2013_;
goto v___jp_1994_;
}
}
}
}
}
else
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
lean_del_object(v___x_1819_);
v___x_2023_ = lean_nat_add(v___x_1962_, v_size_1964_);
lean_dec(v_size_1964_);
v___x_2024_ = lean_nat_add(v___x_2023_, v_size_1963_);
lean_dec(v___x_2023_);
v___x_2025_ = lean_nat_add(v___x_1962_, v_size_1963_);
v___x_2026_ = lean_nat_add(v___x_2025_, v_size_1981_);
lean_dec(v___x_2025_);
lean_inc_ref(v_r_1817_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 4, v_r_1817_);
lean_ctor_set(v___x_1978_, 3, v_r_1968_);
lean_ctor_set(v___x_1978_, 2, v_v_1815_);
lean_ctor_set(v___x_1978_, 1, v_k_1814_);
lean_ctor_set(v___x_1978_, 0, v___x_2026_);
v___x_2028_ = v___x_1978_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2026_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_k_1814_);
lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_v_1815_);
lean_ctor_set(v_reuseFailAlloc_2041_, 3, v_r_1968_);
lean_ctor_set(v_reuseFailAlloc_2041_, 4, v_r_1817_);
v___x_2028_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
v_isSharedCheck_2035_ = !lean_is_exclusive(v_r_1817_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; lean_object* v_unused_2037_; lean_object* v_unused_2038_; lean_object* v_unused_2039_; lean_object* v_unused_2040_; 
v_unused_2036_ = lean_ctor_get(v_r_1817_, 4);
lean_dec(v_unused_2036_);
v_unused_2037_ = lean_ctor_get(v_r_1817_, 3);
lean_dec(v_unused_2037_);
v_unused_2038_ = lean_ctor_get(v_r_1817_, 2);
lean_dec(v_unused_2038_);
v_unused_2039_ = lean_ctor_get(v_r_1817_, 1);
lean_dec(v_unused_2039_);
v_unused_2040_ = lean_ctor_get(v_r_1817_, 0);
lean_dec(v_unused_2040_);
v___x_2030_ = v_r_1817_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_dec(v_r_1817_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 4, v___x_2028_);
lean_ctor_set(v___x_2030_, 3, v_l_1967_);
lean_ctor_set(v___x_2030_, 2, v_v_1966_);
lean_ctor_set(v___x_2030_, 1, v_k_1965_);
lean_ctor_set(v___x_2030_, 0, v___x_2024_);
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_k_1965_);
lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_v_1966_);
lean_ctor_set(v_reuseFailAlloc_2034_, 3, v_l_1967_);
lean_ctor_set(v_reuseFailAlloc_2034_, 4, v___x_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2048_; 
v_l_2048_ = lean_ctor_get(v_impl_1961_, 3);
lean_inc(v_l_2048_);
if (lean_obj_tag(v_l_2048_) == 0)
{
lean_object* v_r_2049_; lean_object* v_k_2050_; lean_object* v_v_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2062_; 
v_r_2049_ = lean_ctor_get(v_impl_1961_, 4);
v_k_2050_ = lean_ctor_get(v_impl_1961_, 1);
v_v_2051_ = lean_ctor_get(v_impl_1961_, 2);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_impl_1961_);
if (v_isSharedCheck_2062_ == 0)
{
lean_object* v_unused_2063_; lean_object* v_unused_2064_; 
v_unused_2063_ = lean_ctor_get(v_impl_1961_, 3);
lean_dec(v_unused_2063_);
v_unused_2064_ = lean_ctor_get(v_impl_1961_, 0);
lean_dec(v_unused_2064_);
v___x_2053_ = v_impl_1961_;
v_isShared_2054_ = v_isSharedCheck_2062_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_r_2049_);
lean_inc(v_v_2051_);
lean_inc(v_k_2050_);
lean_dec(v_impl_1961_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2062_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2055_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2049_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 3, v_r_2049_);
lean_ctor_set(v___x_2053_, 2, v_v_1815_);
lean_ctor_set(v___x_2053_, 1, v_k_1814_);
lean_ctor_set(v___x_2053_, 0, v___x_1962_);
v___x_2057_ = v___x_2053_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_1962_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_k_1814_);
lean_ctor_set(v_reuseFailAlloc_2061_, 2, v_v_1815_);
lean_ctor_set(v_reuseFailAlloc_2061_, 3, v_r_2049_);
lean_ctor_set(v_reuseFailAlloc_2061_, 4, v_r_2049_);
v___x_2057_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2059_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 4, v___x_2057_);
lean_ctor_set(v___x_1819_, 3, v_l_2048_);
lean_ctor_set(v___x_1819_, 2, v_v_2051_);
lean_ctor_set(v___x_1819_, 1, v_k_2050_);
lean_ctor_set(v___x_1819_, 0, v___x_2055_);
v___x_2059_ = v___x_1819_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_k_2050_);
lean_ctor_set(v_reuseFailAlloc_2060_, 2, v_v_2051_);
lean_ctor_set(v_reuseFailAlloc_2060_, 3, v_l_2048_);
lean_ctor_set(v_reuseFailAlloc_2060_, 4, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
else
{
lean_object* v_r_2065_; 
v_r_2065_ = lean_ctor_get(v_impl_1961_, 4);
lean_inc(v_r_2065_);
if (lean_obj_tag(v_r_2065_) == 0)
{
lean_object* v_k_2066_; lean_object* v_v_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2090_; 
v_k_2066_ = lean_ctor_get(v_impl_1961_, 1);
v_v_2067_ = lean_ctor_get(v_impl_1961_, 2);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_impl_1961_);
if (v_isSharedCheck_2090_ == 0)
{
lean_object* v_unused_2091_; lean_object* v_unused_2092_; lean_object* v_unused_2093_; 
v_unused_2091_ = lean_ctor_get(v_impl_1961_, 4);
lean_dec(v_unused_2091_);
v_unused_2092_ = lean_ctor_get(v_impl_1961_, 3);
lean_dec(v_unused_2092_);
v_unused_2093_ = lean_ctor_get(v_impl_1961_, 0);
lean_dec(v_unused_2093_);
v___x_2069_ = v_impl_1961_;
v_isShared_2070_ = v_isSharedCheck_2090_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_v_2067_);
lean_inc(v_k_2066_);
lean_dec(v_impl_1961_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2090_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v_k_2071_; lean_object* v_v_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2086_; 
v_k_2071_ = lean_ctor_get(v_r_2065_, 1);
v_v_2072_ = lean_ctor_get(v_r_2065_, 2);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_r_2065_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; lean_object* v_unused_2088_; lean_object* v_unused_2089_; 
v_unused_2087_ = lean_ctor_get(v_r_2065_, 4);
lean_dec(v_unused_2087_);
v_unused_2088_ = lean_ctor_get(v_r_2065_, 3);
lean_dec(v_unused_2088_);
v_unused_2089_ = lean_ctor_get(v_r_2065_, 0);
lean_dec(v_unused_2089_);
v___x_2074_ = v_r_2065_;
v_isShared_2075_ = v_isSharedCheck_2086_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_v_2072_);
lean_inc(v_k_2071_);
lean_dec(v_r_2065_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2086_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2076_ = lean_unsigned_to_nat(3u);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 4, v_l_2048_);
lean_ctor_set(v___x_2074_, 3, v_l_2048_);
lean_ctor_set(v___x_2074_, 2, v_v_2067_);
lean_ctor_set(v___x_2074_, 1, v_k_2066_);
lean_ctor_set(v___x_2074_, 0, v___x_1962_);
v___x_2078_ = v___x_2074_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_1962_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_k_2066_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_v_2067_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_l_2048_);
lean_ctor_set(v_reuseFailAlloc_2085_, 4, v_l_2048_);
v___x_2078_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2080_; 
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 4, v_l_2048_);
lean_ctor_set(v___x_2069_, 2, v_v_1815_);
lean_ctor_set(v___x_2069_, 1, v_k_1814_);
lean_ctor_set(v___x_2069_, 0, v___x_1962_);
v___x_2080_ = v___x_2069_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_1962_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_k_1814_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_v_1815_);
lean_ctor_set(v_reuseFailAlloc_2084_, 3, v_l_2048_);
lean_ctor_set(v_reuseFailAlloc_2084_, 4, v_l_2048_);
v___x_2080_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2082_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 4, v___x_2080_);
lean_ctor_set(v___x_1819_, 3, v___x_2078_);
lean_ctor_set(v___x_1819_, 2, v_v_2072_);
lean_ctor_set(v___x_1819_, 1, v_k_2071_);
lean_ctor_set(v___x_1819_, 0, v___x_2076_);
v___x_2082_ = v___x_1819_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_k_2071_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v_v_2072_);
lean_ctor_set(v_reuseFailAlloc_2083_, 3, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2083_, 4, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2096_; 
v___x_2094_ = lean_unsigned_to_nat(2u);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 4, v_r_2065_);
lean_ctor_set(v___x_1819_, 3, v_impl_1961_);
lean_ctor_set(v___x_1819_, 0, v___x_2094_);
v___x_2096_ = v___x_1819_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_k_1814_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v_v_1815_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v_impl_1961_);
lean_ctor_set(v_reuseFailAlloc_2097_, 4, v_r_2065_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_unsigned_to_nat(1u);
v___x_2100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
lean_ctor_set(v___x_2100_, 1, v_k_1810_);
lean_ctor_set(v___x_2100_, 2, v_v_1811_);
lean_ctor_set(v___x_2100_, 3, v_t_1812_);
lean_ctor_set(v___x_2100_, 4, v_t_1812_);
return v___x_2100_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(lean_object* v_k_2101_, lean_object* v_t_2102_){
_start:
{
if (lean_obj_tag(v_t_2102_) == 0)
{
lean_object* v_k_2103_; lean_object* v_l_2104_; lean_object* v_r_2105_; uint8_t v___x_2106_; 
v_k_2103_ = lean_ctor_get(v_t_2102_, 1);
v_l_2104_ = lean_ctor_get(v_t_2102_, 3);
v_r_2105_ = lean_ctor_get(v_t_2102_, 4);
v___x_2106_ = lean_nat_dec_lt(v_k_2101_, v_k_2103_);
if (v___x_2106_ == 0)
{
uint8_t v___x_2107_; 
v___x_2107_ = lean_nat_dec_eq(v_k_2101_, v_k_2103_);
if (v___x_2107_ == 0)
{
v_t_2102_ = v_r_2105_;
goto _start;
}
else
{
return v___x_2107_;
}
}
else
{
v_t_2102_ = v_l_2104_;
goto _start;
}
}
else
{
uint8_t v___x_2110_; 
v___x_2110_ = 0;
return v___x_2110_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg___boxed(lean_object* v_k_2111_, lean_object* v_t_2112_){
_start:
{
uint8_t v_res_2113_; lean_object* v_r_2114_; 
v_res_2113_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2111_, v_t_2112_);
lean_dec(v_t_2112_);
lean_dec(v_k_2111_);
v_r_2114_ = lean_box(v_res_2113_);
return v_r_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(lean_object* v_y_2115_, lean_object* v_x_2116_, size_t v_x_2117_, size_t v_x_2118_){
_start:
{
if (lean_obj_tag(v_x_2116_) == 0)
{
lean_object* v_cs_2119_; size_t v_j_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; 
v_cs_2119_ = lean_ctor_get(v_x_2116_, 0);
v_j_2120_ = lean_usize_shift_right(v_x_2117_, v_x_2118_);
v___x_2121_ = lean_usize_to_nat(v_j_2120_);
v___x_2122_ = lean_array_get_size(v_cs_2119_);
v___x_2123_ = lean_nat_dec_lt(v___x_2121_, v___x_2122_);
if (v___x_2123_ == 0)
{
lean_dec(v___x_2121_);
lean_dec(v_y_2115_);
return v_x_2116_;
}
else
{
lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2141_; 
lean_inc_ref(v_cs_2119_);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_x_2116_);
if (v_isSharedCheck_2141_ == 0)
{
lean_object* v_unused_2142_; 
v_unused_2142_ = lean_ctor_get(v_x_2116_, 0);
lean_dec(v_unused_2142_);
v___x_2125_ = v_x_2116_;
v_isShared_2126_ = v_isSharedCheck_2141_;
goto v_resetjp_2124_;
}
else
{
lean_dec(v_x_2116_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2141_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
size_t v___x_2127_; size_t v___x_2128_; size_t v___x_2129_; size_t v_i_2130_; size_t v___x_2131_; size_t v_shift_2132_; lean_object* v_v_2133_; lean_object* v___x_2134_; lean_object* v_xs_x27_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2127_ = ((size_t)1ULL);
v___x_2128_ = lean_usize_shift_left(v___x_2127_, v_x_2118_);
v___x_2129_ = lean_usize_sub(v___x_2128_, v___x_2127_);
v_i_2130_ = lean_usize_land(v_x_2117_, v___x_2129_);
v___x_2131_ = ((size_t)5ULL);
v_shift_2132_ = lean_usize_sub(v_x_2118_, v___x_2131_);
v_v_2133_ = lean_array_fget(v_cs_2119_, v___x_2121_);
v___x_2134_ = lean_box(0);
v_xs_x27_2135_ = lean_array_fset(v_cs_2119_, v___x_2121_, v___x_2134_);
v___x_2136_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2115_, v_v_2133_, v_i_2130_, v_shift_2132_);
v___x_2137_ = lean_array_fset(v_xs_x27_2135_, v___x_2121_, v___x_2136_);
lean_dec(v___x_2121_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v___x_2137_);
v___x_2139_ = v___x_2125_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v_vs_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v_vs_2143_ = lean_ctor_get(v_x_2116_, 0);
v___x_2144_ = lean_usize_to_nat(v_x_2117_);
v___x_2145_ = lean_array_get_size(v_vs_2143_);
v___x_2146_ = lean_nat_dec_lt(v___x_2144_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_dec(v___x_2144_);
lean_dec(v_y_2115_);
return v_x_2116_;
}
else
{
lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2161_; 
lean_inc_ref(v_vs_2143_);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_x_2116_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; 
v_unused_2162_ = lean_ctor_get(v_x_2116_, 0);
lean_dec(v_unused_2162_);
v___x_2148_ = v_x_2116_;
v_isShared_2149_ = v_isSharedCheck_2161_;
goto v_resetjp_2147_;
}
else
{
lean_dec(v_x_2116_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2161_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v_v_2150_; lean_object* v___x_2151_; lean_object* v_xs_x27_2152_; lean_object* v___y_2154_; uint8_t v___x_2159_; 
v_v_2150_ = lean_array_fget(v_vs_2143_, v___x_2144_);
v___x_2151_ = lean_box(0);
v_xs_x27_2152_ = lean_array_fset(v_vs_2143_, v___x_2144_, v___x_2151_);
v___x_2159_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2115_, v_v_2150_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2115_, v___x_2151_, v_v_2150_);
v___y_2154_ = v___x_2160_;
goto v___jp_2153_;
}
else
{
lean_dec(v_y_2115_);
v___y_2154_ = v_v_2150_;
goto v___jp_2153_;
}
v___jp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2157_; 
v___x_2155_ = lean_array_fset(v_xs_x27_2152_, v___x_2144_, v___y_2154_);
lean_dec(v___x_2144_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2155_);
v___x_2157_ = v___x_2148_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2163_, lean_object* v_x_2164_, lean_object* v_x_2165_, lean_object* v_x_2166_){
_start:
{
size_t v_x_4533__boxed_2167_; size_t v_x_4534__boxed_2168_; lean_object* v_res_2169_; 
v_x_4533__boxed_2167_ = lean_unbox_usize(v_x_2165_);
lean_dec(v_x_2165_);
v_x_4534__boxed_2168_ = lean_unbox_usize(v_x_2166_);
lean_dec(v_x_2166_);
v_res_2169_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2163_, v_x_2164_, v_x_4533__boxed_2167_, v_x_4534__boxed_2168_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(lean_object* v_y_2170_, lean_object* v_t_2171_, lean_object* v_i_2172_){
_start:
{
lean_object* v_root_2173_; lean_object* v_tail_2174_; lean_object* v_size_2175_; size_t v_shift_2176_; lean_object* v_tailOff_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2204_; 
v_root_2173_ = lean_ctor_get(v_t_2171_, 0);
v_tail_2174_ = lean_ctor_get(v_t_2171_, 1);
v_size_2175_ = lean_ctor_get(v_t_2171_, 2);
v_shift_2176_ = lean_ctor_get_usize(v_t_2171_, 4);
v_tailOff_2177_ = lean_ctor_get(v_t_2171_, 3);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_t_2171_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2179_ = v_t_2171_;
v_isShared_2180_ = v_isSharedCheck_2204_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_tailOff_2177_);
lean_inc(v_size_2175_);
lean_inc(v_tail_2174_);
lean_inc(v_root_2173_);
lean_dec(v_t_2171_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2204_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
uint8_t v___x_2181_; 
v___x_2181_ = lean_nat_dec_le(v_tailOff_2177_, v_i_2172_);
if (v___x_2181_ == 0)
{
size_t v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2182_ = lean_usize_of_nat(v_i_2172_);
v___x_2183_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2170_, v_root_2173_, v___x_2182_, v_shift_2176_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2183_);
v___x_2185_ = v___x_2179_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_tail_2174_);
lean_ctor_set(v_reuseFailAlloc_2186_, 2, v_size_2175_);
lean_ctor_set(v_reuseFailAlloc_2186_, 3, v_tailOff_2177_);
lean_ctor_set_usize(v_reuseFailAlloc_2186_, 4, v_shift_2176_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
else
{
lean_object* v___x_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; 
v___x_2187_ = lean_nat_sub(v_i_2172_, v_tailOff_2177_);
v___x_2188_ = lean_array_get_size(v_tail_2174_);
v___x_2189_ = lean_nat_dec_lt(v___x_2187_, v___x_2188_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2191_; 
lean_dec(v___x_2187_);
lean_dec(v_y_2170_);
if (v_isShared_2180_ == 0)
{
v___x_2191_ = v___x_2179_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_root_2173_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_tail_2174_);
lean_ctor_set(v_reuseFailAlloc_2192_, 2, v_size_2175_);
lean_ctor_set(v_reuseFailAlloc_2192_, 3, v_tailOff_2177_);
lean_ctor_set_usize(v_reuseFailAlloc_2192_, 4, v_shift_2176_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
else
{
lean_object* v_v_2193_; lean_object* v___x_2194_; lean_object* v_xs_x27_2195_; lean_object* v___y_2197_; uint8_t v___x_2202_; 
v_v_2193_ = lean_array_fget(v_tail_2174_, v___x_2187_);
v___x_2194_ = lean_box(0);
v_xs_x27_2195_ = lean_array_fset(v_tail_2174_, v___x_2187_, v___x_2194_);
v___x_2202_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2170_, v_v_2193_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2170_, v___x_2194_, v_v_2193_);
v___y_2197_ = v___x_2203_;
goto v___jp_2196_;
}
else
{
lean_dec(v_y_2170_);
v___y_2197_ = v_v_2193_;
goto v___jp_2196_;
}
v___jp_2196_:
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2198_ = lean_array_fset(v_xs_x27_2195_, v___x_2187_, v___y_2197_);
lean_dec(v___x_2187_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 1, v___x_2198_);
v___x_2200_ = v___x_2179_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_root_2173_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_size_2175_);
lean_ctor_set(v_reuseFailAlloc_2201_, 3, v_tailOff_2177_);
lean_ctor_set_usize(v_reuseFailAlloc_2201_, 4, v_shift_2176_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2___boxed(lean_object* v_y_2205_, lean_object* v_t_2206_, lean_object* v_i_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2205_, v_t_2206_, v_i_2207_);
lean_dec(v_i_2207_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(lean_object* v_y_2209_, lean_object* v_x_2210_, lean_object* v_s_2211_){
_start:
{
lean_object* v_vars_2212_; lean_object* v_varMap_2213_; lean_object* v_vars_x27_2214_; lean_object* v_varMap_x27_2215_; lean_object* v_natToIntMap_2216_; lean_object* v_natDef_2217_; lean_object* v_dvds_2218_; lean_object* v_lowers_2219_; lean_object* v_uppers_2220_; lean_object* v_diseqs_2221_; lean_object* v_elimEqs_2222_; lean_object* v_elimStack_2223_; lean_object* v_occurs_2224_; lean_object* v_assignment_2225_; lean_object* v_nextCnstrId_2226_; uint8_t v_caseSplits_2227_; lean_object* v_conflict_x3f_2228_; lean_object* v_diseqSplits_2229_; lean_object* v_divMod_2230_; lean_object* v_toIntIds_2231_; lean_object* v_toIntInfos_2232_; lean_object* v_toIntTermMap_2233_; lean_object* v_toIntVarMap_2234_; uint8_t v_usedCommRing_2235_; lean_object* v_nonlinearOccs_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2244_; 
v_vars_2212_ = lean_ctor_get(v_s_2211_, 0);
v_varMap_2213_ = lean_ctor_get(v_s_2211_, 1);
v_vars_x27_2214_ = lean_ctor_get(v_s_2211_, 2);
v_varMap_x27_2215_ = lean_ctor_get(v_s_2211_, 3);
v_natToIntMap_2216_ = lean_ctor_get(v_s_2211_, 4);
v_natDef_2217_ = lean_ctor_get(v_s_2211_, 5);
v_dvds_2218_ = lean_ctor_get(v_s_2211_, 6);
v_lowers_2219_ = lean_ctor_get(v_s_2211_, 7);
v_uppers_2220_ = lean_ctor_get(v_s_2211_, 8);
v_diseqs_2221_ = lean_ctor_get(v_s_2211_, 9);
v_elimEqs_2222_ = lean_ctor_get(v_s_2211_, 10);
v_elimStack_2223_ = lean_ctor_get(v_s_2211_, 11);
v_occurs_2224_ = lean_ctor_get(v_s_2211_, 12);
v_assignment_2225_ = lean_ctor_get(v_s_2211_, 13);
v_nextCnstrId_2226_ = lean_ctor_get(v_s_2211_, 14);
v_caseSplits_2227_ = lean_ctor_get_uint8(v_s_2211_, sizeof(void*)*23);
v_conflict_x3f_2228_ = lean_ctor_get(v_s_2211_, 15);
v_diseqSplits_2229_ = lean_ctor_get(v_s_2211_, 16);
v_divMod_2230_ = lean_ctor_get(v_s_2211_, 17);
v_toIntIds_2231_ = lean_ctor_get(v_s_2211_, 18);
v_toIntInfos_2232_ = lean_ctor_get(v_s_2211_, 19);
v_toIntTermMap_2233_ = lean_ctor_get(v_s_2211_, 20);
v_toIntVarMap_2234_ = lean_ctor_get(v_s_2211_, 21);
v_usedCommRing_2235_ = lean_ctor_get_uint8(v_s_2211_, sizeof(void*)*23 + 1);
v_nonlinearOccs_2236_ = lean_ctor_get(v_s_2211_, 22);
v_isSharedCheck_2244_ = !lean_is_exclusive(v_s_2211_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2238_ = v_s_2211_;
v_isShared_2239_ = v_isSharedCheck_2244_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_nonlinearOccs_2236_);
lean_inc(v_toIntVarMap_2234_);
lean_inc(v_toIntTermMap_2233_);
lean_inc(v_toIntInfos_2232_);
lean_inc(v_toIntIds_2231_);
lean_inc(v_divMod_2230_);
lean_inc(v_diseqSplits_2229_);
lean_inc(v_conflict_x3f_2228_);
lean_inc(v_nextCnstrId_2226_);
lean_inc(v_assignment_2225_);
lean_inc(v_occurs_2224_);
lean_inc(v_elimStack_2223_);
lean_inc(v_elimEqs_2222_);
lean_inc(v_diseqs_2221_);
lean_inc(v_uppers_2220_);
lean_inc(v_lowers_2219_);
lean_inc(v_dvds_2218_);
lean_inc(v_natDef_2217_);
lean_inc(v_natToIntMap_2216_);
lean_inc(v_varMap_x27_2215_);
lean_inc(v_vars_x27_2214_);
lean_inc(v_varMap_2213_);
lean_inc(v_vars_2212_);
lean_dec(v_s_2211_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2244_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2240_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2209_, v_occurs_2224_, v_x_2210_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 12, v___x_2240_);
v___x_2242_ = v___x_2238_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_vars_2212_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_varMap_2213_);
lean_ctor_set(v_reuseFailAlloc_2243_, 2, v_vars_x27_2214_);
lean_ctor_set(v_reuseFailAlloc_2243_, 3, v_varMap_x27_2215_);
lean_ctor_set(v_reuseFailAlloc_2243_, 4, v_natToIntMap_2216_);
lean_ctor_set(v_reuseFailAlloc_2243_, 5, v_natDef_2217_);
lean_ctor_set(v_reuseFailAlloc_2243_, 6, v_dvds_2218_);
lean_ctor_set(v_reuseFailAlloc_2243_, 7, v_lowers_2219_);
lean_ctor_set(v_reuseFailAlloc_2243_, 8, v_uppers_2220_);
lean_ctor_set(v_reuseFailAlloc_2243_, 9, v_diseqs_2221_);
lean_ctor_set(v_reuseFailAlloc_2243_, 10, v_elimEqs_2222_);
lean_ctor_set(v_reuseFailAlloc_2243_, 11, v_elimStack_2223_);
lean_ctor_set(v_reuseFailAlloc_2243_, 12, v___x_2240_);
lean_ctor_set(v_reuseFailAlloc_2243_, 13, v_assignment_2225_);
lean_ctor_set(v_reuseFailAlloc_2243_, 14, v_nextCnstrId_2226_);
lean_ctor_set(v_reuseFailAlloc_2243_, 15, v_conflict_x3f_2228_);
lean_ctor_set(v_reuseFailAlloc_2243_, 16, v_diseqSplits_2229_);
lean_ctor_set(v_reuseFailAlloc_2243_, 17, v_divMod_2230_);
lean_ctor_set(v_reuseFailAlloc_2243_, 18, v_toIntIds_2231_);
lean_ctor_set(v_reuseFailAlloc_2243_, 19, v_toIntInfos_2232_);
lean_ctor_set(v_reuseFailAlloc_2243_, 20, v_toIntTermMap_2233_);
lean_ctor_set(v_reuseFailAlloc_2243_, 21, v_toIntVarMap_2234_);
lean_ctor_set(v_reuseFailAlloc_2243_, 22, v_nonlinearOccs_2236_);
lean_ctor_set_uint8(v_reuseFailAlloc_2243_, sizeof(void*)*23, v_caseSplits_2227_);
lean_ctor_set_uint8(v_reuseFailAlloc_2243_, sizeof(void*)*23 + 1, v_usedCommRing_2235_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed(lean_object* v_y_2245_, lean_object* v_x_2246_, lean_object* v_s_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(v_y_2245_, v_x_2246_, v_s_2247_);
lean_dec(v_x_2246_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(lean_object* v_x_2249_, lean_object* v_y_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2249_, v_a_2251_, v_a_2252_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2267_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2257_ = v___x_2254_;
v_isShared_2258_ = v_isSharedCheck_2267_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2254_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2267_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
uint8_t v___x_2259_; 
v___x_2259_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2250_, v_a_2255_);
lean_dec(v_a_2255_);
if (v___x_2259_ == 0)
{
lean_object* v___f_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_del_object(v___x_2257_);
v___f_2260_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2260_, 0, v_y_2250_);
lean_closure_set(v___f_2260_, 1, v_x_2249_);
v___x_2261_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2262_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2261_, v___f_2260_, v_a_2251_);
return v___x_2262_;
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2265_; 
lean_dec(v_y_2250_);
lean_dec(v_x_2249_);
v___x_2263_ = lean_box(0);
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 0, v___x_2263_);
v___x_2265_ = v___x_2257_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec(v_y_2250_);
lean_dec(v_x_2249_);
v_a_2268_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2254_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2254_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___boxed(lean_object* v_x_2276_, lean_object* v_y_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2276_, v_y_2277_, v_a_2278_, v_a_2279_);
lean_dec_ref(v_a_2279_);
lean_dec(v_a_2278_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc(lean_object* v_x_2282_, lean_object* v_y_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2282_, v_y_2283_, v_a_2284_, v_a_2292_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___boxed(lean_object* v_x_2296_, lean_object* v_y_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc(v_x_2296_, v_y_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
lean_dec(v_a_2299_);
lean_dec(v_a_2298_);
return v_res_2309_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(lean_object* v_00_u03b2_2310_, lean_object* v_k_2311_, lean_object* v_t_2312_){
_start:
{
uint8_t v___x_2313_; 
v___x_2313_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2311_, v_t_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2314_, lean_object* v_k_2315_, lean_object* v_t_2316_){
_start:
{
uint8_t v_res_2317_; lean_object* v_r_2318_; 
v_res_2317_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(v_00_u03b2_2314_, v_k_2315_, v_t_2316_);
lean_dec(v_t_2316_);
lean_dec(v_k_2315_);
v_r_2318_ = lean_box(v_res_2317_);
return v_r_2318_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1(lean_object* v_00_u03b2_2319_, lean_object* v_k_2320_, lean_object* v_v_2321_, lean_object* v_t_2322_, lean_object* v_hl_2323_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2320_, v_v_2321_, v_t_2322_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(lean_object* v_y_2325_, lean_object* v_p_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
if (lean_obj_tag(v_p_2326_) == 1)
{
lean_object* v_v_2330_; lean_object* v_p_2331_; lean_object* v___x_2332_; 
v_v_2330_ = lean_ctor_get(v_p_2326_, 1);
lean_inc(v_v_2330_);
v_p_2331_ = lean_ctor_get(v_p_2326_, 2);
lean_inc_ref(v_p_2331_);
lean_dec_ref_known(v_p_2326_, 3);
lean_inc(v_y_2325_);
v___x_2332_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_v_2330_, v_y_2325_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_dec_ref_known(v___x_2332_, 1);
v_p_2326_ = v_p_2331_;
goto _start;
}
else
{
lean_dec_ref(v_p_2331_);
lean_dec(v_y_2325_);
return v___x_2332_;
}
}
else
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
lean_dec_ref(v_p_2326_);
lean_dec(v_y_2325_);
v___x_2334_ = lean_box(0);
v___x_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
return v___x_2335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg___boxed(lean_object* v_y_2336_, lean_object* v_p_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2336_, v_p_2337_, v_a_2338_, v_a_2339_);
lean_dec_ref(v_a_2339_);
lean_dec(v_a_2338_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(lean_object* v_y_2342_, lean_object* v_p_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2342_, v_p_2343_, v_a_2344_, v_a_2352_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___boxed(lean_object* v_y_2356_, lean_object* v_p_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(v_y_2356_, v_p_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
lean_dec(v_a_2367_);
lean_dec_ref(v_a_2366_);
lean_dec(v_a_2365_);
lean_dec_ref(v_a_2364_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
lean_dec(v_a_2361_);
lean_dec_ref(v_a_2360_);
lean_dec(v_a_2359_);
lean_dec(v_a_2358_);
return v_res_2369_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = ((lean_object*)(l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__0));
v___x_2372_ = l_Lean_stringToMessageData(v___x_2371_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg(lean_object* v_p_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
if (lean_obj_tag(v_p_2373_) == 1)
{
lean_object* v_v_2380_; lean_object* v_p_2381_; lean_object* v___x_2382_; 
v_v_2380_ = lean_ctor_get(v_p_2373_, 1);
lean_inc(v_v_2380_);
v_p_2381_ = lean_ctor_get(v_p_2373_, 2);
lean_inc_ref(v_p_2381_);
lean_dec_ref_known(v_p_2373_, 3);
v___x_2382_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_v_2380_, v_p_2381_, v_a_2374_, v_a_2377_);
return v___x_2382_;
}
else
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
lean_dec_ref(v_p_2373_);
v___x_2383_ = lean_obj_once(&l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1, &l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1_once, _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1);
v___x_2384_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2383_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
return v___x_2384_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg___boxed(lean_object* v_p_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs(lean_object* v_p_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2393_, v_a_2394_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___boxed(lean_object* v_p_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Int_Internal_Linear_Poly_updateOccs(v_p_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
lean_dec(v_a_2408_);
lean_dec(v_a_2407_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go_spec__0(lean_object* v_a_2419_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Rat_ofInt(v_a_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(lean_object* v_a_2421_, lean_object* v_v_2422_, lean_object* v_a_2423_){
_start:
{
if (lean_obj_tag(v_a_2423_) == 0)
{
lean_object* v_k_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2433_; 
v_k_2424_ = lean_ctor_get(v_a_2423_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_a_2423_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2426_ = v_a_2423_;
v_isShared_2427_ = v_isSharedCheck_2433_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_k_2424_);
lean_dec(v_a_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2433_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2431_; 
v___x_2428_ = l_Rat_ofInt(v_k_2424_);
v___x_2429_ = l_Rat_add(v_v_2422_, v___x_2428_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set_tag(v___x_2426_, 1);
lean_ctor_set(v___x_2426_, 0, v___x_2429_);
v___x_2431_ = v___x_2426_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
else
{
lean_object* v_k_2434_; lean_object* v_v_2435_; lean_object* v_p_2436_; lean_object* v_size_2437_; uint8_t v___x_2438_; 
v_k_2434_ = lean_ctor_get(v_a_2423_, 0);
lean_inc(v_k_2434_);
v_v_2435_ = lean_ctor_get(v_a_2423_, 1);
lean_inc(v_v_2435_);
v_p_2436_ = lean_ctor_get(v_a_2423_, 2);
lean_inc_ref(v_p_2436_);
lean_dec_ref_known(v_a_2423_, 3);
v_size_2437_ = lean_ctor_get(v_a_2421_, 2);
v___x_2438_ = lean_nat_dec_lt(v_v_2435_, v_size_2437_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; 
lean_dec_ref(v_p_2436_);
lean_dec(v_v_2435_);
lean_dec(v_k_2434_);
lean_dec_ref(v_v_2422_);
v___x_2439_ = lean_box(0);
return v___x_2439_;
}
else
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2440_ = l_Rat_ofInt(v_k_2434_);
v___x_2441_ = l_instInhabitedRat;
v___x_2442_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2441_, v_a_2421_, v_v_2435_);
lean_dec(v_v_2435_);
v___x_2443_ = l_Rat_mul(v___x_2440_, v___x_2442_);
lean_dec_ref(v___x_2440_);
v___x_2444_ = l_Rat_add(v_v_2422_, v___x_2443_);
v_v_2422_ = v___x_2444_;
v_a_2423_ = v_p_2436_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go___boxed(lean_object* v_a_2446_, lean_object* v_v_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_a_2446_, v_v_2447_, v_a_2448_);
lean_dec_ref(v_a_2446_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(lean_object* v_a_2450_){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = lean_nat_to_int(v_a_2450_);
v___x_2452_ = l_Rat_ofInt(v___x_2451_);
return v___x_2452_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_unsigned_to_nat(0u);
v___x_2454_ = l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(v___x_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg(lean_object* v_p_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2456_, v_a_2457_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2470_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2462_ = v___x_2459_;
v_isShared_2463_ = v_isSharedCheck_2470_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2470_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v_assignment_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2468_; 
v_assignment_2464_ = lean_ctor_get(v_a_2460_, 13);
lean_inc_ref(v_assignment_2464_);
lean_dec(v_a_2460_);
v___x_2465_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2466_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_assignment_2464_, v___x_2465_, v_p_2455_);
lean_dec_ref(v_assignment_2464_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v___x_2466_);
v___x_2468_ = v___x_2462_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
lean_dec_ref(v_p_2455_);
v_a_2471_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2459_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2459_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg___boxed(lean_object* v_p_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2479_, v_a_2480_, v_a_2481_);
lean_dec_ref(v_a_2481_);
lean_dec(v_a_2480_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f(lean_object* v_p_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2484_, v_a_2485_, v_a_2493_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___boxed(lean_object* v_p_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Int_Internal_Linear_Poly_eval_x3f(v_p_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_);
lean_dec(v_a_2507_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec(v_a_2498_);
return v_res_2509_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(lean_object* v_c_2510_){
_start:
{
lean_object* v_p_2511_; uint8_t v___x_2512_; 
v_p_2511_ = lean_ctor_get(v_c_2510_, 0);
v___x_2512_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat___boxed(lean_object* v_c_2513_){
_start:
{
uint8_t v_res_2514_; lean_object* v_r_2515_; 
v_res_2514_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(v_c_2513_);
lean_dec_ref(v_c_2513_);
v_r_2515_ = lean_box(v_res_2514_);
return v_r_2515_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(lean_object* v_c_2516_){
_start:
{
lean_object* v_d_2517_; lean_object* v_p_2518_; uint8_t v___x_2519_; 
v_d_2517_ = lean_ctor_get(v_c_2516_, 0);
lean_inc(v_d_2517_);
v_p_2518_ = lean_ctor_get(v_c_2516_, 1);
lean_inc_ref(v_p_2518_);
lean_dec_ref(v_c_2516_);
v___x_2519_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_2517_, v_p_2518_);
lean_dec_ref(v_p_2518_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat___boxed(lean_object* v_c_2520_){
_start:
{
uint8_t v_res_2521_; lean_object* v_r_2522_; 
v_res_2521_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(v_c_2520_);
v_r_2522_ = lean_box(v_res_2521_);
return v_r_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object* v_c_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v_d_2527_; lean_object* v_p_2528_; lean_object* v___x_2529_; 
v_d_2527_ = lean_ctor_get(v_c_2523_, 0);
lean_inc(v_d_2527_);
v_p_2528_ = lean_ctor_get(v_c_2523_, 1);
lean_inc_ref(v_p_2528_);
lean_dec_ref(v_c_2523_);
v___x_2529_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2528_, v_a_2524_, v_a_2525_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2555_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2532_ = v___x_2529_;
v_isShared_2533_ = v_isSharedCheck_2555_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2555_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
if (lean_obj_tag(v_a_2530_) == 1)
{
lean_object* v_val_2534_; lean_object* v_num_2535_; lean_object* v_den_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; 
v_val_2534_ = lean_ctor_get(v_a_2530_, 0);
lean_inc(v_val_2534_);
lean_dec_ref_known(v_a_2530_, 1);
v_num_2535_ = lean_ctor_get(v_val_2534_, 0);
lean_inc(v_num_2535_);
v_den_2536_ = lean_ctor_get(v_val_2534_, 1);
lean_inc(v_den_2536_);
lean_dec(v_val_2534_);
v___x_2537_ = lean_unsigned_to_nat(1u);
v___x_2538_ = lean_nat_dec_eq(v_den_2536_, v___x_2537_);
lean_dec(v_den_2536_);
if (v___x_2538_ == 0)
{
uint8_t v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2542_; 
lean_dec(v_num_2535_);
lean_dec(v_d_2527_);
v___x_2539_ = 0;
v___x_2540_ = lean_box(v___x_2539_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2540_);
v___x_2542_ = v___x_2532_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
else
{
uint8_t v___x_2544_; uint8_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2548_; 
v___x_2544_ = l_Int_decidableDvd(v_d_2527_, v_num_2535_);
lean_dec(v_num_2535_);
lean_dec(v_d_2527_);
v___x_2545_ = l_Lean_Bool_toLBool(v___x_2544_);
v___x_2546_ = lean_box(v___x_2545_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2546_);
v___x_2548_ = v___x_2532_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2546_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
else
{
uint8_t v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2553_; 
lean_dec(v_a_2530_);
lean_dec(v_d_2527_);
v___x_2550_ = 2;
v___x_2551_ = lean_box(v___x_2550_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2551_);
v___x_2553_ = v___x_2532_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec(v_d_2527_);
v_a_2556_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2529_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2529_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg___boxed(lean_object* v_c_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2564_, v_a_2565_, v_a_2566_);
lean_dec_ref(v_a_2566_);
lean_dec(v_a_2565_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(lean_object* v_c_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2569_, v_a_2570_, v_a_2578_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___boxed(lean_object* v_c_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(v_c_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_);
lean_dec(v_a_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
lean_dec(v_a_2584_);
lean_dec(v_a_2583_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg(lean_object* v_p_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2595_, v_a_2596_, v_a_2597_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2617_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2602_ = v___x_2599_;
v_isShared_2603_ = v_isSharedCheck_2617_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2599_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2617_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
if (lean_obj_tag(v_a_2600_) == 1)
{
lean_object* v_val_2604_; lean_object* v___x_2605_; uint8_t v___x_2606_; uint8_t v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2610_; 
v_val_2604_ = lean_ctor_get(v_a_2600_, 0);
lean_inc(v_val_2604_);
lean_dec_ref_known(v_a_2600_, 1);
v___x_2605_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2606_ = l_Rat_instDecidableLe(v_val_2604_, v___x_2605_);
v___x_2607_ = l_Lean_Bool_toLBool(v___x_2606_);
v___x_2608_ = lean_box(v___x_2607_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v___x_2608_);
v___x_2610_ = v___x_2602_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
else
{
uint8_t v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2615_; 
lean_dec(v_a_2600_);
v___x_2612_ = 2;
v___x_2613_ = lean_box(v___x_2612_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v___x_2613_);
v___x_2615_ = v___x_2602_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2613_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
v_a_2618_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2599_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2599_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg___boxed(lean_object* v_p_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2626_, v_a_2627_, v_a_2628_);
lean_dec_ref(v_a_2628_);
lean_dec(v_a_2627_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe(lean_object* v_p_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2631_, v_a_2632_, v_a_2640_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___boxed(lean_object* v_p_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Int_Internal_Linear_Poly_satisfiedLe(v_p_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec(v_a_2645_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(lean_object* v_c_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v_p_2661_; lean_object* v___x_2662_; 
v_p_2661_ = lean_ctor_get(v_c_2657_, 0);
lean_inc_ref(v_p_2661_);
lean_dec_ref(v_c_2657_);
v___x_2662_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2661_, v_a_2658_, v_a_2659_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg___boxed(lean_object* v_c_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2663_, v_a_2664_, v_a_2665_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(lean_object* v_c_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2668_, v_a_2669_, v_a_2677_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___boxed(lean_object* v_c_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(v_c_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
lean_dec(v_a_2683_);
lean_dec(v_a_2682_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(lean_object* v_c_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v_p_2698_; lean_object* v___x_2699_; 
v_p_2698_ = lean_ctor_get(v_c_2694_, 0);
lean_inc_ref(v_p_2698_);
lean_dec_ref(v_c_2694_);
v___x_2699_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2698_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2719_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2702_ = v___x_2699_;
v_isShared_2703_ = v_isSharedCheck_2719_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2699_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2719_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
uint8_t v___y_2705_; 
if (lean_obj_tag(v_a_2700_) == 1)
{
lean_object* v_val_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; 
v_val_2711_ = lean_ctor_get(v_a_2700_, 0);
lean_inc(v_val_2711_);
lean_dec_ref_known(v_a_2700_, 1);
v___x_2712_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2713_ = l_instDecidableEqRat_decEq(v_val_2711_, v___x_2712_);
lean_dec(v_val_2711_);
if (v___x_2713_ == 0)
{
uint8_t v___x_2714_; 
v___x_2714_ = 1;
v___y_2705_ = v___x_2714_;
goto v___jp_2704_;
}
else
{
uint8_t v___x_2715_; 
v___x_2715_ = 0;
v___y_2705_ = v___x_2715_;
goto v___jp_2704_;
}
}
else
{
uint8_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
lean_del_object(v___x_2702_);
lean_dec(v_a_2700_);
v___x_2716_ = 2;
v___x_2717_ = lean_box(v___x_2716_);
v___x_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
return v___x_2718_;
}
v___jp_2704_:
{
uint8_t v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2709_; 
v___x_2706_ = l_Lean_Bool_toLBool(v___y_2705_);
v___x_2707_ = lean_box(v___x_2706_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v___x_2707_);
v___x_2709_ = v___x_2702_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
v_a_2720_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2699_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2699_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg___boxed(lean_object* v_c_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_2728_, v_a_2729_, v_a_2730_);
lean_dec_ref(v_a_2730_);
lean_dec(v_a_2729_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(lean_object* v_c_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_2733_, v_a_2734_, v_a_2742_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___boxed(lean_object* v_c_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(v_c_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_);
lean_dec(v_a_2756_);
lean_dec_ref(v_a_2755_);
lean_dec(v_a_2754_);
lean_dec_ref(v_a_2753_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec(v_a_2747_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(lean_object* v_c_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v_p_2763_; lean_object* v___x_2764_; 
v_p_2763_ = lean_ctor_get(v_c_2759_, 0);
lean_inc_ref(v_p_2763_);
lean_dec_ref(v_c_2759_);
v___x_2764_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2763_, v_a_2760_, v_a_2761_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2782_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2767_ = v___x_2764_;
v_isShared_2768_ = v_isSharedCheck_2782_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2764_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2782_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
if (lean_obj_tag(v_a_2765_) == 1)
{
lean_object* v_val_2769_; lean_object* v___x_2770_; uint8_t v___x_2771_; uint8_t v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2775_; 
v_val_2769_ = lean_ctor_get(v_a_2765_, 0);
lean_inc(v_val_2769_);
lean_dec_ref_known(v_a_2765_, 1);
v___x_2770_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2771_ = l_instDecidableEqRat_decEq(v_val_2769_, v___x_2770_);
lean_dec(v_val_2769_);
v___x_2772_ = l_Lean_Bool_toLBool(v___x_2771_);
v___x_2773_ = lean_box(v___x_2772_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v___x_2773_);
v___x_2775_ = v___x_2767_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
else
{
uint8_t v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2780_; 
lean_dec(v_a_2765_);
v___x_2777_ = 2;
v___x_2778_ = lean_box(v___x_2777_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v___x_2778_);
v___x_2780_ = v___x_2767_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
v_a_2783_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2764_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2764_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg___boxed(lean_object* v_c_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_2791_, v_a_2792_, v_a_2793_);
lean_dec_ref(v_a_2793_);
lean_dec(v_a_2792_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(lean_object* v_c_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_2796_, v_a_2797_, v_a_2805_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___boxed(lean_object* v_c_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(v_c_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_);
lean_dec(v_a_2819_);
lean_dec_ref(v_a_2818_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2813_);
lean_dec_ref(v_a_2812_);
lean_dec(v_a_2811_);
lean_dec(v_a_2810_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg(lean_object* v_p_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_){
_start:
{
if (lean_obj_tag(v_p_2822_) == 0)
{
lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2833_; 
v_isSharedCheck_2833_ = !lean_is_exclusive(v_p_2822_);
if (v_isSharedCheck_2833_ == 0)
{
lean_object* v_unused_2834_; 
v_unused_2834_ = lean_ctor_get(v_p_2822_, 0);
lean_dec(v_unused_2834_);
v___x_2827_ = v_p_2822_;
v_isShared_2828_ = v_isSharedCheck_2833_;
goto v_resetjp_2826_;
}
else
{
lean_dec(v_p_2822_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2833_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2829_; lean_object* v___x_2831_; 
v___x_2829_ = lean_box(0);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 0, v___x_2829_);
v___x_2831_ = v___x_2827_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2829_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
else
{
lean_object* v_k_2835_; lean_object* v_v_2836_; lean_object* v_p_2837_; lean_object* v___x_2838_; 
v_k_2835_ = lean_ctor_get(v_p_2822_, 0);
lean_inc(v_k_2835_);
v_v_2836_ = lean_ctor_get(v_p_2822_, 1);
lean_inc(v_v_2836_);
v_p_2837_ = lean_ctor_get(v_p_2822_, 2);
lean_inc_ref(v_p_2837_);
lean_dec_ref_known(v_p_2822_, 3);
v___x_2838_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2823_, v_a_2824_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2865_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2865_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2865_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___y_2844_; lean_object* v_elimEqs_2859_; lean_object* v_size_2860_; lean_object* v___x_2861_; uint8_t v___x_2862_; 
v_elimEqs_2859_ = lean_ctor_get(v_a_2839_, 10);
lean_inc_ref(v_elimEqs_2859_);
lean_dec(v_a_2839_);
v_size_2860_ = lean_ctor_get(v_elimEqs_2859_, 2);
v___x_2861_ = lean_box(0);
v___x_2862_ = lean_nat_dec_lt(v_v_2836_, v_size_2860_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; 
lean_dec_ref(v_elimEqs_2859_);
v___x_2863_ = l_outOfBounds___redArg(v___x_2861_);
v___y_2844_ = v___x_2863_;
goto v___jp_2843_;
}
else
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2861_, v_elimEqs_2859_, v_v_2836_);
lean_dec_ref(v_elimEqs_2859_);
v___y_2844_ = v___x_2864_;
goto v___jp_2843_;
}
v___jp_2843_:
{
if (lean_obj_tag(v___y_2844_) == 1)
{
lean_object* v_val_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2857_; 
lean_dec_ref(v_p_2837_);
v_val_2845_ = lean_ctor_get(v___y_2844_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___y_2844_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2847_ = v___y_2844_;
v_isShared_2848_ = v_isSharedCheck_2857_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_val_2845_);
lean_dec(v___y_2844_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2857_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2852_; 
v___x_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2849_, 0, v_v_2836_);
lean_ctor_set(v___x_2849_, 1, v_val_2845_);
v___x_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2850_, 0, v_k_2835_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v___x_2850_);
v___x_2852_ = v___x_2847_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2850_);
v___x_2852_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
lean_object* v___x_2854_; 
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2852_);
v___x_2854_ = v___x_2841_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2852_);
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
else
{
lean_dec(v___y_2844_);
lean_del_object(v___x_2841_);
lean_dec(v_v_2836_);
lean_dec(v_k_2835_);
v_p_2822_ = v_p_2837_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec_ref(v_p_2837_);
lean_dec(v_v_2836_);
lean_dec(v_k_2835_);
v_a_2866_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2838_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2838_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg___boxed(lean_object* v_p_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_2874_, v_a_2875_, v_a_2876_);
lean_dec_ref(v_a_2876_);
lean_dec(v_a_2875_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst(lean_object* v_p_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_2879_, v_a_2880_, v_a_2888_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___boxed(lean_object* v_p_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Int_Internal_Linear_Poly_findVarToSubst(v_p_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_a_2894_);
lean_dec(v_a_2893_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(lean_object* v_pred_2905_){
_start:
{
lean_object* v_c_u2081_2906_; lean_object* v_c_u2082_2907_; uint8_t v_left_2908_; lean_object* v_c_u2083_x3f_2909_; lean_object* v_p_2910_; lean_object* v_p_2911_; lean_object* v_a_2912_; lean_object* v_b_2913_; 
v_c_u2081_2906_ = lean_ctor_get(v_pred_2905_, 0);
v_c_u2082_2907_ = lean_ctor_get(v_pred_2905_, 1);
v_left_2908_ = lean_ctor_get_uint8(v_pred_2905_, sizeof(void*)*3);
v_c_u2083_x3f_2909_ = lean_ctor_get(v_pred_2905_, 2);
v_p_2910_ = lean_ctor_get(v_c_u2081_2906_, 0);
v_p_2911_ = lean_ctor_get(v_c_u2082_2907_, 0);
v_a_2912_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_2910_);
v_b_2913_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_2911_);
if (lean_obj_tag(v_c_u2083_x3f_2909_) == 0)
{
if (v_left_2908_ == 0)
{
lean_object* v___x_2914_; 
lean_dec(v_a_2912_);
v___x_2914_ = lean_nat_abs(v_b_2913_);
lean_dec(v_b_2913_);
return v___x_2914_;
}
else
{
lean_object* v___x_2915_; 
lean_dec(v_b_2913_);
v___x_2915_ = lean_nat_abs(v_a_2912_);
lean_dec(v_a_2912_);
return v___x_2915_;
}
}
else
{
lean_object* v_val_2916_; lean_object* v_d_2917_; lean_object* v_p_2918_; lean_object* v_c_2919_; 
v_val_2916_ = lean_ctor_get(v_c_u2083_x3f_2909_, 0);
v_d_2917_ = lean_ctor_get(v_val_2916_, 0);
v_p_2918_ = lean_ctor_get(v_val_2916_, 1);
v_c_2919_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_2918_);
if (v_left_2908_ == 0)
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
lean_dec(v_a_2912_);
v___x_2920_ = lean_int_mul(v_b_2913_, v_d_2917_);
v___x_2921_ = l_Int_gcd(v___x_2920_, v_c_2919_);
lean_dec(v_c_2919_);
v___x_2922_ = lean_nat_to_int(v___x_2921_);
v___x_2923_ = lean_int_ediv(v___x_2920_, v___x_2922_);
lean_dec(v___x_2922_);
lean_dec(v___x_2920_);
v___x_2924_ = l_Int_lcm(v_b_2913_, v___x_2923_);
lean_dec(v___x_2923_);
lean_dec(v_b_2913_);
return v___x_2924_;
}
else
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
lean_dec(v_b_2913_);
v___x_2925_ = lean_int_mul(v_a_2912_, v_d_2917_);
v___x_2926_ = l_Int_gcd(v___x_2925_, v_c_2919_);
lean_dec(v_c_2919_);
v___x_2927_ = lean_nat_to_int(v___x_2926_);
v___x_2928_ = lean_int_ediv(v___x_2925_, v___x_2927_);
lean_dec(v___x_2927_);
lean_dec(v___x_2925_);
v___x_2929_ = l_Int_lcm(v_a_2912_, v___x_2928_);
lean_dec(v___x_2928_);
lean_dec(v_a_2912_);
return v___x_2929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases___boxed(lean_object* v_pred_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(v_pred_2930_);
lean_dec_ref(v_pred_2930_);
return v_res_2931_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0));
v___x_2934_ = l_Lean_stringToMessageData(v___x_2933_);
return v___x_2934_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4(void){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3));
v___x_2939_ = l_Lean_MessageData_ofFormat(v___x_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(lean_object* v_pred_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v_c_u2081_2944_; lean_object* v_c_u2082_2945_; lean_object* v_c_u2083_x3f_2946_; lean_object* v___x_2947_; 
v_c_u2081_2944_ = lean_ctor_get(v_pred_2940_, 0);
lean_inc_ref(v_c_u2081_2944_);
v_c_u2082_2945_ = lean_ctor_get(v_pred_2940_, 1);
lean_inc_ref(v_c_u2082_2945_);
v_c_u2083_x3f_2946_ = lean_ctor_get(v_pred_2940_, 2);
lean_inc(v_c_u2083_x3f_2946_);
lean_dec_ref(v_pred_2940_);
v___x_2947_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_2944_, v_a_2941_, v_a_2942_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2949_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref_known(v___x_2947_, 1);
v___x_2949_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_2945_, v_a_2941_, v_a_2942_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2968_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2952_ = v___x_2949_;
v_isShared_2953_ = v_isSharedCheck_2968_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2949_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2968_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v_____do__lift_2955_; 
if (lean_obj_tag(v_c_u2083_x3f_2946_) == 1)
{
lean_object* v_val_2964_; lean_object* v___x_2965_; 
v_val_2964_ = lean_ctor_get(v_c_u2083_x3f_2946_, 0);
lean_inc(v_val_2964_);
lean_dec_ref_known(v_c_u2083_x3f_2946_, 1);
v___x_2965_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_val_2964_, v_a_2941_, v_a_2942_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v___x_2965_, 1);
v_____do__lift_2955_ = v_a_2966_;
goto v___jp_2954_;
}
else
{
lean_del_object(v___x_2952_);
lean_dec(v_a_2950_);
lean_dec(v_a_2948_);
return v___x_2965_;
}
}
else
{
lean_object* v___x_2967_; 
lean_dec(v_c_u2083_x3f_2946_);
v___x_2967_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4);
v_____do__lift_2955_ = v___x_2967_;
goto v___jp_2954_;
}
v___jp_2954_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2962_; 
v___x_2956_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_2957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2957_, 0, v_a_2948_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v___x_2958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
lean_ctor_set(v___x_2958_, 1, v_a_2950_);
v___x_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
lean_ctor_set(v___x_2959_, 1, v___x_2956_);
v___x_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
lean_ctor_set(v___x_2960_, 1, v_____do__lift_2955_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 0, v___x_2960_);
v___x_2962_ = v___x_2952_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2960_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
else
{
lean_dec(v_a_2948_);
lean_dec(v_c_u2083_x3f_2946_);
return v___x_2949_;
}
}
else
{
lean_dec(v_c_u2083_x3f_2946_);
lean_dec_ref(v_c_u2082_2945_);
return v___x_2947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___boxed(lean_object* v_pred_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_2969_, v_a_2970_, v_a_2971_);
lean_dec_ref(v_a_2971_);
lean_dec(v_a_2970_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(lean_object* v_pred_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_2974_, v_a_2975_, v_a_2983_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___boxed(lean_object* v_pred_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(v_pred_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
lean_dec(v_a_2989_);
lean_dec(v_a_2988_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(lean_object* v_h_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_){
_start:
{
switch(lean_obj_tag(v_h_3000_))
{
case 0:
{
lean_object* v_c_3004_; lean_object* v___x_3005_; 
v_c_3004_ = lean_ctor_get(v_h_3000_, 0);
lean_inc_ref(v_c_3004_);
lean_dec_ref_known(v_h_3000_, 1);
v___x_3005_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_3004_, v_a_3001_, v_a_3002_);
return v___x_3005_;
}
case 1:
{
lean_object* v_c_3006_; lean_object* v___x_3007_; 
v_c_3006_ = lean_ctor_get(v_h_3000_, 0);
lean_inc_ref(v_c_3006_);
lean_dec_ref_known(v_h_3000_, 1);
v___x_3007_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3006_, v_a_3001_, v_a_3002_);
return v___x_3007_;
}
case 2:
{
lean_object* v_c_3008_; lean_object* v___x_3009_; 
v_c_3008_ = lean_ctor_get(v_h_3000_, 0);
lean_inc_ref(v_c_3008_);
lean_dec_ref_known(v_h_3000_, 1);
v___x_3009_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_3008_, v_a_3001_, v_a_3002_);
return v___x_3009_;
}
case 3:
{
lean_object* v_c_3010_; lean_object* v___x_3011_; 
v_c_3010_ = lean_ctor_get(v_h_3000_, 0);
lean_inc_ref(v_c_3010_);
lean_dec_ref_known(v_h_3000_, 1);
v___x_3011_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_3010_, v_a_3001_, v_a_3002_);
return v___x_3011_;
}
default: 
{
lean_object* v_c_u2081_3012_; lean_object* v_c_u2082_3013_; lean_object* v_c_u2083_3014_; lean_object* v___x_3015_; 
v_c_u2081_3012_ = lean_ctor_get(v_h_3000_, 0);
lean_inc_ref(v_c_u2081_3012_);
v_c_u2082_3013_ = lean_ctor_get(v_h_3000_, 1);
lean_inc_ref(v_c_u2082_3013_);
v_c_u2083_3014_ = lean_ctor_get(v_h_3000_, 2);
lean_inc_ref(v_c_u2083_3014_);
lean_dec_ref_known(v_h_3000_, 3);
v___x_3015_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3012_, v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3017_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v___x_3017_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3013_, v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3019_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3019_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2083_3014_, v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3032_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3022_ = v___x_3019_;
v_isShared_3023_ = v_isSharedCheck_3032_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3032_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3024_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3025_, 0, v_a_3016_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
lean_ctor_set(v___x_3026_, 1, v_a_3018_);
v___x_3027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
lean_ctor_set(v___x_3027_, 1, v___x_3024_);
v___x_3028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
lean_ctor_set(v___x_3028_, 1, v_a_3020_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v___x_3028_);
v___x_3030_ = v___x_3022_;
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
lean_dec(v_a_3018_);
lean_dec(v_a_3016_);
return v___x_3019_;
}
}
else
{
lean_dec(v_a_3016_);
lean_dec_ref(v_c_u2083_3014_);
return v___x_3017_;
}
}
else
{
lean_dec_ref(v_c_u2083_3014_);
lean_dec_ref(v_c_u2082_3013_);
return v___x_3015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg___boxed(lean_object* v_h_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3033_, v_a_3034_, v_a_3035_);
lean_dec_ref(v_a_3035_);
lean_dec(v_a_3034_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(lean_object* v_h_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3038_, v_a_3039_, v_a_3047_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___boxed(lean_object* v_h_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(v_h_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec_ref(v_a_3058_);
lean_dec(v_a_3057_);
lean_dec_ref(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_a_3053_);
lean_dec(v_a_3052_);
return v_res_3063_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
