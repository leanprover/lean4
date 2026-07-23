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
v_conflict_x3f_120_ = lean_ctor_get(v_a_116_, 16);
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
lean_object* v_vars_578_; lean_object* v_varMap_579_; lean_object* v_vars_x27_580_; lean_object* v_varMap_x27_581_; lean_object* v_natToIntMap_582_; lean_object* v_natDef_583_; lean_object* v_dvds_584_; lean_object* v_lowers_585_; lean_object* v_uppers_586_; lean_object* v_diseqs_587_; lean_object* v_elimEqs_588_; lean_object* v_elimStack_589_; lean_object* v_occurs_590_; lean_object* v_assignment_591_; lean_object* v_nextCnstrId_592_; uint8_t v_caseSplits_593_; lean_object* v_steps_594_; lean_object* v_conflict_x3f_595_; lean_object* v_diseqSplits_596_; lean_object* v_divMod_597_; lean_object* v_toIntIds_598_; lean_object* v_toIntInfos_599_; lean_object* v_toIntTermMap_600_; lean_object* v_toIntVarMap_601_; uint8_t v_usedCommRing_602_; lean_object* v_nonlinearOccs_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_611_; 
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
v_caseSplits_593_ = lean_ctor_get_uint8(v_s_577_, sizeof(void*)*24);
v_steps_594_ = lean_ctor_get(v_s_577_, 15);
v_conflict_x3f_595_ = lean_ctor_get(v_s_577_, 16);
v_diseqSplits_596_ = lean_ctor_get(v_s_577_, 17);
v_divMod_597_ = lean_ctor_get(v_s_577_, 18);
v_toIntIds_598_ = lean_ctor_get(v_s_577_, 19);
v_toIntInfos_599_ = lean_ctor_get(v_s_577_, 20);
v_toIntTermMap_600_ = lean_ctor_get(v_s_577_, 21);
v_toIntVarMap_601_ = lean_ctor_get(v_s_577_, 22);
v_usedCommRing_602_ = lean_ctor_get_uint8(v_s_577_, sizeof(void*)*24 + 1);
v_nonlinearOccs_603_ = lean_ctor_get(v_s_577_, 23);
v_isSharedCheck_611_ = !lean_is_exclusive(v_s_577_);
if (v_isSharedCheck_611_ == 0)
{
v___x_605_ = v_s_577_;
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_nonlinearOccs_603_);
lean_inc(v_toIntVarMap_601_);
lean_inc(v_toIntTermMap_600_);
lean_inc(v_toIntInfos_599_);
lean_inc(v_toIntIds_598_);
lean_inc(v_divMod_597_);
lean_inc(v_diseqSplits_596_);
lean_inc(v_conflict_x3f_595_);
lean_inc(v_steps_594_);
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
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_607_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_591_, v_x_576_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 13, v___x_607_);
v___x_609_ = v___x_605_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 24, 2);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_vars_578_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_varMap_579_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v_vars_x27_580_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v_varMap_x27_581_);
lean_ctor_set(v_reuseFailAlloc_610_, 4, v_natToIntMap_582_);
lean_ctor_set(v_reuseFailAlloc_610_, 5, v_natDef_583_);
lean_ctor_set(v_reuseFailAlloc_610_, 6, v_dvds_584_);
lean_ctor_set(v_reuseFailAlloc_610_, 7, v_lowers_585_);
lean_ctor_set(v_reuseFailAlloc_610_, 8, v_uppers_586_);
lean_ctor_set(v_reuseFailAlloc_610_, 9, v_diseqs_587_);
lean_ctor_set(v_reuseFailAlloc_610_, 10, v_elimEqs_588_);
lean_ctor_set(v_reuseFailAlloc_610_, 11, v_elimStack_589_);
lean_ctor_set(v_reuseFailAlloc_610_, 12, v_occurs_590_);
lean_ctor_set(v_reuseFailAlloc_610_, 13, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_610_, 14, v_nextCnstrId_592_);
lean_ctor_set(v_reuseFailAlloc_610_, 15, v_steps_594_);
lean_ctor_set(v_reuseFailAlloc_610_, 16, v_conflict_x3f_595_);
lean_ctor_set(v_reuseFailAlloc_610_, 17, v_diseqSplits_596_);
lean_ctor_set(v_reuseFailAlloc_610_, 18, v_divMod_597_);
lean_ctor_set(v_reuseFailAlloc_610_, 19, v_toIntIds_598_);
lean_ctor_set(v_reuseFailAlloc_610_, 20, v_toIntInfos_599_);
lean_ctor_set(v_reuseFailAlloc_610_, 21, v_toIntTermMap_600_);
lean_ctor_set(v_reuseFailAlloc_610_, 22, v_toIntVarMap_601_);
lean_ctor_set(v_reuseFailAlloc_610_, 23, v_nonlinearOccs_603_);
lean_ctor_set_uint8(v_reuseFailAlloc_610_, sizeof(void*)*24, v_caseSplits_593_);
lean_ctor_set_uint8(v_reuseFailAlloc_610_, sizeof(void*)*24 + 1, v_usedCommRing_602_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_x_612_, lean_object* v_s_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(v_x_612_, v_s_613_);
lean_dec(v_x_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object* v_x_615_, lean_object* v_a_616_){
_start:
{
lean_object* v___f_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___f_618_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_618_, 0, v_x_615_);
v___x_619_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_620_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_619_, v___f_618_, v_a_616_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___boxed(lean_object* v_x_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_621_, v_a_622_);
lean_dec(v_a_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(lean_object* v_x_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_625_, v_a_626_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___boxed(lean_object* v_x_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(v_x_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
lean_dec(v_a_640_);
lean_dec(v_a_639_);
return v_res_650_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__0));
v___x_653_ = l_Lean_stringToMessageData(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_unsigned_to_nat(1u);
v___x_655_ = lean_nat_to_int(v___x_654_);
return v___x_655_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__3));
v___x_658_ = l_Lean_stringToMessageData(v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(lean_object* v_r_659_, lean_object* v_p_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
if (lean_obj_tag(v_p_660_) == 0)
{
lean_object* v_k_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_682_; 
v_k_664_ = lean_ctor_get(v_p_660_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v_p_660_);
if (v_isSharedCheck_682_ == 0)
{
v___x_666_ = v_p_660_;
v_isShared_667_ = v_isSharedCheck_682_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_k_664_);
lean_dec(v_p_660_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_682_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_669_ = lean_int_dec_eq(v_k_664_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_670_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v_r_659_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = l_Int_repr(v_k_664_);
lean_dec(v_k_664_);
if (v_isShared_667_ == 0)
{
lean_ctor_set_tag(v___x_666_, 3);
lean_ctor_set(v___x_666_, 0, v___x_672_);
v___x_674_ = v___x_666_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_672_);
v___x_674_ = v_reuseFailAlloc_678_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = l_Lean_MessageData_ofFormat(v___x_674_);
v___x_676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_671_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
else
{
lean_object* v___x_680_; 
lean_dec(v_k_664_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v_r_659_);
v___x_680_ = v___x_666_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_r_659_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_object* v_k_683_; lean_object* v_v_684_; lean_object* v_p_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v_k_683_ = lean_ctor_get(v_p_660_, 0);
lean_inc(v_k_683_);
v_v_684_ = lean_ctor_get(v_p_660_, 1);
lean_inc(v_v_684_);
v_p_685_ = lean_ctor_get(v_p_660_, 2);
lean_inc_ref(v_p_685_);
lean_dec_ref_known(v_p_660_, 3);
v___x_686_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_687_ = lean_int_dec_eq(v_k_683_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_684_, v_a_661_, v_a_662_);
lean_dec(v_v_684_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v___x_688_, 1);
v___x_690_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_691_, 0, v_r_659_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = l_Int_repr(v_k_683_);
lean_dec(v_k_683_);
v___x_693_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
v___x_694_ = l_Lean_MessageData_ofFormat(v___x_693_);
v___x_695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_691_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4);
v___x_697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_689_);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v_r_659_ = v___x_699_;
v_p_660_ = v_p_685_;
goto _start;
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec_ref(v_p_685_);
lean_dec(v_k_683_);
lean_dec_ref(v_r_659_);
v_a_701_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_688_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_688_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v___x_709_; 
lean_dec(v_k_683_);
v___x_709_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_684_, v_a_661_, v_a_662_);
lean_dec(v_v_684_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v_r_659_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_710_);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v_r_659_ = v___x_714_;
v_p_660_ = v_p_685_;
goto _start;
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec_ref(v_p_685_);
lean_dec_ref(v_r_659_);
v_a_716_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_709_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_709_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___boxed(lean_object* v_r_724_, lean_object* v_p_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v_r_724_, v_p_725_, v_a_726_, v_a_727_);
lean_dec_ref(v_a_727_);
lean_dec(v_a_726_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(lean_object* v_r_730_, lean_object* v_p_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v_r_730_, v_p_731_, v_a_732_, v_a_740_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___boxed(lean_object* v_r_744_, lean_object* v_p_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(v_r_744_, v_p_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec(v_a_746_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___redArg(lean_object* v_p_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
if (lean_obj_tag(v_p_758_) == 0)
{
lean_object* v_k_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_772_; 
v_k_762_ = lean_ctor_get(v_p_758_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v_p_758_);
if (v_isSharedCheck_772_ == 0)
{
v___x_764_ = v_p_758_;
v_isShared_765_ = v_isSharedCheck_772_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_k_762_);
lean_dec(v_p_758_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_772_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = l_Int_repr(v_k_762_);
lean_dec(v_k_762_);
if (v_isShared_765_ == 0)
{
lean_ctor_set_tag(v___x_764_, 3);
lean_ctor_set(v___x_764_, 0, v___x_766_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_771_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = l_Lean_MessageData_ofFormat(v___x_768_);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
}
}
else
{
lean_object* v_k_773_; lean_object* v_v_774_; lean_object* v_p_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_k_773_ = lean_ctor_get(v_p_758_, 0);
lean_inc(v_k_773_);
v_v_774_ = lean_ctor_get(v_p_758_, 1);
lean_inc(v_v_774_);
v_p_775_ = lean_ctor_get(v_p_758_, 2);
lean_inc_ref(v_p_775_);
lean_dec_ref_known(v_p_758_, 3);
v___x_776_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_777_ = lean_int_dec_eq(v_k_773_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_774_, v_a_759_, v_a_760_);
lean_dec(v_v_774_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref_known(v___x_778_, 1);
v___x_780_ = l_Int_repr(v_k_773_);
lean_dec(v_k_773_);
v___x_781_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
v___x_782_ = l_Lean_MessageData_ofFormat(v___x_781_);
v___x_783_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4);
v___x_784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_779_);
v___x_786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v___x_786_, v_p_775_, v_a_759_, v_a_760_);
return v___x_787_;
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec_ref(v_p_775_);
lean_dec(v_k_773_);
v_a_788_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_778_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_778_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v___x_796_; 
lean_dec(v_k_773_);
v___x_796_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_774_, v_a_759_, v_a_760_);
lean_dec(v_v_774_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref_known(v___x_796_, 1);
v___x_798_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_797_);
v___x_799_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v___x_798_, v_p_775_, v_a_759_, v_a_760_);
return v___x_799_;
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec_ref(v_p_775_);
v_a_800_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_796_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_796_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
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
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___redArg___boxed(lean_object* v_p_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_808_, v_a_809_, v_a_810_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp(lean_object* v_p_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_813_, v_a_814_, v_a_822_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___boxed(lean_object* v_p_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Int_Internal_Linear_Poly_pp(v_p_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec(v_a_827_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0(lean_object* v_a_839_, lean_object* v___x_840_, lean_object* v_x_841_){
_start:
{
lean_object* v_size_842_; uint8_t v___x_843_; 
v_size_842_ = lean_ctor_get(v_a_839_, 2);
v___x_843_ = lean_nat_dec_lt(v_x_841_, v_size_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
v___x_844_ = l_outOfBounds___redArg(v___x_840_);
return v___x_844_;
}
else
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_PersistentArray_get_x21___redArg(v___x_840_, v_a_839_, v_x_841_);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed(lean_object* v_a_846_, lean_object* v___x_847_, lean_object* v_x_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0(v_a_846_, v___x_847_, v_x_848_);
lean_dec(v_x_848_);
lean_dec_ref(v___x_847_);
lean_dec_ref(v_a_846_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(lean_object* v_p_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_851_, v_a_852_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; lean_object* v___f_857_; lean_object* v___x_858_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v___x_856_ = l_Lean_instInhabitedExpr;
v___f_857_ = lean_alloc_closure((void*)(l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_857_, 0, v_a_855_);
lean_closure_set(v___f_857_, 1, v___x_856_);
v___x_858_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_857_, v_p_850_);
return v___x_858_;
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_dec_ref(v_p_850_);
v_a_859_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_854_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_854_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___boxed(lean_object* v_p_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_867_, v_a_868_, v_a_869_);
lean_dec_ref(v_a_869_);
lean_dec(v_a_868_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27(lean_object* v_p_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_872_, v_a_873_, v_a_881_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___boxed(lean_object* v_p_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Int_Internal_Linear_Poly_denoteExpr_x27(v_p_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec(v_a_886_);
return v_res_897_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object* v_c_898_){
_start:
{
lean_object* v_p_899_; 
v_p_899_ = lean_ctor_get(v_c_898_, 1);
if (lean_obj_tag(v_p_899_) == 0)
{
lean_object* v_d_900_; lean_object* v_k_901_; lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v_d_900_ = lean_ctor_get(v_c_898_, 0);
v_k_901_ = lean_ctor_get(v_p_899_, 0);
v___x_902_ = lean_int_emod(v_k_901_, v_d_900_);
v___x_903_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_904_ = lean_int_dec_eq(v___x_902_, v___x_903_);
lean_dec(v___x_902_);
return v___x_904_;
}
else
{
lean_object* v_d_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v_d_905_ = lean_ctor_get(v_c_898_, 0);
v___x_906_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
v___x_907_ = lean_int_dec_eq(v_d_905_, v___x_906_);
return v___x_907_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial___boxed(lean_object* v_c_908_){
_start:
{
uint8_t v_res_909_; lean_object* v_r_910_; 
v_res_909_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_c_908_);
lean_dec_ref(v_c_908_);
v_r_910_ = lean_box(v_res_909_);
return v_r_910_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0));
v___x_913_ = l_Lean_stringToMessageData(v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object* v_c_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_d_918_; lean_object* v_p_919_; lean_object* v___x_920_; 
v_d_918_ = lean_ctor_get(v_c_914_, 0);
lean_inc(v_d_918_);
v_p_919_ = lean_ctor_get(v_c_914_, 1);
lean_inc_ref(v_p_919_);
lean_dec_ref(v_c_914_);
v___x_920_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_919_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_934_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_934_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_934_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_934_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_925_ = l_Int_repr(v_d_918_);
lean_dec(v_d_918_);
v___x_926_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
v___x_927_ = l_Lean_MessageData_ofFormat(v___x_926_);
v___x_928_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v_a_921_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_930_);
v___x_932_ = v___x_923_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
else
{
lean_dec(v_d_918_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___boxed(lean_object* v_c_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_935_, v_a_936_, v_a_937_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(lean_object* v_c_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_940_, v_a_941_, v_a_949_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___boxed(lean_object* v_c_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(v_c_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec(v_a_954_);
return v_res_965_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_unsigned_to_nat(0u);
v___x_972_ = l_Lean_Level_ofNat(v___x_971_);
return v___x_972_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = lean_box(0);
v___x_974_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3);
v___x_975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v___x_973_);
return v___x_975_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_976_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4);
v___x_977_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2));
v___x_978_ = l_Lean_Expr_const___override(v___x_977_, v___x_976_);
return v___x_978_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = lean_box(0);
v___x_983_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7));
v___x_984_ = l_Lean_Expr_const___override(v___x_983_, v___x_982_);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_989_ = lean_box(0);
v___x_990_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10));
v___x_991_ = l_Lean_Expr_const___override(v___x_990_, v___x_989_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(lean_object* v_c_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v_d_996_; lean_object* v_p_997_; lean_object* v___x_998_; 
v_d_996_ = lean_ctor_get(v_c_992_, 0);
lean_inc(v_d_996_);
v_p_997_ = lean_ctor_get(v_c_992_, 1);
lean_inc_ref(v_p_997_);
lean_dec_ref(v_c_992_);
v___x_998_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_997_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1020_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1020_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1020_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___y_1004_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1009_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1010_ = lean_int_dec_le(v___x_1009_, v_d_996_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1011_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5);
v___x_1012_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8);
v___x_1013_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11);
v___x_1014_ = lean_int_neg(v_d_996_);
lean_dec(v_d_996_);
v___x_1015_ = l_Int_toNat(v___x_1014_);
lean_dec(v___x_1014_);
v___x_1016_ = l_Lean_instToExprInt_mkNat(v___x_1015_);
v___x_1017_ = l_Lean_mkApp3(v___x_1011_, v___x_1012_, v___x_1013_, v___x_1016_);
v___y_1004_ = v___x_1017_;
goto v___jp_1003_;
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = l_Int_toNat(v_d_996_);
lean_dec(v_d_996_);
v___x_1019_ = l_Lean_instToExprInt_mkNat(v___x_1018_);
v___y_1004_ = v___x_1019_;
goto v___jp_1003_;
}
v___jp_1003_:
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1005_ = l_Lean_mkIntDvd(v___y_1004_, v_a_999_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1005_);
v___x_1007_ = v___x_1001_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
else
{
lean_dec(v_d_996_);
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1021_, v_a_1022_, v_a_1023_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(lean_object* v_c_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1026_, v_a_1027_, v_a_1035_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___boxed(lean_object* v_c_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(v_c_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_a_1041_);
lean_dec(v_a_1040_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(lean_object* v_msgData_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v___x_1058_; lean_object* v_env_1059_; lean_object* v___x_1060_; lean_object* v_mctx_1061_; lean_object* v_lctx_1062_; lean_object* v_options_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1058_ = lean_st_ref_get(v___y_1056_);
v_env_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc_ref(v_env_1059_);
lean_dec(v___x_1058_);
v___x_1060_ = lean_st_ref_get(v___y_1054_);
v_mctx_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc_ref(v_mctx_1061_);
lean_dec(v___x_1060_);
v_lctx_1062_ = lean_ctor_get(v___y_1053_, 2);
v_options_1063_ = lean_ctor_get(v___y_1055_, 2);
lean_inc_ref(v_options_1063_);
lean_inc_ref(v_lctx_1062_);
v___x_1064_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1064_, 0, v_env_1059_);
lean_ctor_set(v___x_1064_, 1, v_mctx_1061_);
lean_ctor_set(v___x_1064_, 2, v_lctx_1062_);
lean_ctor_set(v___x_1064_, 3, v_options_1063_);
v___x_1065_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v_msgData_1052_);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object* v_msgData_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msgData_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(lean_object* v_msg_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_ref_1080_; lean_object* v___x_1081_; lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1090_; 
v_ref_1080_ = lean_ctor_get(v___y_1077_, 5);
v___x_1081_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msg_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
lean_inc(v_ref_1080_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_ref_1080_);
lean_ctor_set(v___x_1086_, 1, v_a_1082_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set_tag(v___x_1084_, 1);
lean_ctor_set(v___x_1084_, 0, v___x_1086_);
v___x_1088_ = v___x_1084_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg___boxed(lean_object* v_msg_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1097_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0));
v___x_1100_ = l_Lean_stringToMessageData(v___x_1099_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2));
v___x_1103_ = l_Lean_stringToMessageData(v___x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object* v_c_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1104_, v_a_1105_, v_a_1113_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___x_1118_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1119_ = l_Lean_indentD(v_a_1117_);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1122_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
return v___x_1123_;
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
v_a_1124_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1116_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1116_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec(v_a_1133_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(lean_object* v_00_u03b1_1145_, lean_object* v_c_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1159_, lean_object* v_c_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(v_00_u03b1_1159_, v_c_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
lean_dec(v_a_1161_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(lean_object* v_00_u03b1_1173_, lean_object* v_msg_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1174_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___boxed(lean_object* v_00_u03b1_1187_, lean_object* v_msg_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(v_00_u03b1_1187_, v_msg_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec(v___y_1189_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial_spec__0(lean_object* v_a_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_nat_to_int(v_a_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(lean_object* v_c_1203_){
_start:
{
lean_object* v_p_1204_; 
v_p_1204_ = lean_ctor_get(v_c_1203_, 0);
if (lean_obj_tag(v_p_1204_) == 0)
{
lean_object* v_k_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v_k_1205_ = lean_ctor_get(v_p_1204_, 0);
v___x_1206_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1207_ = lean_int_dec_eq(v_k_1205_, v___x_1206_);
if (v___x_1207_ == 0)
{
uint8_t v___x_1208_; 
v___x_1208_ = 1;
return v___x_1208_;
}
else
{
uint8_t v___x_1209_; 
v___x_1209_ = 0;
return v___x_1209_;
}
}
else
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1210_ = l_Int_Internal_Linear_Poly_getConst(v_p_1204_);
v___x_1211_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v_p_1204_);
v___x_1212_ = lean_nat_to_int(v___x_1211_);
v___x_1213_ = lean_int_emod(v___x_1210_, v___x_1212_);
lean_dec(v___x_1212_);
lean_dec(v___x_1210_);
v___x_1214_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1215_ = lean_int_dec_eq(v___x_1213_, v___x_1214_);
lean_dec(v___x_1213_);
if (v___x_1215_ == 0)
{
uint8_t v___x_1216_; 
v___x_1216_ = 1;
return v___x_1216_;
}
else
{
uint8_t v___x_1217_; 
v___x_1217_ = 0;
return v___x_1217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial___boxed(lean_object* v_c_1218_){
_start:
{
uint8_t v_res_1219_; lean_object* v_r_1220_; 
v_res_1219_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(v_c_1218_);
lean_dec_ref(v_c_1218_);
v_r_1220_ = lean_box(v_res_1219_);
return v_r_1220_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0));
v___x_1223_ = l_Lean_stringToMessageData(v___x_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(lean_object* v_c_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_p_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1245_; 
v_p_1228_ = lean_ctor_get(v_c_1224_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_c_1224_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v_c_1224_, 1);
lean_dec(v_unused_1246_);
v___x_1230_ = v_c_1224_;
v_isShared_1231_ = v_isSharedCheck_1245_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_p_1228_);
lean_dec(v_c_1224_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1245_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1228_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1244_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1235_ = v___x_1232_;
v_isShared_1236_ = v_isSharedCheck_1244_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1232_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1244_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1237_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1);
if (v_isShared_1231_ == 0)
{
lean_ctor_set_tag(v___x_1230_, 7);
lean_ctor_set(v___x_1230_, 1, v___x_1237_);
lean_ctor_set(v___x_1230_, 0, v_a_1233_);
v___x_1239_ = v___x_1230_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1233_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1241_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1239_);
v___x_1241_ = v___x_1235_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
else
{
lean_del_object(v___x_1230_);
return v___x_1232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___boxed(lean_object* v_c_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1247_, v_a_1248_, v_a_1249_);
lean_dec_ref(v_a_1249_);
lean_dec(v_a_1248_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(lean_object* v_c_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1252_, v_a_1253_, v_a_1261_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___boxed(lean_object* v_c_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(v_c_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec(v_a_1266_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(lean_object* v_c_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1278_, v_a_1279_, v_a_1282_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v___x_1287_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1288_ = l_Lean_indentD(v_a_1286_);
v___x_1289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1287_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
v___x_1290_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1289_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_);
return v___x_1290_;
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_a_1291_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1285_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1285_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(lean_object* v_00_u03b1_1307_, lean_object* v_c_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1308_, v_a_1309_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1321_, lean_object* v_c_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(v_00_u03b1_1321_, v_c_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
lean_dec(v_a_1332_);
lean_dec_ref(v_a_1331_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec(v_a_1324_);
lean_dec(v_a_1323_);
return v_res_1334_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1336_ = l_Lean_mkIntLit(v___x_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(lean_object* v_c_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_p_1341_; lean_object* v___x_1342_; 
v_p_1341_ = lean_ctor_get(v_c_1337_, 0);
lean_inc_ref(v_p_1341_);
lean_dec_ref(v_c_1337_);
v___x_1342_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1341_, v_a_1338_, v_a_1339_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1353_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1353_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1353_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1347_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1348_ = l_Lean_mkIntEq(v_a_1343_, v___x_1347_);
v___x_1349_ = l_Lean_mkNot(v___x_1348_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1349_);
v___x_1351_ = v___x_1345_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
else
{
return v___x_1342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1354_, v_a_1355_, v_a_1356_);
lean_dec_ref(v_a_1356_);
lean_dec(v_a_1355_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(lean_object* v_c_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1359_, v_a_1360_, v_a_1368_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___boxed(lean_object* v_c_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(v_c_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
lean_dec(v_a_1374_);
lean_dec(v_a_1373_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert___boxed(lean_object* v_c_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_00___x40___internal___hyg_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = lean_grind_cutsat_assert_le(v_c_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
return v_res_1409_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(lean_object* v_c_1410_){
_start:
{
lean_object* v_p_1411_; 
v_p_1411_ = lean_ctor_get(v_c_1410_, 0);
if (lean_obj_tag(v_p_1411_) == 0)
{
lean_object* v_k_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v_k_1412_ = lean_ctor_get(v_p_1411_, 0);
v___x_1413_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1414_ = lean_int_dec_le(v_k_1412_, v___x_1413_);
return v___x_1414_;
}
else
{
uint8_t v___x_1415_; 
v___x_1415_ = 0;
return v___x_1415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial___boxed(lean_object* v_c_1416_){
_start:
{
uint8_t v_res_1417_; lean_object* v_r_1418_; 
v_res_1417_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_c_1416_);
lean_dec_ref(v_c_1416_);
v_r_1418_ = lean_box(v_res_1417_);
return v_r_1418_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0));
v___x_1421_ = l_Lean_stringToMessageData(v___x_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(lean_object* v_c_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_p_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1443_; 
v_p_1426_ = lean_ctor_get(v_c_1422_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_c_1422_);
if (v_isSharedCheck_1443_ == 0)
{
lean_object* v_unused_1444_; 
v_unused_1444_ = lean_ctor_get(v_c_1422_, 1);
lean_dec(v_unused_1444_);
v___x_1428_ = v_c_1422_;
v_isShared_1429_ = v_isSharedCheck_1443_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_p_1426_);
lean_dec(v_c_1422_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1443_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1426_, v_a_1423_, v_a_1424_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1442_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1442_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1442_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1435_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1);
if (v_isShared_1429_ == 0)
{
lean_ctor_set_tag(v___x_1428_, 7);
lean_ctor_set(v___x_1428_, 1, v___x_1435_);
lean_ctor_set(v___x_1428_, 0, v_a_1431_);
v___x_1437_ = v___x_1428_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1431_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
lean_object* v___x_1439_; 
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v___x_1437_);
v___x_1439_ = v___x_1433_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
else
{
lean_del_object(v___x_1428_);
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___boxed(lean_object* v_c_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1445_, v_a_1446_, v_a_1447_);
lean_dec_ref(v_a_1447_);
lean_dec(v_a_1446_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(lean_object* v_c_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1450_, v_a_1451_, v_a_1459_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___boxed(lean_object* v_c_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(v_c_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec(v_a_1464_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(lean_object* v_c_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v_p_1480_; lean_object* v___x_1481_; 
v_p_1480_ = lean_ctor_get(v_c_1476_, 0);
lean_inc_ref(v_p_1480_);
lean_dec_ref(v_c_1476_);
v___x_1481_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1480_, v_a_1477_, v_a_1478_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1491_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1491_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1491_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1486_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1487_ = l_Lean_mkIntLE(v_a_1482_, v___x_1486_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v___x_1487_);
v___x_1489_ = v___x_1484_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
else
{
return v___x_1481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1492_, v_a_1493_, v_a_1494_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(lean_object* v_c_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1497_, v_a_1498_, v_a_1506_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___boxed(lean_object* v_c_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(v_c_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
lean_dec(v_a_1514_);
lean_dec_ref(v_a_1513_);
lean_dec(v_a_1512_);
lean_dec(v_a_1511_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(lean_object* v_c_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1523_, v_a_1524_, v_a_1527_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v___x_1532_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1533_ = l_Lean_indentD(v_a_1531_);
v___x_1534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1532_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1534_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
return v___x_1535_;
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
v_a_1536_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1530_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1530_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
lean_dec(v_a_1549_);
lean_dec_ref(v_a_1548_);
lean_dec(v_a_1547_);
lean_dec_ref(v_a_1546_);
lean_dec(v_a_1545_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(lean_object* v_00_u03b1_1552_, lean_object* v_c_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1553_, v_a_1554_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1566_, lean_object* v_c_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(v_00_u03b1_1566_, v_c_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
lean_dec(v_a_1573_);
lean_dec_ref(v_a_1572_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
lean_dec(v_a_1569_);
lean_dec(v_a_1568_);
return v_res_1579_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(lean_object* v_c_1580_){
_start:
{
lean_object* v_p_1581_; 
v_p_1581_ = lean_ctor_get(v_c_1580_, 0);
if (lean_obj_tag(v_p_1581_) == 0)
{
lean_object* v_k_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v_k_1582_ = lean_ctor_get(v_p_1581_, 0);
v___x_1583_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1584_ = lean_int_dec_eq(v_k_1582_, v___x_1583_);
return v___x_1584_;
}
else
{
uint8_t v___x_1585_; 
v___x_1585_ = 0;
return v___x_1585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial___boxed(lean_object* v_c_1586_){
_start:
{
uint8_t v_res_1587_; lean_object* v_r_1588_; 
v_res_1587_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(v_c_1586_);
lean_dec_ref(v_c_1586_);
v_r_1588_ = lean_box(v_res_1587_);
return v_r_1588_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0));
v___x_1591_ = l_Lean_stringToMessageData(v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object* v_c_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v_p_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1613_; 
v_p_1596_ = lean_ctor_get(v_c_1592_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_c_1592_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v_c_1592_, 1);
lean_dec(v_unused_1614_);
v___x_1598_ = v_c_1592_;
v_isShared_1599_ = v_isSharedCheck_1613_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_p_1596_);
lean_dec(v_c_1592_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1613_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1596_, v_a_1593_, v_a_1594_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1612_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1612_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1612_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1605_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1);
if (v_isShared_1599_ == 0)
{
lean_ctor_set_tag(v___x_1598_, 7);
lean_ctor_set(v___x_1598_, 1, v___x_1605_);
lean_ctor_set(v___x_1598_, 0, v_a_1601_);
v___x_1607_ = v___x_1598_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1601_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1609_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___x_1607_);
v___x_1609_ = v___x_1603_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
else
{
lean_del_object(v___x_1598_);
return v___x_1600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___boxed(lean_object* v_c_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1615_, v_a_1616_, v_a_1617_);
lean_dec_ref(v_a_1617_);
lean_dec(v_a_1616_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(lean_object* v_c_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1620_, v_a_1621_, v_a_1629_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___boxed(lean_object* v_c_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(v_c_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
lean_dec(v_a_1641_);
lean_dec_ref(v_a_1640_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
lean_dec(v_a_1635_);
lean_dec(v_a_1634_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(lean_object* v_c_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v_p_1650_; lean_object* v___x_1651_; 
v_p_1650_ = lean_ctor_get(v_c_1646_, 0);
lean_inc_ref(v_p_1650_);
lean_dec_ref(v_c_1646_);
v___x_1651_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1650_, v_a_1647_, v_a_1648_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1661_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1661_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1661_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1656_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1657_ = l_Lean_mkIntEq(v_a_1652_, v___x_1656_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1657_);
v___x_1659_ = v___x_1654_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
else
{
return v___x_1651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1662_, v_a_1663_, v_a_1664_);
lean_dec_ref(v_a_1664_);
lean_dec(v_a_1663_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(lean_object* v_c_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1667_, v_a_1668_, v_a_1676_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___boxed(lean_object* v_c_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(v_c_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec(v_a_1681_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(lean_object* v_c_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1693_, v_a_1694_, v_a_1697_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v___x_1700_, 1);
v___x_1702_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1703_ = l_Lean_indentD(v_a_1701_);
v___x_1704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1702_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
v___x_1705_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1704_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
return v___x_1705_;
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
v_a_1706_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1700_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1700_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(lean_object* v_00_u03b1_1722_, lean_object* v_c_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_1723_, v_a_1724_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1736_, lean_object* v_c_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(v_00_u03b1_1736_, v_c_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec(v_a_1743_);
lean_dec_ref(v_a_1742_);
lean_dec(v_a_1741_);
lean_dec_ref(v_a_1740_);
lean_dec(v_a_1739_);
lean_dec(v_a_1738_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(lean_object* v_x_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1751_, v_a_1752_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1771_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1771_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1771_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v_occurs_1759_; lean_object* v_size_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v_occurs_1759_ = lean_ctor_get(v_a_1755_, 12);
lean_inc_ref(v_occurs_1759_);
lean_dec(v_a_1755_);
v_size_1760_ = lean_ctor_get(v_occurs_1759_, 2);
v___x_1761_ = lean_box(1);
v___x_1762_ = lean_nat_dec_lt(v_x_1750_, v_size_1760_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
lean_dec_ref(v_occurs_1759_);
v___x_1763_ = l_outOfBounds___redArg(v___x_1761_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v___x_1763_);
v___x_1765_ = v___x_1757_;
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
else
{
lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1767_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1761_, v_occurs_1759_, v_x_1750_);
lean_dec_ref(v_occurs_1759_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v___x_1767_);
v___x_1769_ = v___x_1757_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
v_a_1772_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1754_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1754_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg___boxed(lean_object* v_x_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_1780_, v_a_1781_, v_a_1782_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec(v_x_1780_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(lean_object* v_x_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_1785_, v_a_1786_, v_a_1794_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___boxed(lean_object* v_x_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(v_x_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
lean_dec(v_a_1806_);
lean_dec_ref(v_a_1805_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
lean_dec(v_a_1802_);
lean_dec_ref(v_a_1801_);
lean_dec(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec(v_x_1798_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(lean_object* v_k_1811_, lean_object* v_v_1812_, lean_object* v_t_1813_){
_start:
{
if (lean_obj_tag(v_t_1813_) == 0)
{
lean_object* v_size_1814_; lean_object* v_k_1815_; lean_object* v_v_1816_; lean_object* v_l_1817_; lean_object* v_r_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_2099_; 
v_size_1814_ = lean_ctor_get(v_t_1813_, 0);
v_k_1815_ = lean_ctor_get(v_t_1813_, 1);
v_v_1816_ = lean_ctor_get(v_t_1813_, 2);
v_l_1817_ = lean_ctor_get(v_t_1813_, 3);
v_r_1818_ = lean_ctor_get(v_t_1813_, 4);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_t_1813_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_1820_ = v_t_1813_;
v_isShared_1821_ = v_isSharedCheck_2099_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_r_1818_);
lean_inc(v_l_1817_);
lean_inc(v_v_1816_);
lean_inc(v_k_1815_);
lean_inc(v_size_1814_);
lean_dec(v_t_1813_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_2099_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
uint8_t v___x_1822_; 
v___x_1822_ = lean_nat_dec_lt(v_k_1811_, v_k_1815_);
if (v___x_1822_ == 0)
{
uint8_t v___x_1823_; 
v___x_1823_ = lean_nat_dec_eq(v_k_1811_, v_k_1815_);
if (v___x_1823_ == 0)
{
lean_object* v_impl_1824_; lean_object* v___x_1825_; 
lean_dec(v_size_1814_);
v_impl_1824_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_1811_, v_v_1812_, v_r_1818_);
v___x_1825_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1817_) == 0)
{
lean_object* v_size_1826_; lean_object* v_size_1827_; lean_object* v_k_1828_; lean_object* v_v_1829_; lean_object* v_l_1830_; lean_object* v_r_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v_size_1826_ = lean_ctor_get(v_l_1817_, 0);
v_size_1827_ = lean_ctor_get(v_impl_1824_, 0);
lean_inc(v_size_1827_);
v_k_1828_ = lean_ctor_get(v_impl_1824_, 1);
lean_inc(v_k_1828_);
v_v_1829_ = lean_ctor_get(v_impl_1824_, 2);
lean_inc(v_v_1829_);
v_l_1830_ = lean_ctor_get(v_impl_1824_, 3);
lean_inc(v_l_1830_);
v_r_1831_ = lean_ctor_get(v_impl_1824_, 4);
lean_inc(v_r_1831_);
v___x_1832_ = lean_unsigned_to_nat(3u);
v___x_1833_ = lean_nat_mul(v___x_1832_, v_size_1826_);
v___x_1834_ = lean_nat_dec_lt(v___x_1833_, v_size_1827_);
lean_dec(v___x_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
lean_dec(v_r_1831_);
lean_dec(v_l_1830_);
lean_dec(v_v_1829_);
lean_dec(v_k_1828_);
v___x_1835_ = lean_nat_add(v___x_1825_, v_size_1826_);
v___x_1836_ = lean_nat_add(v___x_1835_, v_size_1827_);
lean_dec(v_size_1827_);
lean_dec(v___x_1835_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 4, v_impl_1824_);
lean_ctor_set(v___x_1820_, 0, v___x_1836_);
v___x_1838_ = v___x_1820_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_k_1815_);
lean_ctor_set(v_reuseFailAlloc_1839_, 2, v_v_1816_);
lean_ctor_set(v_reuseFailAlloc_1839_, 3, v_l_1817_);
lean_ctor_set(v_reuseFailAlloc_1839_, 4, v_impl_1824_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
else
{
lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1903_; 
v_isSharedCheck_1903_ = !lean_is_exclusive(v_impl_1824_);
if (v_isSharedCheck_1903_ == 0)
{
lean_object* v_unused_1904_; lean_object* v_unused_1905_; lean_object* v_unused_1906_; lean_object* v_unused_1907_; lean_object* v_unused_1908_; 
v_unused_1904_ = lean_ctor_get(v_impl_1824_, 4);
lean_dec(v_unused_1904_);
v_unused_1905_ = lean_ctor_get(v_impl_1824_, 3);
lean_dec(v_unused_1905_);
v_unused_1906_ = lean_ctor_get(v_impl_1824_, 2);
lean_dec(v_unused_1906_);
v_unused_1907_ = lean_ctor_get(v_impl_1824_, 1);
lean_dec(v_unused_1907_);
v_unused_1908_ = lean_ctor_get(v_impl_1824_, 0);
lean_dec(v_unused_1908_);
v___x_1841_ = v_impl_1824_;
v_isShared_1842_ = v_isSharedCheck_1903_;
goto v_resetjp_1840_;
}
else
{
lean_dec(v_impl_1824_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1903_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v_size_1843_; lean_object* v_k_1844_; lean_object* v_v_1845_; lean_object* v_l_1846_; lean_object* v_r_1847_; lean_object* v_size_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v_size_1843_ = lean_ctor_get(v_l_1830_, 0);
v_k_1844_ = lean_ctor_get(v_l_1830_, 1);
v_v_1845_ = lean_ctor_get(v_l_1830_, 2);
v_l_1846_ = lean_ctor_get(v_l_1830_, 3);
v_r_1847_ = lean_ctor_get(v_l_1830_, 4);
v_size_1848_ = lean_ctor_get(v_r_1831_, 0);
v___x_1849_ = lean_unsigned_to_nat(2u);
v___x_1850_ = lean_nat_mul(v___x_1849_, v_size_1848_);
v___x_1851_ = lean_nat_dec_lt(v_size_1843_, v___x_1850_);
lean_dec(v___x_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1879_; 
lean_inc(v_r_1847_);
lean_inc(v_l_1846_);
lean_inc(v_v_1845_);
lean_inc(v_k_1844_);
v_isSharedCheck_1879_ = !lean_is_exclusive(v_l_1830_);
if (v_isSharedCheck_1879_ == 0)
{
lean_object* v_unused_1880_; lean_object* v_unused_1881_; lean_object* v_unused_1882_; lean_object* v_unused_1883_; lean_object* v_unused_1884_; 
v_unused_1880_ = lean_ctor_get(v_l_1830_, 4);
lean_dec(v_unused_1880_);
v_unused_1881_ = lean_ctor_get(v_l_1830_, 3);
lean_dec(v_unused_1881_);
v_unused_1882_ = lean_ctor_get(v_l_1830_, 2);
lean_dec(v_unused_1882_);
v_unused_1883_ = lean_ctor_get(v_l_1830_, 1);
lean_dec(v_unused_1883_);
v_unused_1884_ = lean_ctor_get(v_l_1830_, 0);
lean_dec(v_unused_1884_);
v___x_1853_ = v_l_1830_;
v_isShared_1854_ = v_isSharedCheck_1879_;
goto v_resetjp_1852_;
}
else
{
lean_dec(v_l_1830_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1879_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1869_; 
v___x_1855_ = lean_nat_add(v___x_1825_, v_size_1826_);
v___x_1856_ = lean_nat_add(v___x_1855_, v_size_1827_);
lean_dec(v_size_1827_);
if (lean_obj_tag(v_l_1846_) == 0)
{
lean_object* v_size_1877_; 
v_size_1877_ = lean_ctor_get(v_l_1846_, 0);
lean_inc(v_size_1877_);
v___y_1869_ = v_size_1877_;
goto v___jp_1868_;
}
else
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_unsigned_to_nat(0u);
v___y_1869_ = v___x_1878_;
goto v___jp_1868_;
}
v___jp_1857_:
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1861_ = lean_nat_add(v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec(v___y_1859_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 4, v_r_1831_);
lean_ctor_set(v___x_1853_, 3, v_r_1847_);
lean_ctor_set(v___x_1853_, 2, v_v_1829_);
lean_ctor_set(v___x_1853_, 1, v_k_1828_);
lean_ctor_set(v___x_1853_, 0, v___x_1861_);
v___x_1863_ = v___x_1853_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_k_1828_);
lean_ctor_set(v_reuseFailAlloc_1867_, 2, v_v_1829_);
lean_ctor_set(v_reuseFailAlloc_1867_, 3, v_r_1847_);
lean_ctor_set(v_reuseFailAlloc_1867_, 4, v_r_1831_);
v___x_1863_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1865_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 4, v___x_1863_);
lean_ctor_set(v___x_1841_, 3, v___y_1858_);
lean_ctor_set(v___x_1841_, 2, v_v_1845_);
lean_ctor_set(v___x_1841_, 1, v_k_1844_);
lean_ctor_set(v___x_1841_, 0, v___x_1856_);
v___x_1865_ = v___x_1841_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1856_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_k_1844_);
lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_v_1845_);
lean_ctor_set(v_reuseFailAlloc_1866_, 3, v___y_1858_);
lean_ctor_set(v_reuseFailAlloc_1866_, 4, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
v___jp_1868_:
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1870_ = lean_nat_add(v___x_1855_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec(v___x_1855_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 4, v_l_1846_);
lean_ctor_set(v___x_1820_, 0, v___x_1870_);
v___x_1872_ = v___x_1820_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1870_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_k_1815_);
lean_ctor_set(v_reuseFailAlloc_1876_, 2, v_v_1816_);
lean_ctor_set(v_reuseFailAlloc_1876_, 3, v_l_1817_);
lean_ctor_set(v_reuseFailAlloc_1876_, 4, v_l_1846_);
v___x_1872_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_nat_add(v___x_1825_, v_size_1848_);
if (lean_obj_tag(v_r_1847_) == 0)
{
lean_object* v_size_1874_; 
v_size_1874_ = lean_ctor_get(v_r_1847_, 0);
lean_inc(v_size_1874_);
v___y_1858_ = v___x_1872_;
v___y_1859_ = v___x_1873_;
v___y_1860_ = v_size_1874_;
goto v___jp_1857_;
}
else
{
lean_object* v___x_1875_; 
v___x_1875_ = lean_unsigned_to_nat(0u);
v___y_1858_ = v___x_1872_;
v___y_1859_ = v___x_1873_;
v___y_1860_ = v___x_1875_;
goto v___jp_1857_;
}
}
}
}
}
else
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1889_; 
lean_del_object(v___x_1820_);
v___x_1885_ = lean_nat_add(v___x_1825_, v_size_1826_);
v___x_1886_ = lean_nat_add(v___x_1885_, v_size_1827_);
lean_dec(v_size_1827_);
v___x_1887_ = lean_nat_add(v___x_1885_, v_size_1843_);
lean_dec(v___x_1885_);
lean_inc_ref(v_l_1817_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 4, v_l_1830_);
lean_ctor_set(v___x_1841_, 3, v_l_1817_);
lean_ctor_set(v___x_1841_, 2, v_v_1816_);
lean_ctor_set(v___x_1841_, 1, v_k_1815_);
lean_ctor_set(v___x_1841_, 0, v___x_1887_);
v___x_1889_ = v___x_1841_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_k_1815_);
lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_v_1816_);
lean_ctor_set(v_reuseFailAlloc_1902_, 3, v_l_1817_);
lean_ctor_set(v_reuseFailAlloc_1902_, 4, v_l_1830_);
v___x_1889_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
v_isSharedCheck_1896_ = !lean_is_exclusive(v_l_1817_);
if (v_isSharedCheck_1896_ == 0)
{
lean_object* v_unused_1897_; lean_object* v_unused_1898_; lean_object* v_unused_1899_; lean_object* v_unused_1900_; lean_object* v_unused_1901_; 
v_unused_1897_ = lean_ctor_get(v_l_1817_, 4);
lean_dec(v_unused_1897_);
v_unused_1898_ = lean_ctor_get(v_l_1817_, 3);
lean_dec(v_unused_1898_);
v_unused_1899_ = lean_ctor_get(v_l_1817_, 2);
lean_dec(v_unused_1899_);
v_unused_1900_ = lean_ctor_get(v_l_1817_, 1);
lean_dec(v_unused_1900_);
v_unused_1901_ = lean_ctor_get(v_l_1817_, 0);
lean_dec(v_unused_1901_);
v___x_1891_ = v_l_1817_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_dec(v_l_1817_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 4, v_r_1831_);
lean_ctor_set(v___x_1891_, 3, v___x_1889_);
lean_ctor_set(v___x_1891_, 2, v_v_1829_);
lean_ctor_set(v___x_1891_, 1, v_k_1828_);
lean_ctor_set(v___x_1891_, 0, v___x_1886_);
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_k_1828_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_v_1829_);
lean_ctor_set(v_reuseFailAlloc_1895_, 3, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1895_, 4, v_r_1831_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1909_; 
v_l_1909_ = lean_ctor_get(v_impl_1824_, 3);
lean_inc(v_l_1909_);
if (lean_obj_tag(v_l_1909_) == 0)
{
lean_object* v_r_1910_; lean_object* v_k_1911_; lean_object* v_v_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1935_; 
v_r_1910_ = lean_ctor_get(v_impl_1824_, 4);
v_k_1911_ = lean_ctor_get(v_impl_1824_, 1);
v_v_1912_ = lean_ctor_get(v_impl_1824_, 2);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_impl_1824_);
if (v_isSharedCheck_1935_ == 0)
{
lean_object* v_unused_1936_; lean_object* v_unused_1937_; 
v_unused_1936_ = lean_ctor_get(v_impl_1824_, 3);
lean_dec(v_unused_1936_);
v_unused_1937_ = lean_ctor_get(v_impl_1824_, 0);
lean_dec(v_unused_1937_);
v___x_1914_ = v_impl_1824_;
v_isShared_1915_ = v_isSharedCheck_1935_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_r_1910_);
lean_inc(v_v_1912_);
lean_inc(v_k_1911_);
lean_dec(v_impl_1824_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1935_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v_k_1916_; lean_object* v_v_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1931_; 
v_k_1916_ = lean_ctor_get(v_l_1909_, 1);
v_v_1917_ = lean_ctor_get(v_l_1909_, 2);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_l_1909_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; lean_object* v_unused_1933_; lean_object* v_unused_1934_; 
v_unused_1932_ = lean_ctor_get(v_l_1909_, 4);
lean_dec(v_unused_1932_);
v_unused_1933_ = lean_ctor_get(v_l_1909_, 3);
lean_dec(v_unused_1933_);
v_unused_1934_ = lean_ctor_get(v_l_1909_, 0);
lean_dec(v_unused_1934_);
v___x_1919_ = v_l_1909_;
v_isShared_1920_ = v_isSharedCheck_1931_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_v_1917_);
lean_inc(v_k_1916_);
lean_dec(v_l_1909_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1931_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1921_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1910_, 2);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 4, v_r_1910_);
lean_ctor_set(v___x_1919_, 3, v_r_1910_);
lean_ctor_set(v___x_1919_, 2, v_v_1816_);
lean_ctor_set(v___x_1919_, 1, v_k_1815_);
lean_ctor_set(v___x_1919_, 0, v___x_1825_);
v___x_1923_ = v___x_1919_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_k_1815_);
lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_v_1816_);
lean_ctor_set(v_reuseFailAlloc_1930_, 3, v_r_1910_);
lean_ctor_set(v_reuseFailAlloc_1930_, 4, v_r_1910_);
v___x_1923_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1925_; 
lean_inc(v_r_1910_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 3, v_r_1910_);
lean_ctor_set(v___x_1914_, 0, v___x_1825_);
v___x_1925_ = v___x_1914_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_k_1911_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v_v_1912_);
lean_ctor_set(v_reuseFailAlloc_1929_, 3, v_r_1910_);
lean_ctor_set(v_reuseFailAlloc_1929_, 4, v_r_1910_);
v___x_1925_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___x_1927_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 4, v___x_1925_);
lean_ctor_set(v___x_1820_, 3, v___x_1923_);
lean_ctor_set(v___x_1820_, 2, v_v_1917_);
lean_ctor_set(v___x_1820_, 1, v_k_1916_);
lean_ctor_set(v___x_1820_, 0, v___x_1921_);
v___x_1927_ = v___x_1820_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_k_1916_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v_v_1917_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1928_, 4, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
}
else
{
lean_object* v_r_1938_; 
v_r_1938_ = lean_ctor_get(v_impl_1824_, 4);
lean_inc(v_r_1938_);
if (lean_obj_tag(v_r_1938_) == 0)
{
lean_object* v_k_1939_; lean_object* v_v_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1951_; 
v_k_1939_ = lean_ctor_get(v_impl_1824_, 1);
v_v_1940_ = lean_ctor_get(v_impl_1824_, 2);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_impl_1824_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; lean_object* v_unused_1953_; lean_object* v_unused_1954_; 
v_unused_1952_ = lean_ctor_get(v_impl_1824_, 4);
lean_dec(v_unused_1952_);
v_unused_1953_ = lean_ctor_get(v_impl_1824_, 3);
lean_dec(v_unused_1953_);
v_unused_1954_ = lean_ctor_get(v_impl_1824_, 0);
lean_dec(v_unused_1954_);
v___x_1942_ = v_impl_1824_;
v_isShared_1943_ = v_isSharedCheck_1951_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_v_1940_);
lean_inc(v_k_1939_);
lean_dec(v_impl_1824_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1951_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1944_; lean_object* v___x_1946_; 
v___x_1944_ = lean_unsigned_to_nat(3u);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 4, v_l_1909_);
lean_ctor_set(v___x_1942_, 2, v_v_1816_);
lean_ctor_set(v___x_1942_, 1, v_k_1815_);
lean_ctor_set(v___x_1942_, 0, v___x_1825_);
v___x_1946_ = v___x_1942_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1825_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_k_1815_);
lean_ctor_set(v_reuseFailAlloc_1950_, 2, v_v_1816_);
lean_ctor_set(v_reuseFailAlloc_1950_, 3, v_l_1909_);
lean_ctor_set(v_reuseFailAlloc_1950_, 4, v_l_1909_);
v___x_1946_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
lean_object* v___x_1948_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 4, v_r_1938_);
lean_ctor_set(v___x_1820_, 3, v___x_1946_);
lean_ctor_set(v___x_1820_, 2, v_v_1940_);
lean_ctor_set(v___x_1820_, 1, v_k_1939_);
lean_ctor_set(v___x_1820_, 0, v___x_1944_);
v___x_1948_ = v___x_1820_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_1949_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_1949_, 3, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_1949_, 4, v_r_1938_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1955_ = lean_unsigned_to_nat(2u);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 4, v_impl_1824_);
lean_ctor_set(v___x_1820_, 3, v_r_1938_);
lean_ctor_set(v___x_1820_, 0, v___x_1955_);
v___x_1957_ = v___x_1820_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_k_1815_);
lean_ctor_set(v_reuseFailAlloc_1958_, 2, v_v_1816_);
lean_ctor_set(v_reuseFailAlloc_1958_, 3, v_r_1938_);
lean_ctor_set(v_reuseFailAlloc_1958_, 4, v_impl_1824_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
else
{
lean_object* v___x_1960_; 
lean_dec(v_v_1816_);
lean_dec(v_k_1815_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 2, v_v_1812_);
lean_ctor_set(v___x_1820_, 1, v_k_1811_);
v___x_1960_ = v___x_1820_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_size_1814_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_k_1811_);
lean_ctor_set(v_reuseFailAlloc_1961_, 2, v_v_1812_);
lean_ctor_set(v_reuseFailAlloc_1961_, 3, v_l_1817_);
lean_ctor_set(v_reuseFailAlloc_1961_, 4, v_r_1818_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
else
{
lean_object* v_impl_1962_; lean_object* v___x_1963_; 
lean_dec(v_size_1814_);
v_impl_1962_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_1811_, v_v_1812_, v_l_1817_);
v___x_1963_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1818_) == 0)
{
lean_object* v_size_1964_; lean_object* v_size_1965_; lean_object* v_k_1966_; lean_object* v_v_1967_; lean_object* v_l_1968_; lean_object* v_r_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v_size_1964_ = lean_ctor_get(v_r_1818_, 0);
v_size_1965_ = lean_ctor_get(v_impl_1962_, 0);
lean_inc(v_size_1965_);
v_k_1966_ = lean_ctor_get(v_impl_1962_, 1);
lean_inc(v_k_1966_);
v_v_1967_ = lean_ctor_get(v_impl_1962_, 2);
lean_inc(v_v_1967_);
v_l_1968_ = lean_ctor_get(v_impl_1962_, 3);
lean_inc(v_l_1968_);
v_r_1969_ = lean_ctor_get(v_impl_1962_, 4);
lean_inc(v_r_1969_);
v___x_1970_ = lean_unsigned_to_nat(3u);
v___x_1971_ = lean_nat_mul(v___x_1970_, v_size_1964_);
v___x_1972_ = lean_nat_dec_lt(v___x_1971_, v_size_1965_);
lean_dec(v___x_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1976_; 
lean_dec(v_r_1969_);
lean_dec(v_l_1968_);
lean_dec(v_v_1967_);
lean_dec(v_k_1966_);
v___x_1973_ = lean_nat_add(v___x_1963_, v_size_1965_);
lean_dec(v_size_1965_);
v___x_1974_ = lean_nat_add(v___x_1973_, v_size_1964_);
lean_dec(v___x_1973_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 3, v_impl_1962_);
lean_ctor_set(v___x_1820_, 0, v___x_1974_);
v___x_1976_ = v___x_1820_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_k_1815_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v_v_1816_);
lean_ctor_set(v_reuseFailAlloc_1977_, 3, v_impl_1962_);
lean_ctor_set(v_reuseFailAlloc_1977_, 4, v_r_1818_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
else
{
lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2043_; 
v_isSharedCheck_2043_ = !lean_is_exclusive(v_impl_1962_);
if (v_isSharedCheck_2043_ == 0)
{
lean_object* v_unused_2044_; lean_object* v_unused_2045_; lean_object* v_unused_2046_; lean_object* v_unused_2047_; lean_object* v_unused_2048_; 
v_unused_2044_ = lean_ctor_get(v_impl_1962_, 4);
lean_dec(v_unused_2044_);
v_unused_2045_ = lean_ctor_get(v_impl_1962_, 3);
lean_dec(v_unused_2045_);
v_unused_2046_ = lean_ctor_get(v_impl_1962_, 2);
lean_dec(v_unused_2046_);
v_unused_2047_ = lean_ctor_get(v_impl_1962_, 1);
lean_dec(v_unused_2047_);
v_unused_2048_ = lean_ctor_get(v_impl_1962_, 0);
lean_dec(v_unused_2048_);
v___x_1979_ = v_impl_1962_;
v_isShared_1980_ = v_isSharedCheck_2043_;
goto v_resetjp_1978_;
}
else
{
lean_dec(v_impl_1962_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2043_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v_size_1981_; lean_object* v_size_1982_; lean_object* v_k_1983_; lean_object* v_v_1984_; lean_object* v_l_1985_; lean_object* v_r_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v_size_1981_ = lean_ctor_get(v_l_1968_, 0);
v_size_1982_ = lean_ctor_get(v_r_1969_, 0);
v_k_1983_ = lean_ctor_get(v_r_1969_, 1);
v_v_1984_ = lean_ctor_get(v_r_1969_, 2);
v_l_1985_ = lean_ctor_get(v_r_1969_, 3);
v_r_1986_ = lean_ctor_get(v_r_1969_, 4);
v___x_1987_ = lean_unsigned_to_nat(2u);
v___x_1988_ = lean_nat_mul(v___x_1987_, v_size_1981_);
v___x_1989_ = lean_nat_dec_lt(v_size_1982_, v___x_1988_);
lean_dec(v___x_1988_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2018_; 
lean_inc(v_r_1986_);
lean_inc(v_l_1985_);
lean_inc(v_v_1984_);
lean_inc(v_k_1983_);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_r_1969_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; lean_object* v_unused_2020_; lean_object* v_unused_2021_; lean_object* v_unused_2022_; lean_object* v_unused_2023_; 
v_unused_2019_ = lean_ctor_get(v_r_1969_, 4);
lean_dec(v_unused_2019_);
v_unused_2020_ = lean_ctor_get(v_r_1969_, 3);
lean_dec(v_unused_2020_);
v_unused_2021_ = lean_ctor_get(v_r_1969_, 2);
lean_dec(v_unused_2021_);
v_unused_2022_ = lean_ctor_get(v_r_1969_, 1);
lean_dec(v_unused_2022_);
v_unused_2023_ = lean_ctor_get(v_r_1969_, 0);
lean_dec(v_unused_2023_);
v___x_1991_ = v_r_1969_;
v_isShared_1992_ = v_isSharedCheck_2018_;
goto v_resetjp_1990_;
}
else
{
lean_dec(v_r_1969_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2018_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___x_2006_; lean_object* v___y_2008_; 
v___x_1993_ = lean_nat_add(v___x_1963_, v_size_1965_);
lean_dec(v_size_1965_);
v___x_1994_ = lean_nat_add(v___x_1993_, v_size_1964_);
lean_dec(v___x_1993_);
v___x_2006_ = lean_nat_add(v___x_1963_, v_size_1981_);
if (lean_obj_tag(v_l_1985_) == 0)
{
lean_object* v_size_2016_; 
v_size_2016_ = lean_ctor_get(v_l_1985_, 0);
lean_inc(v_size_2016_);
v___y_2008_ = v_size_2016_;
goto v___jp_2007_;
}
else
{
lean_object* v___x_2017_; 
v___x_2017_ = lean_unsigned_to_nat(0u);
v___y_2008_ = v___x_2017_;
goto v___jp_2007_;
}
v___jp_1995_:
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1999_ = lean_nat_add(v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec(v___y_1997_);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 4, v_r_1818_);
lean_ctor_set(v___x_1991_, 3, v_r_1986_);
lean_ctor_set(v___x_1991_, 2, v_v_1816_);
lean_ctor_set(v___x_1991_, 1, v_k_1815_);
lean_ctor_set(v___x_1991_, 0, v___x_1999_);
v___x_2001_ = v___x_1991_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_k_1815_);
lean_ctor_set(v_reuseFailAlloc_2005_, 2, v_v_1816_);
lean_ctor_set(v_reuseFailAlloc_2005_, 3, v_r_1986_);
lean_ctor_set(v_reuseFailAlloc_2005_, 4, v_r_1818_);
v___x_2001_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2003_; 
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 4, v___x_2001_);
lean_ctor_set(v___x_1979_, 3, v___y_1996_);
lean_ctor_set(v___x_1979_, 2, v_v_1984_);
lean_ctor_set(v___x_1979_, 1, v_k_1983_);
lean_ctor_set(v___x_1979_, 0, v___x_1994_);
v___x_2003_ = v___x_1979_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2004_, 3, v___y_1996_);
lean_ctor_set(v_reuseFailAlloc_2004_, 4, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
v___jp_2007_:
{
lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2009_ = lean_nat_add(v___x_2006_, v___y_2008_);
lean_dec(v___y_2008_);
lean_dec(v___x_2006_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 4, v_l_1985_);
lean_ctor_set(v___x_1820_, 3, v_l_1968_);
lean_ctor_set(v___x_1820_, 2, v_v_1967_);
lean_ctor_set(v___x_1820_, 1, v_k_1966_);
lean_ctor_set(v___x_1820_, 0, v___x_2009_);
v___x_2011_ = v___x_1820_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_2015_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_2015_, 3, v_l_1968_);
lean_ctor_set(v_reuseFailAlloc_2015_, 4, v_l_1985_);
v___x_2011_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; 
v___x_2012_ = lean_nat_add(v___x_1963_, v_size_1964_);
if (lean_obj_tag(v_r_1986_) == 0)
{
lean_object* v_size_2013_; 
v_size_2013_ = lean_ctor_get(v_r_1986_, 0);
lean_inc(v_size_2013_);
v___y_1996_ = v___x_2011_;
v___y_1997_ = v___x_2012_;
v___y_1998_ = v_size_2013_;
goto v___jp_1995_;
}
else
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_unsigned_to_nat(0u);
v___y_1996_ = v___x_2011_;
v___y_1997_ = v___x_2012_;
v___y_1998_ = v___x_2014_;
goto v___jp_1995_;
}
}
}
}
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2029_; 
lean_del_object(v___x_1820_);
v___x_2024_ = lean_nat_add(v___x_1963_, v_size_1965_);
lean_dec(v_size_1965_);
v___x_2025_ = lean_nat_add(v___x_2024_, v_size_1964_);
lean_dec(v___x_2024_);
v___x_2026_ = lean_nat_add(v___x_1963_, v_size_1964_);
v___x_2027_ = lean_nat_add(v___x_2026_, v_size_1982_);
lean_dec(v___x_2026_);
lean_inc_ref(v_r_1818_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 4, v_r_1818_);
lean_ctor_set(v___x_1979_, 3, v_r_1969_);
lean_ctor_set(v___x_1979_, 2, v_v_1816_);
lean_ctor_set(v___x_1979_, 1, v_k_1815_);
lean_ctor_set(v___x_1979_, 0, v___x_2027_);
v___x_2029_ = v___x_1979_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2027_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_k_1815_);
lean_ctor_set(v_reuseFailAlloc_2042_, 2, v_v_1816_);
lean_ctor_set(v_reuseFailAlloc_2042_, 3, v_r_1969_);
lean_ctor_set(v_reuseFailAlloc_2042_, 4, v_r_1818_);
v___x_2029_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
v_isSharedCheck_2036_ = !lean_is_exclusive(v_r_1818_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; lean_object* v_unused_2038_; lean_object* v_unused_2039_; lean_object* v_unused_2040_; lean_object* v_unused_2041_; 
v_unused_2037_ = lean_ctor_get(v_r_1818_, 4);
lean_dec(v_unused_2037_);
v_unused_2038_ = lean_ctor_get(v_r_1818_, 3);
lean_dec(v_unused_2038_);
v_unused_2039_ = lean_ctor_get(v_r_1818_, 2);
lean_dec(v_unused_2039_);
v_unused_2040_ = lean_ctor_get(v_r_1818_, 1);
lean_dec(v_unused_2040_);
v_unused_2041_ = lean_ctor_get(v_r_1818_, 0);
lean_dec(v_unused_2041_);
v___x_2031_ = v_r_1818_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_dec(v_r_1818_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 4, v___x_2029_);
lean_ctor_set(v___x_2031_, 3, v_l_1968_);
lean_ctor_set(v___x_2031_, 2, v_v_1967_);
lean_ctor_set(v___x_2031_, 1, v_k_1966_);
lean_ctor_set(v___x_2031_, 0, v___x_2025_);
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_2035_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_2035_, 3, v_l_1968_);
lean_ctor_set(v_reuseFailAlloc_2035_, 4, v___x_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2049_; 
v_l_2049_ = lean_ctor_get(v_impl_1962_, 3);
lean_inc(v_l_2049_);
if (lean_obj_tag(v_l_2049_) == 0)
{
lean_object* v_r_2050_; lean_object* v_k_2051_; lean_object* v_v_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2063_; 
v_r_2050_ = lean_ctor_get(v_impl_1962_, 4);
v_k_2051_ = lean_ctor_get(v_impl_1962_, 1);
v_v_2052_ = lean_ctor_get(v_impl_1962_, 2);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_impl_1962_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; lean_object* v_unused_2065_; 
v_unused_2064_ = lean_ctor_get(v_impl_1962_, 3);
lean_dec(v_unused_2064_);
v_unused_2065_ = lean_ctor_get(v_impl_1962_, 0);
lean_dec(v_unused_2065_);
v___x_2054_ = v_impl_1962_;
v_isShared_2055_ = v_isSharedCheck_2063_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_r_2050_);
lean_inc(v_v_2052_);
lean_inc(v_k_2051_);
lean_dec(v_impl_1962_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2063_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2056_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2050_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 3, v_r_2050_);
lean_ctor_set(v___x_2054_, 2, v_v_1816_);
lean_ctor_set(v___x_2054_, 1, v_k_1815_);
lean_ctor_set(v___x_2054_, 0, v___x_1963_);
v___x_2058_ = v___x_2054_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_k_1815_);
lean_ctor_set(v_reuseFailAlloc_2062_, 2, v_v_1816_);
lean_ctor_set(v_reuseFailAlloc_2062_, 3, v_r_2050_);
lean_ctor_set(v_reuseFailAlloc_2062_, 4, v_r_2050_);
v___x_2058_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2060_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 4, v___x_2058_);
lean_ctor_set(v___x_1820_, 3, v_l_2049_);
lean_ctor_set(v___x_1820_, 2, v_v_2052_);
lean_ctor_set(v___x_1820_, 1, v_k_2051_);
lean_ctor_set(v___x_1820_, 0, v___x_2056_);
v___x_2060_ = v___x_1820_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_k_2051_);
lean_ctor_set(v_reuseFailAlloc_2061_, 2, v_v_2052_);
lean_ctor_set(v_reuseFailAlloc_2061_, 3, v_l_2049_);
lean_ctor_set(v_reuseFailAlloc_2061_, 4, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
else
{
lean_object* v_r_2066_; 
v_r_2066_ = lean_ctor_get(v_impl_1962_, 4);
lean_inc(v_r_2066_);
if (lean_obj_tag(v_r_2066_) == 0)
{
lean_object* v_k_2067_; lean_object* v_v_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2091_; 
v_k_2067_ = lean_ctor_get(v_impl_1962_, 1);
v_v_2068_ = lean_ctor_get(v_impl_1962_, 2);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_impl_1962_);
if (v_isSharedCheck_2091_ == 0)
{
lean_object* v_unused_2092_; lean_object* v_unused_2093_; lean_object* v_unused_2094_; 
v_unused_2092_ = lean_ctor_get(v_impl_1962_, 4);
lean_dec(v_unused_2092_);
v_unused_2093_ = lean_ctor_get(v_impl_1962_, 3);
lean_dec(v_unused_2093_);
v_unused_2094_ = lean_ctor_get(v_impl_1962_, 0);
lean_dec(v_unused_2094_);
v___x_2070_ = v_impl_1962_;
v_isShared_2071_ = v_isSharedCheck_2091_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_v_2068_);
lean_inc(v_k_2067_);
lean_dec(v_impl_1962_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2091_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v_k_2072_; lean_object* v_v_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2087_; 
v_k_2072_ = lean_ctor_get(v_r_2066_, 1);
v_v_2073_ = lean_ctor_get(v_r_2066_, 2);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_r_2066_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; lean_object* v_unused_2089_; lean_object* v_unused_2090_; 
v_unused_2088_ = lean_ctor_get(v_r_2066_, 4);
lean_dec(v_unused_2088_);
v_unused_2089_ = lean_ctor_get(v_r_2066_, 3);
lean_dec(v_unused_2089_);
v_unused_2090_ = lean_ctor_get(v_r_2066_, 0);
lean_dec(v_unused_2090_);
v___x_2075_ = v_r_2066_;
v_isShared_2076_ = v_isSharedCheck_2087_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_v_2073_);
lean_inc(v_k_2072_);
lean_dec(v_r_2066_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2087_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2077_ = lean_unsigned_to_nat(3u);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 4, v_l_2049_);
lean_ctor_set(v___x_2075_, 3, v_l_2049_);
lean_ctor_set(v___x_2075_, 2, v_v_2068_);
lean_ctor_set(v___x_2075_, 1, v_k_2067_);
lean_ctor_set(v___x_2075_, 0, v___x_1963_);
v___x_2079_ = v___x_2075_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_k_2067_);
lean_ctor_set(v_reuseFailAlloc_2086_, 2, v_v_2068_);
lean_ctor_set(v_reuseFailAlloc_2086_, 3, v_l_2049_);
lean_ctor_set(v_reuseFailAlloc_2086_, 4, v_l_2049_);
v___x_2079_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2081_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 4, v_l_2049_);
lean_ctor_set(v___x_2070_, 2, v_v_1816_);
lean_ctor_set(v___x_2070_, 1, v_k_1815_);
lean_ctor_set(v___x_2070_, 0, v___x_1963_);
v___x_2081_ = v___x_2070_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_k_1815_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_v_1816_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_l_2049_);
lean_ctor_set(v_reuseFailAlloc_2085_, 4, v_l_2049_);
v___x_2081_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
lean_object* v___x_2083_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 4, v___x_2081_);
lean_ctor_set(v___x_1820_, 3, v___x_2079_);
lean_ctor_set(v___x_1820_, 2, v_v_2073_);
lean_ctor_set(v___x_1820_, 1, v_k_2072_);
lean_ctor_set(v___x_1820_, 0, v___x_2077_);
v___x_2083_ = v___x_1820_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_k_2072_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_v_2073_);
lean_ctor_set(v_reuseFailAlloc_2084_, 3, v___x_2079_);
lean_ctor_set(v_reuseFailAlloc_2084_, 4, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2095_ = lean_unsigned_to_nat(2u);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 4, v_r_2066_);
lean_ctor_set(v___x_1820_, 3, v_impl_1962_);
lean_ctor_set(v___x_1820_, 0, v___x_2095_);
v___x_2097_ = v___x_1820_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_k_1815_);
lean_ctor_set(v_reuseFailAlloc_2098_, 2, v_v_1816_);
lean_ctor_set(v_reuseFailAlloc_2098_, 3, v_impl_1962_);
lean_ctor_set(v_reuseFailAlloc_2098_, 4, v_r_2066_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = lean_unsigned_to_nat(1u);
v___x_2101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v_k_1811_);
lean_ctor_set(v___x_2101_, 2, v_v_1812_);
lean_ctor_set(v___x_2101_, 3, v_t_1813_);
lean_ctor_set(v___x_2101_, 4, v_t_1813_);
return v___x_2101_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(lean_object* v_k_2102_, lean_object* v_t_2103_){
_start:
{
if (lean_obj_tag(v_t_2103_) == 0)
{
lean_object* v_k_2104_; lean_object* v_l_2105_; lean_object* v_r_2106_; uint8_t v___x_2107_; 
v_k_2104_ = lean_ctor_get(v_t_2103_, 1);
v_l_2105_ = lean_ctor_get(v_t_2103_, 3);
v_r_2106_ = lean_ctor_get(v_t_2103_, 4);
v___x_2107_ = lean_nat_dec_lt(v_k_2102_, v_k_2104_);
if (v___x_2107_ == 0)
{
uint8_t v___x_2108_; 
v___x_2108_ = lean_nat_dec_eq(v_k_2102_, v_k_2104_);
if (v___x_2108_ == 0)
{
v_t_2103_ = v_r_2106_;
goto _start;
}
else
{
return v___x_2108_;
}
}
else
{
v_t_2103_ = v_l_2105_;
goto _start;
}
}
else
{
uint8_t v___x_2111_; 
v___x_2111_ = 0;
return v___x_2111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg___boxed(lean_object* v_k_2112_, lean_object* v_t_2113_){
_start:
{
uint8_t v_res_2114_; lean_object* v_r_2115_; 
v_res_2114_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2112_, v_t_2113_);
lean_dec(v_t_2113_);
lean_dec(v_k_2112_);
v_r_2115_ = lean_box(v_res_2114_);
return v_r_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(lean_object* v_y_2116_, lean_object* v_x_2117_, size_t v_x_2118_, size_t v_x_2119_){
_start:
{
if (lean_obj_tag(v_x_2117_) == 0)
{
lean_object* v_cs_2120_; size_t v_j_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v_cs_2120_ = lean_ctor_get(v_x_2117_, 0);
v_j_2121_ = lean_usize_shift_right(v_x_2118_, v_x_2119_);
v___x_2122_ = lean_usize_to_nat(v_j_2121_);
v___x_2123_ = lean_array_get_size(v_cs_2120_);
v___x_2124_ = lean_nat_dec_lt(v___x_2122_, v___x_2123_);
if (v___x_2124_ == 0)
{
lean_dec(v___x_2122_);
lean_dec(v_y_2116_);
return v_x_2117_;
}
else
{
lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2142_; 
lean_inc_ref(v_cs_2120_);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_x_2117_);
if (v_isSharedCheck_2142_ == 0)
{
lean_object* v_unused_2143_; 
v_unused_2143_ = lean_ctor_get(v_x_2117_, 0);
lean_dec(v_unused_2143_);
v___x_2126_ = v_x_2117_;
v_isShared_2127_ = v_isSharedCheck_2142_;
goto v_resetjp_2125_;
}
else
{
lean_dec(v_x_2117_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2142_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
size_t v___x_2128_; size_t v___x_2129_; size_t v___x_2130_; size_t v_i_2131_; size_t v___x_2132_; size_t v_shift_2133_; lean_object* v_v_2134_; lean_object* v___x_2135_; lean_object* v_xs_x27_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2128_ = ((size_t)1ULL);
v___x_2129_ = lean_usize_shift_left(v___x_2128_, v_x_2119_);
v___x_2130_ = lean_usize_sub(v___x_2129_, v___x_2128_);
v_i_2131_ = lean_usize_land(v_x_2118_, v___x_2130_);
v___x_2132_ = ((size_t)5ULL);
v_shift_2133_ = lean_usize_sub(v_x_2119_, v___x_2132_);
v_v_2134_ = lean_array_fget(v_cs_2120_, v___x_2122_);
v___x_2135_ = lean_box(0);
v_xs_x27_2136_ = lean_array_fset(v_cs_2120_, v___x_2122_, v___x_2135_);
v___x_2137_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2116_, v_v_2134_, v_i_2131_, v_shift_2133_);
v___x_2138_ = lean_array_fset(v_xs_x27_2136_, v___x_2122_, v___x_2137_);
lean_dec(v___x_2122_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2138_);
v___x_2140_ = v___x_2126_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
else
{
lean_object* v_vs_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v_vs_2144_ = lean_ctor_get(v_x_2117_, 0);
v___x_2145_ = lean_usize_to_nat(v_x_2118_);
v___x_2146_ = lean_array_get_size(v_vs_2144_);
v___x_2147_ = lean_nat_dec_lt(v___x_2145_, v___x_2146_);
if (v___x_2147_ == 0)
{
lean_dec(v___x_2145_);
lean_dec(v_y_2116_);
return v_x_2117_;
}
else
{
lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2162_; 
lean_inc_ref(v_vs_2144_);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_x_2117_);
if (v_isSharedCheck_2162_ == 0)
{
lean_object* v_unused_2163_; 
v_unused_2163_ = lean_ctor_get(v_x_2117_, 0);
lean_dec(v_unused_2163_);
v___x_2149_ = v_x_2117_;
v_isShared_2150_ = v_isSharedCheck_2162_;
goto v_resetjp_2148_;
}
else
{
lean_dec(v_x_2117_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2162_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v_v_2151_; lean_object* v___x_2152_; lean_object* v_xs_x27_2153_; lean_object* v___y_2155_; uint8_t v___x_2160_; 
v_v_2151_ = lean_array_fget(v_vs_2144_, v___x_2145_);
v___x_2152_ = lean_box(0);
v_xs_x27_2153_ = lean_array_fset(v_vs_2144_, v___x_2145_, v___x_2152_);
v___x_2160_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2116_, v_v_2151_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2116_, v___x_2152_, v_v_2151_);
v___y_2155_ = v___x_2161_;
goto v___jp_2154_;
}
else
{
lean_dec(v_y_2116_);
v___y_2155_ = v_v_2151_;
goto v___jp_2154_;
}
v___jp_2154_:
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2156_ = lean_array_fset(v_xs_x27_2153_, v___x_2145_, v___y_2155_);
lean_dec(v___x_2145_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v___x_2156_);
v___x_2158_ = v___x_2149_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2164_, lean_object* v_x_2165_, lean_object* v_x_2166_, lean_object* v_x_2167_){
_start:
{
size_t v_x_4560__boxed_2168_; size_t v_x_4561__boxed_2169_; lean_object* v_res_2170_; 
v_x_4560__boxed_2168_ = lean_unbox_usize(v_x_2166_);
lean_dec(v_x_2166_);
v_x_4561__boxed_2169_ = lean_unbox_usize(v_x_2167_);
lean_dec(v_x_2167_);
v_res_2170_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2164_, v_x_2165_, v_x_4560__boxed_2168_, v_x_4561__boxed_2169_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(lean_object* v_y_2171_, lean_object* v_t_2172_, lean_object* v_i_2173_){
_start:
{
lean_object* v_root_2174_; lean_object* v_tail_2175_; lean_object* v_size_2176_; size_t v_shift_2177_; lean_object* v_tailOff_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2205_; 
v_root_2174_ = lean_ctor_get(v_t_2172_, 0);
v_tail_2175_ = lean_ctor_get(v_t_2172_, 1);
v_size_2176_ = lean_ctor_get(v_t_2172_, 2);
v_shift_2177_ = lean_ctor_get_usize(v_t_2172_, 4);
v_tailOff_2178_ = lean_ctor_get(v_t_2172_, 3);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_t_2172_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2180_ = v_t_2172_;
v_isShared_2181_ = v_isSharedCheck_2205_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_tailOff_2178_);
lean_inc(v_size_2176_);
lean_inc(v_tail_2175_);
lean_inc(v_root_2174_);
lean_dec(v_t_2172_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2205_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
uint8_t v___x_2182_; 
v___x_2182_ = lean_nat_dec_le(v_tailOff_2178_, v_i_2173_);
if (v___x_2182_ == 0)
{
size_t v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2183_ = lean_usize_of_nat(v_i_2173_);
v___x_2184_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2171_, v_root_2174_, v___x_2183_, v_shift_2177_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2184_);
v___x_2186_ = v___x_2180_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_tail_2175_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_size_2176_);
lean_ctor_set(v_reuseFailAlloc_2187_, 3, v_tailOff_2178_);
lean_ctor_set_usize(v_reuseFailAlloc_2187_, 4, v_shift_2177_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
else
{
lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
v___x_2188_ = lean_nat_sub(v_i_2173_, v_tailOff_2178_);
v___x_2189_ = lean_array_get_size(v_tail_2175_);
v___x_2190_ = lean_nat_dec_lt(v___x_2188_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2192_; 
lean_dec(v___x_2188_);
lean_dec(v_y_2171_);
if (v_isShared_2181_ == 0)
{
v___x_2192_ = v___x_2180_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_root_2174_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_tail_2175_);
lean_ctor_set(v_reuseFailAlloc_2193_, 2, v_size_2176_);
lean_ctor_set(v_reuseFailAlloc_2193_, 3, v_tailOff_2178_);
lean_ctor_set_usize(v_reuseFailAlloc_2193_, 4, v_shift_2177_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
else
{
lean_object* v_v_2194_; lean_object* v___x_2195_; lean_object* v_xs_x27_2196_; lean_object* v___y_2198_; uint8_t v___x_2203_; 
v_v_2194_ = lean_array_fget(v_tail_2175_, v___x_2188_);
v___x_2195_ = lean_box(0);
v_xs_x27_2196_ = lean_array_fset(v_tail_2175_, v___x_2188_, v___x_2195_);
v___x_2203_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2171_, v_v_2194_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2171_, v___x_2195_, v_v_2194_);
v___y_2198_ = v___x_2204_;
goto v___jp_2197_;
}
else
{
lean_dec(v_y_2171_);
v___y_2198_ = v_v_2194_;
goto v___jp_2197_;
}
v___jp_2197_:
{
lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2199_ = lean_array_fset(v_xs_x27_2196_, v___x_2188_, v___y_2198_);
lean_dec(v___x_2188_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 1, v___x_2199_);
v___x_2201_ = v___x_2180_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_root_2174_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v___x_2199_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_size_2176_);
lean_ctor_set(v_reuseFailAlloc_2202_, 3, v_tailOff_2178_);
lean_ctor_set_usize(v_reuseFailAlloc_2202_, 4, v_shift_2177_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2___boxed(lean_object* v_y_2206_, lean_object* v_t_2207_, lean_object* v_i_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2206_, v_t_2207_, v_i_2208_);
lean_dec(v_i_2208_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(lean_object* v_y_2210_, lean_object* v_x_2211_, lean_object* v_s_2212_){
_start:
{
lean_object* v_vars_2213_; lean_object* v_varMap_2214_; lean_object* v_vars_x27_2215_; lean_object* v_varMap_x27_2216_; lean_object* v_natToIntMap_2217_; lean_object* v_natDef_2218_; lean_object* v_dvds_2219_; lean_object* v_lowers_2220_; lean_object* v_uppers_2221_; lean_object* v_diseqs_2222_; lean_object* v_elimEqs_2223_; lean_object* v_elimStack_2224_; lean_object* v_occurs_2225_; lean_object* v_assignment_2226_; lean_object* v_nextCnstrId_2227_; uint8_t v_caseSplits_2228_; lean_object* v_steps_2229_; lean_object* v_conflict_x3f_2230_; lean_object* v_diseqSplits_2231_; lean_object* v_divMod_2232_; lean_object* v_toIntIds_2233_; lean_object* v_toIntInfos_2234_; lean_object* v_toIntTermMap_2235_; lean_object* v_toIntVarMap_2236_; uint8_t v_usedCommRing_2237_; lean_object* v_nonlinearOccs_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2246_; 
v_vars_2213_ = lean_ctor_get(v_s_2212_, 0);
v_varMap_2214_ = lean_ctor_get(v_s_2212_, 1);
v_vars_x27_2215_ = lean_ctor_get(v_s_2212_, 2);
v_varMap_x27_2216_ = lean_ctor_get(v_s_2212_, 3);
v_natToIntMap_2217_ = lean_ctor_get(v_s_2212_, 4);
v_natDef_2218_ = lean_ctor_get(v_s_2212_, 5);
v_dvds_2219_ = lean_ctor_get(v_s_2212_, 6);
v_lowers_2220_ = lean_ctor_get(v_s_2212_, 7);
v_uppers_2221_ = lean_ctor_get(v_s_2212_, 8);
v_diseqs_2222_ = lean_ctor_get(v_s_2212_, 9);
v_elimEqs_2223_ = lean_ctor_get(v_s_2212_, 10);
v_elimStack_2224_ = lean_ctor_get(v_s_2212_, 11);
v_occurs_2225_ = lean_ctor_get(v_s_2212_, 12);
v_assignment_2226_ = lean_ctor_get(v_s_2212_, 13);
v_nextCnstrId_2227_ = lean_ctor_get(v_s_2212_, 14);
v_caseSplits_2228_ = lean_ctor_get_uint8(v_s_2212_, sizeof(void*)*24);
v_steps_2229_ = lean_ctor_get(v_s_2212_, 15);
v_conflict_x3f_2230_ = lean_ctor_get(v_s_2212_, 16);
v_diseqSplits_2231_ = lean_ctor_get(v_s_2212_, 17);
v_divMod_2232_ = lean_ctor_get(v_s_2212_, 18);
v_toIntIds_2233_ = lean_ctor_get(v_s_2212_, 19);
v_toIntInfos_2234_ = lean_ctor_get(v_s_2212_, 20);
v_toIntTermMap_2235_ = lean_ctor_get(v_s_2212_, 21);
v_toIntVarMap_2236_ = lean_ctor_get(v_s_2212_, 22);
v_usedCommRing_2237_ = lean_ctor_get_uint8(v_s_2212_, sizeof(void*)*24 + 1);
v_nonlinearOccs_2238_ = lean_ctor_get(v_s_2212_, 23);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_s_2212_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2240_ = v_s_2212_;
v_isShared_2241_ = v_isSharedCheck_2246_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_nonlinearOccs_2238_);
lean_inc(v_toIntVarMap_2236_);
lean_inc(v_toIntTermMap_2235_);
lean_inc(v_toIntInfos_2234_);
lean_inc(v_toIntIds_2233_);
lean_inc(v_divMod_2232_);
lean_inc(v_diseqSplits_2231_);
lean_inc(v_conflict_x3f_2230_);
lean_inc(v_steps_2229_);
lean_inc(v_nextCnstrId_2227_);
lean_inc(v_assignment_2226_);
lean_inc(v_occurs_2225_);
lean_inc(v_elimStack_2224_);
lean_inc(v_elimEqs_2223_);
lean_inc(v_diseqs_2222_);
lean_inc(v_uppers_2221_);
lean_inc(v_lowers_2220_);
lean_inc(v_dvds_2219_);
lean_inc(v_natDef_2218_);
lean_inc(v_natToIntMap_2217_);
lean_inc(v_varMap_x27_2216_);
lean_inc(v_vars_x27_2215_);
lean_inc(v_varMap_2214_);
lean_inc(v_vars_2213_);
lean_dec(v_s_2212_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2246_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; lean_object* v___x_2244_; 
v___x_2242_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2210_, v_occurs_2225_, v_x_2211_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 12, v___x_2242_);
v___x_2244_ = v___x_2240_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 24, 2);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_vars_2213_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_varMap_2214_);
lean_ctor_set(v_reuseFailAlloc_2245_, 2, v_vars_x27_2215_);
lean_ctor_set(v_reuseFailAlloc_2245_, 3, v_varMap_x27_2216_);
lean_ctor_set(v_reuseFailAlloc_2245_, 4, v_natToIntMap_2217_);
lean_ctor_set(v_reuseFailAlloc_2245_, 5, v_natDef_2218_);
lean_ctor_set(v_reuseFailAlloc_2245_, 6, v_dvds_2219_);
lean_ctor_set(v_reuseFailAlloc_2245_, 7, v_lowers_2220_);
lean_ctor_set(v_reuseFailAlloc_2245_, 8, v_uppers_2221_);
lean_ctor_set(v_reuseFailAlloc_2245_, 9, v_diseqs_2222_);
lean_ctor_set(v_reuseFailAlloc_2245_, 10, v_elimEqs_2223_);
lean_ctor_set(v_reuseFailAlloc_2245_, 11, v_elimStack_2224_);
lean_ctor_set(v_reuseFailAlloc_2245_, 12, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2245_, 13, v_assignment_2226_);
lean_ctor_set(v_reuseFailAlloc_2245_, 14, v_nextCnstrId_2227_);
lean_ctor_set(v_reuseFailAlloc_2245_, 15, v_steps_2229_);
lean_ctor_set(v_reuseFailAlloc_2245_, 16, v_conflict_x3f_2230_);
lean_ctor_set(v_reuseFailAlloc_2245_, 17, v_diseqSplits_2231_);
lean_ctor_set(v_reuseFailAlloc_2245_, 18, v_divMod_2232_);
lean_ctor_set(v_reuseFailAlloc_2245_, 19, v_toIntIds_2233_);
lean_ctor_set(v_reuseFailAlloc_2245_, 20, v_toIntInfos_2234_);
lean_ctor_set(v_reuseFailAlloc_2245_, 21, v_toIntTermMap_2235_);
lean_ctor_set(v_reuseFailAlloc_2245_, 22, v_toIntVarMap_2236_);
lean_ctor_set(v_reuseFailAlloc_2245_, 23, v_nonlinearOccs_2238_);
lean_ctor_set_uint8(v_reuseFailAlloc_2245_, sizeof(void*)*24, v_caseSplits_2228_);
lean_ctor_set_uint8(v_reuseFailAlloc_2245_, sizeof(void*)*24 + 1, v_usedCommRing_2237_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed(lean_object* v_y_2247_, lean_object* v_x_2248_, lean_object* v_s_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(v_y_2247_, v_x_2248_, v_s_2249_);
lean_dec(v_x_2248_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(lean_object* v_x_2251_, lean_object* v_y_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2251_, v_a_2253_, v_a_2254_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2269_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2269_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2269_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
uint8_t v___x_2261_; 
v___x_2261_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2252_, v_a_2257_);
lean_dec(v_a_2257_);
if (v___x_2261_ == 0)
{
lean_object* v___f_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
lean_del_object(v___x_2259_);
v___f_2262_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2262_, 0, v_y_2252_);
lean_closure_set(v___f_2262_, 1, v_x_2251_);
v___x_2263_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2264_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2263_, v___f_2262_, v_a_2253_);
return v___x_2264_;
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2267_; 
lean_dec(v_y_2252_);
lean_dec(v_x_2251_);
v___x_2265_ = lean_box(0);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2265_);
v___x_2267_ = v___x_2259_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec(v_y_2252_);
lean_dec(v_x_2251_);
v_a_2270_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2256_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2256_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___boxed(lean_object* v_x_2278_, lean_object* v_y_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2278_, v_y_2279_, v_a_2280_, v_a_2281_);
lean_dec_ref(v_a_2281_);
lean_dec(v_a_2280_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc(lean_object* v_x_2284_, lean_object* v_y_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2284_, v_y_2285_, v_a_2286_, v_a_2294_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___boxed(lean_object* v_x_2298_, lean_object* v_y_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc(v_x_2298_, v_y_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
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
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(lean_object* v_00_u03b2_2312_, lean_object* v_k_2313_, lean_object* v_t_2314_){
_start:
{
uint8_t v___x_2315_; 
v___x_2315_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2313_, v_t_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2316_, lean_object* v_k_2317_, lean_object* v_t_2318_){
_start:
{
uint8_t v_res_2319_; lean_object* v_r_2320_; 
v_res_2319_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(v_00_u03b2_2316_, v_k_2317_, v_t_2318_);
lean_dec(v_t_2318_);
lean_dec(v_k_2317_);
v_r_2320_ = lean_box(v_res_2319_);
return v_r_2320_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1(lean_object* v_00_u03b2_2321_, lean_object* v_k_2322_, lean_object* v_v_2323_, lean_object* v_t_2324_, lean_object* v_hl_2325_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2322_, v_v_2323_, v_t_2324_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(lean_object* v_y_2327_, lean_object* v_p_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
if (lean_obj_tag(v_p_2328_) == 1)
{
lean_object* v_v_2332_; lean_object* v_p_2333_; lean_object* v___x_2334_; 
v_v_2332_ = lean_ctor_get(v_p_2328_, 1);
lean_inc(v_v_2332_);
v_p_2333_ = lean_ctor_get(v_p_2328_, 2);
lean_inc_ref(v_p_2333_);
lean_dec_ref_known(v_p_2328_, 3);
lean_inc(v_y_2327_);
v___x_2334_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_v_2332_, v_y_2327_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_dec_ref_known(v___x_2334_, 1);
v_p_2328_ = v_p_2333_;
goto _start;
}
else
{
lean_dec_ref(v_p_2333_);
lean_dec(v_y_2327_);
return v___x_2334_;
}
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec_ref(v_p_2328_);
lean_dec(v_y_2327_);
v___x_2336_ = lean_box(0);
v___x_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
return v___x_2337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg___boxed(lean_object* v_y_2338_, lean_object* v_p_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2338_, v_p_2339_, v_a_2340_, v_a_2341_);
lean_dec_ref(v_a_2341_);
lean_dec(v_a_2340_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(lean_object* v_y_2344_, lean_object* v_p_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2344_, v_p_2345_, v_a_2346_, v_a_2354_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___boxed(lean_object* v_y_2358_, lean_object* v_p_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(v_y_2358_, v_p_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
lean_dec(v_a_2369_);
lean_dec_ref(v_a_2368_);
lean_dec(v_a_2367_);
lean_dec_ref(v_a_2366_);
lean_dec(v_a_2365_);
lean_dec_ref(v_a_2364_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
lean_dec(v_a_2361_);
lean_dec(v_a_2360_);
return v_res_2371_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = ((lean_object*)(l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__0));
v___x_2374_ = l_Lean_stringToMessageData(v___x_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg(lean_object* v_p_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
if (lean_obj_tag(v_p_2375_) == 1)
{
lean_object* v_v_2382_; lean_object* v_p_2383_; lean_object* v___x_2384_; 
v_v_2382_ = lean_ctor_get(v_p_2375_, 1);
lean_inc(v_v_2382_);
v_p_2383_ = lean_ctor_get(v_p_2375_, 2);
lean_inc_ref(v_p_2383_);
lean_dec_ref_known(v_p_2375_, 3);
v___x_2384_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_v_2382_, v_p_2383_, v_a_2376_, v_a_2379_);
return v___x_2384_;
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec_ref(v_p_2375_);
v___x_2385_ = lean_obj_once(&l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1, &l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1_once, _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1);
v___x_2386_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2385_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2386_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg___boxed(lean_object* v_p_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs(lean_object* v_p_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2395_, v_a_2396_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___boxed(lean_object* v_p_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Int_Internal_Linear_Poly_updateOccs(v_p_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
lean_dec(v_a_2410_);
lean_dec(v_a_2409_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go_spec__0(lean_object* v_a_2421_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Rat_ofInt(v_a_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(lean_object* v_a_2423_, lean_object* v_v_2424_, lean_object* v_a_2425_){
_start:
{
if (lean_obj_tag(v_a_2425_) == 0)
{
lean_object* v_k_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2435_; 
v_k_2426_ = lean_ctor_get(v_a_2425_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_a_2425_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2428_ = v_a_2425_;
v_isShared_2429_ = v_isSharedCheck_2435_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_k_2426_);
lean_dec(v_a_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2435_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2430_ = l_Rat_ofInt(v_k_2426_);
v___x_2431_ = l_Rat_add(v_v_2424_, v___x_2430_);
if (v_isShared_2429_ == 0)
{
lean_ctor_set_tag(v___x_2428_, 1);
lean_ctor_set(v___x_2428_, 0, v___x_2431_);
v___x_2433_ = v___x_2428_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
else
{
lean_object* v_k_2436_; lean_object* v_v_2437_; lean_object* v_p_2438_; lean_object* v_size_2439_; uint8_t v___x_2440_; 
v_k_2436_ = lean_ctor_get(v_a_2425_, 0);
lean_inc(v_k_2436_);
v_v_2437_ = lean_ctor_get(v_a_2425_, 1);
lean_inc(v_v_2437_);
v_p_2438_ = lean_ctor_get(v_a_2425_, 2);
lean_inc_ref(v_p_2438_);
lean_dec_ref_known(v_a_2425_, 3);
v_size_2439_ = lean_ctor_get(v_a_2423_, 2);
v___x_2440_ = lean_nat_dec_lt(v_v_2437_, v_size_2439_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; 
lean_dec_ref(v_p_2438_);
lean_dec(v_v_2437_);
lean_dec(v_k_2436_);
lean_dec_ref(v_v_2424_);
v___x_2441_ = lean_box(0);
return v___x_2441_;
}
else
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2442_ = l_Rat_ofInt(v_k_2436_);
v___x_2443_ = l_instInhabitedRat;
v___x_2444_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2443_, v_a_2423_, v_v_2437_);
lean_dec(v_v_2437_);
v___x_2445_ = l_Rat_mul(v___x_2442_, v___x_2444_);
lean_dec_ref(v___x_2442_);
v___x_2446_ = l_Rat_add(v_v_2424_, v___x_2445_);
v_v_2424_ = v___x_2446_;
v_a_2425_ = v_p_2438_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go___boxed(lean_object* v_a_2448_, lean_object* v_v_2449_, lean_object* v_a_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_a_2448_, v_v_2449_, v_a_2450_);
lean_dec_ref(v_a_2448_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(lean_object* v_a_2452_){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_nat_to_int(v_a_2452_);
v___x_2454_ = l_Rat_ofInt(v___x_2453_);
return v___x_2454_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = lean_unsigned_to_nat(0u);
v___x_2456_ = l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(v___x_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg(lean_object* v_p_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2458_, v_a_2459_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2472_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2472_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2472_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v_assignment_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; 
v_assignment_2466_ = lean_ctor_get(v_a_2462_, 13);
lean_inc_ref(v_assignment_2466_);
lean_dec(v_a_2462_);
v___x_2467_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2468_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_assignment_2466_, v___x_2467_, v_p_2457_);
lean_dec_ref(v_assignment_2466_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2468_);
v___x_2470_ = v___x_2464_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec_ref(v_p_2457_);
v_a_2473_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2461_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2461_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg___boxed(lean_object* v_p_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2481_, v_a_2482_, v_a_2483_);
lean_dec_ref(v_a_2483_);
lean_dec(v_a_2482_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f(lean_object* v_p_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2486_, v_a_2487_, v_a_2495_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___boxed(lean_object* v_p_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Int_Internal_Linear_Poly_eval_x3f(v_p_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
lean_dec(v_a_2509_);
lean_dec_ref(v_a_2508_);
lean_dec(v_a_2507_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
lean_dec(v_a_2500_);
return v_res_2511_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(lean_object* v_c_2512_){
_start:
{
lean_object* v_p_2513_; uint8_t v___x_2514_; 
v_p_2513_ = lean_ctor_get(v_c_2512_, 0);
v___x_2514_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat___boxed(lean_object* v_c_2515_){
_start:
{
uint8_t v_res_2516_; lean_object* v_r_2517_; 
v_res_2516_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(v_c_2515_);
lean_dec_ref(v_c_2515_);
v_r_2517_ = lean_box(v_res_2516_);
return v_r_2517_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(lean_object* v_c_2518_){
_start:
{
lean_object* v_d_2519_; lean_object* v_p_2520_; uint8_t v___x_2521_; 
v_d_2519_ = lean_ctor_get(v_c_2518_, 0);
lean_inc(v_d_2519_);
v_p_2520_ = lean_ctor_get(v_c_2518_, 1);
lean_inc_ref(v_p_2520_);
lean_dec_ref(v_c_2518_);
v___x_2521_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_2519_, v_p_2520_);
lean_dec_ref(v_p_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat___boxed(lean_object* v_c_2522_){
_start:
{
uint8_t v_res_2523_; lean_object* v_r_2524_; 
v_res_2523_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(v_c_2522_);
v_r_2524_ = lean_box(v_res_2523_);
return v_r_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object* v_c_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v_d_2529_; lean_object* v_p_2530_; lean_object* v___x_2531_; 
v_d_2529_ = lean_ctor_get(v_c_2525_, 0);
lean_inc(v_d_2529_);
v_p_2530_ = lean_ctor_get(v_c_2525_, 1);
lean_inc_ref(v_p_2530_);
lean_dec_ref(v_c_2525_);
v___x_2531_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2530_, v_a_2526_, v_a_2527_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2557_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2557_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2557_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
if (lean_obj_tag(v_a_2532_) == 1)
{
lean_object* v_val_2536_; lean_object* v_num_2537_; lean_object* v_den_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v_val_2536_ = lean_ctor_get(v_a_2532_, 0);
lean_inc(v_val_2536_);
lean_dec_ref_known(v_a_2532_, 1);
v_num_2537_ = lean_ctor_get(v_val_2536_, 0);
lean_inc(v_num_2537_);
v_den_2538_ = lean_ctor_get(v_val_2536_, 1);
lean_inc(v_den_2538_);
lean_dec(v_val_2536_);
v___x_2539_ = lean_unsigned_to_nat(1u);
v___x_2540_ = lean_nat_dec_eq(v_den_2538_, v___x_2539_);
lean_dec(v_den_2538_);
if (v___x_2540_ == 0)
{
uint8_t v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2544_; 
lean_dec(v_num_2537_);
lean_dec(v_d_2529_);
v___x_2541_ = 0;
v___x_2542_ = lean_box(v___x_2541_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v___x_2542_);
v___x_2544_ = v___x_2534_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
else
{
uint8_t v___x_2546_; uint8_t v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2550_; 
v___x_2546_ = l_Int_decidableDvd(v_d_2529_, v_num_2537_);
lean_dec(v_num_2537_);
lean_dec(v_d_2529_);
v___x_2547_ = l_Lean_Bool_toLBool(v___x_2546_);
v___x_2548_ = lean_box(v___x_2547_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v___x_2548_);
v___x_2550_ = v___x_2534_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2548_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
else
{
uint8_t v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
lean_dec(v_a_2532_);
lean_dec(v_d_2529_);
v___x_2552_ = 2;
v___x_2553_ = lean_box(v___x_2552_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v___x_2553_);
v___x_2555_ = v___x_2534_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
lean_dec(v_d_2529_);
v_a_2558_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2531_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2531_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg___boxed(lean_object* v_c_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2566_, v_a_2567_, v_a_2568_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(lean_object* v_c_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2571_, v_a_2572_, v_a_2580_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___boxed(lean_object* v_c_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(v_c_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
lean_dec(v_a_2594_);
lean_dec_ref(v_a_2593_);
lean_dec(v_a_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec(v_a_2585_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg(lean_object* v_p_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2597_, v_a_2598_, v_a_2599_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2619_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2619_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2619_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
if (lean_obj_tag(v_a_2602_) == 1)
{
lean_object* v_val_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; uint8_t v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2612_; 
v_val_2606_ = lean_ctor_get(v_a_2602_, 0);
lean_inc(v_val_2606_);
lean_dec_ref_known(v_a_2602_, 1);
v___x_2607_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2608_ = l_Rat_instDecidableLe(v_val_2606_, v___x_2607_);
v___x_2609_ = l_Lean_Bool_toLBool(v___x_2608_);
v___x_2610_ = lean_box(v___x_2609_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2610_);
v___x_2612_ = v___x_2604_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2610_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
else
{
uint8_t v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2617_; 
lean_dec(v_a_2602_);
v___x_2614_ = 2;
v___x_2615_ = lean_box(v___x_2614_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2615_);
v___x_2617_ = v___x_2604_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
v_a_2620_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2601_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2601_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg___boxed(lean_object* v_p_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2628_, v_a_2629_, v_a_2630_);
lean_dec_ref(v_a_2630_);
lean_dec(v_a_2629_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe(lean_object* v_p_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2633_, v_a_2634_, v_a_2642_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___boxed(lean_object* v_p_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Int_Internal_Linear_Poly_satisfiedLe(v_p_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec(v_a_2647_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(lean_object* v_c_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v_p_2663_; lean_object* v___x_2664_; 
v_p_2663_ = lean_ctor_get(v_c_2659_, 0);
lean_inc_ref(v_p_2663_);
lean_dec_ref(v_c_2659_);
v___x_2664_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2663_, v_a_2660_, v_a_2661_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg___boxed(lean_object* v_c_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2665_, v_a_2666_, v_a_2667_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(lean_object* v_c_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2670_, v_a_2671_, v_a_2679_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___boxed(lean_object* v_c_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(v_c_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec(v_a_2684_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(lean_object* v_c_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v_p_2700_; lean_object* v___x_2701_; 
v_p_2700_ = lean_ctor_get(v_c_2696_, 0);
lean_inc_ref(v_p_2700_);
lean_dec_ref(v_c_2696_);
v___x_2701_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2700_, v_a_2697_, v_a_2698_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2721_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2704_ = v___x_2701_;
v_isShared_2705_ = v_isSharedCheck_2721_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2701_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2721_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
uint8_t v___y_2707_; 
if (lean_obj_tag(v_a_2702_) == 1)
{
lean_object* v_val_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
v_val_2713_ = lean_ctor_get(v_a_2702_, 0);
lean_inc(v_val_2713_);
lean_dec_ref_known(v_a_2702_, 1);
v___x_2714_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2715_ = l_instDecidableEqRat_decEq(v_val_2713_, v___x_2714_);
lean_dec(v_val_2713_);
if (v___x_2715_ == 0)
{
uint8_t v___x_2716_; 
v___x_2716_ = 1;
v___y_2707_ = v___x_2716_;
goto v___jp_2706_;
}
else
{
uint8_t v___x_2717_; 
v___x_2717_ = 0;
v___y_2707_ = v___x_2717_;
goto v___jp_2706_;
}
}
else
{
uint8_t v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
lean_del_object(v___x_2704_);
lean_dec(v_a_2702_);
v___x_2718_ = 2;
v___x_2719_ = lean_box(v___x_2718_);
v___x_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
return v___x_2720_;
}
v___jp_2706_:
{
uint8_t v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2711_; 
v___x_2708_ = l_Lean_Bool_toLBool(v___y_2707_);
v___x_2709_ = lean_box(v___x_2708_);
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 0, v___x_2709_);
v___x_2711_ = v___x_2704_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2709_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
v_a_2722_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2701_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2701_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg___boxed(lean_object* v_c_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_2730_, v_a_2731_, v_a_2732_);
lean_dec_ref(v_a_2732_);
lean_dec(v_a_2731_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(lean_object* v_c_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_2735_, v_a_2736_, v_a_2744_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___boxed(lean_object* v_c_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(v_c_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
lean_dec(v_a_2758_);
lean_dec_ref(v_a_2757_);
lean_dec(v_a_2756_);
lean_dec_ref(v_a_2755_);
lean_dec(v_a_2754_);
lean_dec_ref(v_a_2753_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec(v_a_2749_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(lean_object* v_c_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v_p_2765_; lean_object* v___x_2766_; 
v_p_2765_ = lean_ctor_get(v_c_2761_, 0);
lean_inc_ref(v_p_2765_);
lean_dec_ref(v_c_2761_);
v___x_2766_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2765_, v_a_2762_, v_a_2763_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2784_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2769_ = v___x_2766_;
v_isShared_2770_ = v_isSharedCheck_2784_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2766_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2784_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
if (lean_obj_tag(v_a_2767_) == 1)
{
lean_object* v_val_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; uint8_t v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2777_; 
v_val_2771_ = lean_ctor_get(v_a_2767_, 0);
lean_inc(v_val_2771_);
lean_dec_ref_known(v_a_2767_, 1);
v___x_2772_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2773_ = l_instDecidableEqRat_decEq(v_val_2771_, v___x_2772_);
lean_dec(v_val_2771_);
v___x_2774_ = l_Lean_Bool_toLBool(v___x_2773_);
v___x_2775_ = lean_box(v___x_2774_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 0, v___x_2775_);
v___x_2777_ = v___x_2769_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
else
{
uint8_t v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2782_; 
lean_dec(v_a_2767_);
v___x_2779_ = 2;
v___x_2780_ = lean_box(v___x_2779_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 0, v___x_2780_);
v___x_2782_ = v___x_2769_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2780_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
v_a_2785_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2766_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2766_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg___boxed(lean_object* v_c_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_2793_, v_a_2794_, v_a_2795_);
lean_dec_ref(v_a_2795_);
lean_dec(v_a_2794_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(lean_object* v_c_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_2798_, v_a_2799_, v_a_2807_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___boxed(lean_object* v_c_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(v_c_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2820_);
lean_dec(v_a_2819_);
lean_dec_ref(v_a_2818_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2813_);
lean_dec(v_a_2812_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg(lean_object* v_p_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_){
_start:
{
if (lean_obj_tag(v_p_2824_) == 0)
{
lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2835_; 
v_isSharedCheck_2835_ = !lean_is_exclusive(v_p_2824_);
if (v_isSharedCheck_2835_ == 0)
{
lean_object* v_unused_2836_; 
v_unused_2836_ = lean_ctor_get(v_p_2824_, 0);
lean_dec(v_unused_2836_);
v___x_2829_ = v_p_2824_;
v_isShared_2830_ = v_isSharedCheck_2835_;
goto v_resetjp_2828_;
}
else
{
lean_dec(v_p_2824_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2835_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2831_; lean_object* v___x_2833_; 
v___x_2831_ = lean_box(0);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v___x_2831_);
v___x_2833_ = v___x_2829_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2831_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
else
{
lean_object* v_k_2837_; lean_object* v_v_2838_; lean_object* v_p_2839_; lean_object* v___x_2840_; 
v_k_2837_ = lean_ctor_get(v_p_2824_, 0);
lean_inc(v_k_2837_);
v_v_2838_ = lean_ctor_get(v_p_2824_, 1);
lean_inc(v_v_2838_);
v_p_2839_ = lean_ctor_get(v_p_2824_, 2);
lean_inc_ref(v_p_2839_);
lean_dec_ref_known(v_p_2824_, 3);
v___x_2840_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2825_, v_a_2826_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2867_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_2867_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2867_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___y_2846_; lean_object* v_elimEqs_2861_; lean_object* v_size_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; 
v_elimEqs_2861_ = lean_ctor_get(v_a_2841_, 10);
lean_inc_ref(v_elimEqs_2861_);
lean_dec(v_a_2841_);
v_size_2862_ = lean_ctor_get(v_elimEqs_2861_, 2);
v___x_2863_ = lean_box(0);
v___x_2864_ = lean_nat_dec_lt(v_v_2838_, v_size_2862_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2865_; 
lean_dec_ref(v_elimEqs_2861_);
v___x_2865_ = l_outOfBounds___redArg(v___x_2863_);
v___y_2846_ = v___x_2865_;
goto v___jp_2845_;
}
else
{
lean_object* v___x_2866_; 
v___x_2866_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2863_, v_elimEqs_2861_, v_v_2838_);
lean_dec_ref(v_elimEqs_2861_);
v___y_2846_ = v___x_2866_;
goto v___jp_2845_;
}
v___jp_2845_:
{
if (lean_obj_tag(v___y_2846_) == 1)
{
lean_object* v_val_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2859_; 
lean_dec_ref(v_p_2839_);
v_val_2847_ = lean_ctor_get(v___y_2846_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___y_2846_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2849_ = v___y_2846_;
v_isShared_2850_ = v_isSharedCheck_2859_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_val_2847_);
lean_dec(v___y_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2859_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2854_; 
v___x_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2851_, 0, v_v_2838_);
lean_ctor_set(v___x_2851_, 1, v_val_2847_);
v___x_2852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2852_, 0, v_k_2837_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2852_);
v___x_2854_ = v___x_2849_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2852_);
v___x_2854_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2856_; 
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v___x_2854_);
v___x_2856_ = v___x_2843_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
else
{
lean_dec(v___y_2846_);
lean_del_object(v___x_2843_);
lean_dec(v_v_2838_);
lean_dec(v_k_2837_);
v_p_2824_ = v_p_2839_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec_ref(v_p_2839_);
lean_dec(v_v_2838_);
lean_dec(v_k_2837_);
v_a_2868_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2840_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2840_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg___boxed(lean_object* v_p_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_2876_, v_a_2877_, v_a_2878_);
lean_dec_ref(v_a_2878_);
lean_dec(v_a_2877_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst(lean_object* v_p_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_2881_, v_a_2882_, v_a_2890_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___boxed(lean_object* v_p_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Int_Internal_Linear_Poly_findVarToSubst(v_p_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
lean_dec(v_a_2896_);
lean_dec(v_a_2895_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(lean_object* v_pred_2907_){
_start:
{
lean_object* v_c_u2081_2908_; lean_object* v_c_u2082_2909_; uint8_t v_left_2910_; lean_object* v_c_u2083_x3f_2911_; lean_object* v_p_2912_; lean_object* v_p_2913_; lean_object* v_a_2914_; lean_object* v_b_2915_; 
v_c_u2081_2908_ = lean_ctor_get(v_pred_2907_, 0);
v_c_u2082_2909_ = lean_ctor_get(v_pred_2907_, 1);
v_left_2910_ = lean_ctor_get_uint8(v_pred_2907_, sizeof(void*)*3);
v_c_u2083_x3f_2911_ = lean_ctor_get(v_pred_2907_, 2);
v_p_2912_ = lean_ctor_get(v_c_u2081_2908_, 0);
v_p_2913_ = lean_ctor_get(v_c_u2082_2909_, 0);
v_a_2914_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_2912_);
v_b_2915_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_2913_);
if (lean_obj_tag(v_c_u2083_x3f_2911_) == 0)
{
if (v_left_2910_ == 0)
{
lean_object* v___x_2916_; 
lean_dec(v_a_2914_);
v___x_2916_ = lean_nat_abs(v_b_2915_);
lean_dec(v_b_2915_);
return v___x_2916_;
}
else
{
lean_object* v___x_2917_; 
lean_dec(v_b_2915_);
v___x_2917_ = lean_nat_abs(v_a_2914_);
lean_dec(v_a_2914_);
return v___x_2917_;
}
}
else
{
lean_object* v_val_2918_; lean_object* v_d_2919_; lean_object* v_p_2920_; lean_object* v_c_2921_; 
v_val_2918_ = lean_ctor_get(v_c_u2083_x3f_2911_, 0);
v_d_2919_ = lean_ctor_get(v_val_2918_, 0);
v_p_2920_ = lean_ctor_get(v_val_2918_, 1);
v_c_2921_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_2920_);
if (v_left_2910_ == 0)
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
lean_dec(v_a_2914_);
v___x_2922_ = lean_int_mul(v_b_2915_, v_d_2919_);
v___x_2923_ = l_Int_gcd(v___x_2922_, v_c_2921_);
lean_dec(v_c_2921_);
v___x_2924_ = lean_nat_to_int(v___x_2923_);
v___x_2925_ = lean_int_ediv(v___x_2922_, v___x_2924_);
lean_dec(v___x_2924_);
lean_dec(v___x_2922_);
v___x_2926_ = l_Int_lcm(v_b_2915_, v___x_2925_);
lean_dec(v___x_2925_);
lean_dec(v_b_2915_);
return v___x_2926_;
}
else
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
lean_dec(v_b_2915_);
v___x_2927_ = lean_int_mul(v_a_2914_, v_d_2919_);
v___x_2928_ = l_Int_gcd(v___x_2927_, v_c_2921_);
lean_dec(v_c_2921_);
v___x_2929_ = lean_nat_to_int(v___x_2928_);
v___x_2930_ = lean_int_ediv(v___x_2927_, v___x_2929_);
lean_dec(v___x_2929_);
lean_dec(v___x_2927_);
v___x_2931_ = l_Int_lcm(v_a_2914_, v___x_2930_);
lean_dec(v___x_2930_);
lean_dec(v_a_2914_);
return v___x_2931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases___boxed(lean_object* v_pred_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(v_pred_2932_);
lean_dec_ref(v_pred_2932_);
return v_res_2933_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0));
v___x_2936_ = l_Lean_stringToMessageData(v___x_2935_);
return v___x_2936_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4(void){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3));
v___x_2941_ = l_Lean_MessageData_ofFormat(v___x_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(lean_object* v_pred_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v_c_u2081_2946_; lean_object* v_c_u2082_2947_; lean_object* v_c_u2083_x3f_2948_; lean_object* v___x_2949_; 
v_c_u2081_2946_ = lean_ctor_get(v_pred_2942_, 0);
lean_inc_ref(v_c_u2081_2946_);
v_c_u2082_2947_ = lean_ctor_get(v_pred_2942_, 1);
lean_inc_ref(v_c_u2082_2947_);
v_c_u2083_x3f_2948_ = lean_ctor_get(v_pred_2942_, 2);
lean_inc(v_c_u2083_x3f_2948_);
lean_dec_ref(v_pred_2942_);
v___x_2949_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_2946_, v_a_2943_, v_a_2944_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2949_, 1);
v___x_2951_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_2947_, v_a_2943_, v_a_2944_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2970_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2954_ = v___x_2951_;
v_isShared_2955_ = v_isSharedCheck_2970_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2951_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2970_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v_____do__lift_2957_; 
if (lean_obj_tag(v_c_u2083_x3f_2948_) == 1)
{
lean_object* v_val_2966_; lean_object* v___x_2967_; 
v_val_2966_ = lean_ctor_get(v_c_u2083_x3f_2948_, 0);
lean_inc(v_val_2966_);
lean_dec_ref_known(v_c_u2083_x3f_2948_, 1);
v___x_2967_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_val_2966_, v_a_2943_, v_a_2944_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2967_, 1);
v_____do__lift_2957_ = v_a_2968_;
goto v___jp_2956_;
}
else
{
lean_del_object(v___x_2954_);
lean_dec(v_a_2952_);
lean_dec(v_a_2950_);
return v___x_2967_;
}
}
else
{
lean_object* v___x_2969_; 
lean_dec(v_c_u2083_x3f_2948_);
v___x_2969_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4);
v_____do__lift_2957_ = v___x_2969_;
goto v___jp_2956_;
}
v___jp_2956_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2964_; 
v___x_2958_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2959_, 0, v_a_2950_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
lean_ctor_set(v___x_2960_, 1, v_a_2952_);
v___x_2961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
lean_ctor_set(v___x_2961_, 1, v___x_2958_);
v___x_2962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
lean_ctor_set(v___x_2962_, 1, v_____do__lift_2957_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 0, v___x_2962_);
v___x_2964_ = v___x_2954_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
else
{
lean_dec(v_a_2950_);
lean_dec(v_c_u2083_x3f_2948_);
return v___x_2951_;
}
}
else
{
lean_dec(v_c_u2083_x3f_2948_);
lean_dec_ref(v_c_u2082_2947_);
return v___x_2949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___boxed(lean_object* v_pred_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_2971_, v_a_2972_, v_a_2973_);
lean_dec_ref(v_a_2973_);
lean_dec(v_a_2972_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(lean_object* v_pred_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_2976_, v_a_2977_, v_a_2985_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___boxed(lean_object* v_pred_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(v_pred_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_);
lean_dec(v_a_2999_);
lean_dec_ref(v_a_2998_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec(v_a_2990_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(lean_object* v_h_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_){
_start:
{
switch(lean_obj_tag(v_h_3002_))
{
case 0:
{
lean_object* v_c_3006_; lean_object* v___x_3007_; 
v_c_3006_ = lean_ctor_get(v_h_3002_, 0);
lean_inc_ref(v_c_3006_);
lean_dec_ref_known(v_h_3002_, 1);
v___x_3007_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_3006_, v_a_3003_, v_a_3004_);
return v___x_3007_;
}
case 1:
{
lean_object* v_c_3008_; lean_object* v___x_3009_; 
v_c_3008_ = lean_ctor_get(v_h_3002_, 0);
lean_inc_ref(v_c_3008_);
lean_dec_ref_known(v_h_3002_, 1);
v___x_3009_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3008_, v_a_3003_, v_a_3004_);
return v___x_3009_;
}
case 2:
{
lean_object* v_c_3010_; lean_object* v___x_3011_; 
v_c_3010_ = lean_ctor_get(v_h_3002_, 0);
lean_inc_ref(v_c_3010_);
lean_dec_ref_known(v_h_3002_, 1);
v___x_3011_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_3010_, v_a_3003_, v_a_3004_);
return v___x_3011_;
}
case 3:
{
lean_object* v_c_3012_; lean_object* v___x_3013_; 
v_c_3012_ = lean_ctor_get(v_h_3002_, 0);
lean_inc_ref(v_c_3012_);
lean_dec_ref_known(v_h_3002_, 1);
v___x_3013_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_3012_, v_a_3003_, v_a_3004_);
return v___x_3013_;
}
default: 
{
lean_object* v_c_u2081_3014_; lean_object* v_c_u2082_3015_; lean_object* v_c_u2083_3016_; lean_object* v___x_3017_; 
v_c_u2081_3014_ = lean_ctor_get(v_h_3002_, 0);
lean_inc_ref(v_c_u2081_3014_);
v_c_u2082_3015_ = lean_ctor_get(v_h_3002_, 1);
lean_inc_ref(v_c_u2082_3015_);
v_c_u2083_3016_ = lean_ctor_get(v_h_3002_, 2);
lean_inc_ref(v_c_u2083_3016_);
lean_dec_ref_known(v_h_3002_, 3);
v___x_3017_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3014_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3019_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3019_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3015_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3021_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v___x_3019_, 1);
v___x_3021_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2083_3016_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3034_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3024_ = v___x_3021_;
v_isShared_3025_ = v_isSharedCheck_3034_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3034_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3032_; 
v___x_3026_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3027_, 0, v_a_3018_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
v___x_3028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
lean_ctor_set(v___x_3028_, 1, v_a_3020_);
v___x_3029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
lean_ctor_set(v___x_3029_, 1, v___x_3026_);
v___x_3030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
lean_ctor_set(v___x_3030_, 1, v_a_3022_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3030_);
v___x_3032_ = v___x_3024_;
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
else
{
lean_dec(v_a_3020_);
lean_dec(v_a_3018_);
return v___x_3021_;
}
}
else
{
lean_dec(v_a_3018_);
lean_dec_ref(v_c_u2083_3016_);
return v___x_3019_;
}
}
else
{
lean_dec_ref(v_c_u2083_3016_);
lean_dec_ref(v_c_u2082_3015_);
return v___x_3017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg___boxed(lean_object* v_h_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3035_, v_a_3036_, v_a_3037_);
lean_dec_ref(v_a_3037_);
lean_dec(v_a_3036_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(lean_object* v_h_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3040_, v_a_3041_, v_a_3049_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___boxed(lean_object* v_h_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(v_h_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec_ref(v_a_3058_);
lean_dec(v_a_3057_);
lean_dec_ref(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec(v_a_3054_);
return v_res_3065_;
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
