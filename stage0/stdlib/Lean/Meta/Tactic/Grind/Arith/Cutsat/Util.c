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
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_denoteExpr___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_mkIntLE(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
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
uint8_t l_Bool_toLBool(uint8_t);
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
uint8_t l_Int_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatLe(lean_object*);
uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object*);
lean_object* l_Int_Linear_Poly_leadCoeff(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Int_gcd(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Int_lcm(lean_object*, lean_object*);
static lean_once_cell_t l_Int_Linear_Poly_isZero___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Linear_Poly_isZero___closed__0;
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isZero(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isZero___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_isSorted_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_isSorted_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isSorted(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isSorted___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " + "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_pp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_pp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_pp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Int_Linear_Poly_updateOccs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "`grind` internal error, unexpected constant polynomial"};
static const lean_object* l_Int_Linear_Poly_updateOccs___redArg___closed__0 = (const lean_object*)&l_Int_Linear_Poly_updateOccs___redArg___closed__0_value;
static lean_once_cell_t l_Int_Linear_Poly_updateOccs___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Linear_Poly_updateOccs___redArg___closed__1;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_updateOccs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_updateOccs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_Linear_Poly_eval_x3f_spec__0(lean_object*);
static lean_once_cell_t l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Linear_Poly_eval_x3f___redArg___closed__0;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_eval_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_eval_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_eval_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_eval_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_satisfiedLe___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_satisfiedLe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_satisfiedLe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_satisfiedLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Int_Linear_Poly_findVarToSubst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_findVarToSubst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_findVarToSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_findVarToSubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Int_Linear_Poly_isZero___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isZero(lean_object* v_x_3_){
_start:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v_k_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v_k_4_ = lean_ctor_get(v_x_3_, 0);
v___x_5_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
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
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isZero___boxed(lean_object* v_x_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l_Int_Linear_Poly_isZero(v_x_8_);
lean_dec_ref(v_x_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_isSorted_go(lean_object* v_a_11_, lean_object* v_a_12_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_isSorted_go___boxed(lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_isSorted_go(v_a_30_, v_a_31_);
lean_dec_ref(v_a_31_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isSorted(lean_object* v_p_34_){
_start:
{
lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_35_ = lean_box(0);
v___x_36_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_isSorted_go(v___x_35_, v_p_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isSorted___boxed(lean_object* v_p_37_){
_start:
{
uint8_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = l_Int_Linear_Poly_isSorted(v_p_37_);
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
lean_object* v_k_x27_306_; uint8_t v___x_307_; 
v_k_x27_306_ = lean_array_fget_borrowed(v_keys_301_, v_i_302_);
v___x_307_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_303_, v_k_x27_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_add(v_i_302_, v___x_308_);
lean_dec(v_i_302_);
v_i_302_ = v___x_309_;
goto _start;
}
else
{
lean_dec(v_i_302_);
return v___x_307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_311_, lean_object* v_i_312_, lean_object* v_k_313_){
_start:
{
uint8_t v_res_314_; lean_object* v_r_315_; 
v_res_314_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_311_, v_i_312_, v_k_313_);
lean_dec_ref(v_k_313_);
lean_dec_ref(v_keys_311_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(lean_object* v_x_316_, size_t v_x_317_, lean_object* v_x_318_){
_start:
{
if (lean_obj_tag(v_x_316_) == 0)
{
lean_object* v_es_319_; lean_object* v___x_320_; size_t v___x_321_; size_t v___x_322_; lean_object* v_j_323_; lean_object* v___x_324_; 
v_es_319_ = lean_ctor_get(v_x_316_, 0);
v___x_320_ = lean_box(2);
v___x_321_ = ((size_t)31ULL);
v___x_322_ = lean_usize_land(v_x_317_, v___x_321_);
v_j_323_ = lean_usize_to_nat(v___x_322_);
v___x_324_ = lean_array_get_borrowed(v___x_320_, v_es_319_, v_j_323_);
lean_dec(v_j_323_);
switch(lean_obj_tag(v___x_324_))
{
case 0:
{
lean_object* v_key_325_; uint8_t v___x_326_; 
v_key_325_ = lean_ctor_get(v___x_324_, 0);
v___x_326_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_318_, v_key_325_);
return v___x_326_;
}
case 1:
{
lean_object* v_node_327_; size_t v___x_328_; size_t v___x_329_; 
v_node_327_ = lean_ctor_get(v___x_324_, 0);
v___x_328_ = ((size_t)5ULL);
v___x_329_ = lean_usize_shift_right(v_x_317_, v___x_328_);
v_x_316_ = v_node_327_;
v_x_317_ = v___x_329_;
goto _start;
}
default: 
{
uint8_t v___x_331_; 
v___x_331_ = 0;
return v___x_331_;
}
}
}
else
{
lean_object* v_ks_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v_ks_332_ = lean_ctor_get(v_x_316_, 0);
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_ks_332_, v___x_333_, v_x_318_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___boxed(lean_object* v_x_335_, lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
size_t v_x_837__boxed_338_; uint8_t v_res_339_; lean_object* v_r_340_; 
v_x_837__boxed_338_ = lean_unbox_usize(v_x_336_);
lean_dec(v_x_336_);
v_res_339_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_335_, v_x_837__boxed_338_, v_x_337_);
lean_dec_ref(v_x_337_);
lean_dec_ref(v_x_335_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
uint64_t v___x_343_; size_t v___x_344_; uint8_t v___x_345_; 
v___x_343_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_342_);
v___x_344_ = lean_uint64_to_usize(v___x_343_);
v___x_345_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_341_, v___x_344_, v_x_342_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg___boxed(lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
uint8_t v_res_348_; lean_object* v_r_349_; 
v_res_348_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_346_, v_x_347_);
lean_dec_ref(v_x_347_);
lean_dec_ref(v_x_346_);
v_r_349_ = lean_box(v_res_348_);
return v_r_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(lean_object* v_e_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_351_, v_a_352_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_365_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_365_ == 0)
{
v___x_357_ = v___x_354_;
v_isShared_358_ = v_isSharedCheck_365_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_365_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v_varMap_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v_varMap_359_ = lean_ctor_get(v_a_355_, 1);
lean_inc_ref(v_varMap_359_);
lean_dec(v_a_355_);
v___x_360_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_varMap_359_, v_e_350_);
lean_dec_ref(v_varMap_359_);
v___x_361_ = lean_box(v___x_360_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_361_);
v___x_363_ = v___x_357_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
v_a_366_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_354_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_354_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg___boxed(lean_object* v_e_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_374_, v_a_375_, v_a_376_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_e_374_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar(lean_object* v_e_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_379_, v_a_380_, v_a_388_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___boxed(lean_object* v_e_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar(v_e_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_e_392_);
return v_res_404_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(lean_object* v_00_u03b2_405_, lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
uint8_t v___x_408_; 
v___x_408_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_406_, v_x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___boxed(lean_object* v_00_u03b2_409_, lean_object* v_x_410_, lean_object* v_x_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(v_00_u03b2_409_, v_x_410_, v_x_411_);
lean_dec_ref(v_x_411_);
lean_dec_ref(v_x_410_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(lean_object* v_00_u03b2_414_, lean_object* v_x_415_, size_t v_x_416_, lean_object* v_x_417_){
_start:
{
uint8_t v___x_418_; 
v___x_418_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_415_, v_x_416_, v_x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_419_, lean_object* v_x_420_, lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
size_t v_x_944__boxed_423_; uint8_t v_res_424_; lean_object* v_r_425_; 
v_x_944__boxed_423_ = lean_unbox_usize(v_x_421_);
lean_dec(v_x_421_);
v_res_424_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(v_00_u03b2_419_, v_x_420_, v_x_944__boxed_423_, v_x_422_);
lean_dec_ref(v_x_422_);
lean_dec_ref(v_x_420_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_426_, lean_object* v_keys_427_, lean_object* v_vals_428_, lean_object* v_heq_429_, lean_object* v_i_430_, lean_object* v_k_431_){
_start:
{
uint8_t v___x_432_; 
v___x_432_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_427_, v_i_430_, v_k_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_433_, lean_object* v_keys_434_, lean_object* v_vals_435_, lean_object* v_heq_436_, lean_object* v_i_437_, lean_object* v_k_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(v_00_u03b2_433_, v_keys_434_, v_vals_435_, v_heq_436_, v_i_437_, v_k_438_);
lean_dec_ref(v_k_438_);
lean_dec_ref(v_vals_435_);
lean_dec_ref(v_keys_434_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(lean_object* v_e_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_441_, v_a_442_, v_a_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg___boxed(lean_object* v_e_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(v_e_446_, v_a_447_, v_a_448_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_e_446_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(lean_object* v_e_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_451_, v_a_452_, v_a_460_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___boxed(lean_object* v_e_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(v_e_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_e_464_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(lean_object* v_x_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_478_, v_a_479_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_504_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_504_ == 0)
{
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_504_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_504_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___y_487_; lean_object* v_elimEqs_498_; lean_object* v_size_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_elimEqs_498_ = lean_ctor_get(v_a_482_, 10);
lean_inc_ref(v_elimEqs_498_);
lean_dec(v_a_482_);
v_size_499_ = lean_ctor_get(v_elimEqs_498_, 2);
v___x_500_ = lean_box(0);
v___x_501_ = lean_nat_dec_lt(v_x_477_, v_size_499_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
lean_dec_ref(v_elimEqs_498_);
v___x_502_ = l_outOfBounds___redArg(v___x_500_);
v___y_487_ = v___x_502_;
goto v___jp_486_;
}
else
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_PersistentArray_get_x21___redArg(v___x_500_, v_elimEqs_498_, v_x_477_);
lean_dec_ref(v_elimEqs_498_);
v___y_487_ = v___x_503_;
goto v___jp_486_;
}
v___jp_486_:
{
if (lean_obj_tag(v___y_487_) == 0)
{
uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_488_ = 0;
v___x_489_ = lean_box(v___x_488_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_489_);
v___x_491_ = v___x_484_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
else
{
uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
lean_dec_ref_known(v___y_487_, 1);
v___x_493_ = 1;
v___x_494_ = lean_box(v___x_493_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_494_);
v___x_496_ = v___x_484_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
v_a_505_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_481_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_481_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg___boxed(lean_object* v_x_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_513_, v_a_514_, v_a_515_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec(v_x_513_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated(lean_object* v_x_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_518_, v_a_519_, v_a_527_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___boxed(lean_object* v_x_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated(v_x_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec(v_a_532_);
lean_dec(v_x_531_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_assert___boxed(lean_object* v_c_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_00___x40___internal___hyg_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = lean_grind_cutsat_assert_eq(v_c_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(lean_object* v_x_569_, lean_object* v_s_570_){
_start:
{
lean_object* v_vars_571_; lean_object* v_varMap_572_; lean_object* v_vars_x27_573_; lean_object* v_varMap_x27_574_; lean_object* v_natToIntMap_575_; lean_object* v_natDef_576_; lean_object* v_dvds_577_; lean_object* v_lowers_578_; lean_object* v_uppers_579_; lean_object* v_diseqs_580_; lean_object* v_elimEqs_581_; lean_object* v_elimStack_582_; lean_object* v_occurs_583_; lean_object* v_assignment_584_; lean_object* v_nextCnstrId_585_; uint8_t v_caseSplits_586_; lean_object* v_conflict_x3f_587_; lean_object* v_diseqSplits_588_; lean_object* v_divMod_589_; lean_object* v_toIntIds_590_; lean_object* v_toIntInfos_591_; lean_object* v_toIntTermMap_592_; lean_object* v_toIntVarMap_593_; uint8_t v_usedCommRing_594_; lean_object* v_nonlinearOccs_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_603_; 
v_vars_571_ = lean_ctor_get(v_s_570_, 0);
v_varMap_572_ = lean_ctor_get(v_s_570_, 1);
v_vars_x27_573_ = lean_ctor_get(v_s_570_, 2);
v_varMap_x27_574_ = lean_ctor_get(v_s_570_, 3);
v_natToIntMap_575_ = lean_ctor_get(v_s_570_, 4);
v_natDef_576_ = lean_ctor_get(v_s_570_, 5);
v_dvds_577_ = lean_ctor_get(v_s_570_, 6);
v_lowers_578_ = lean_ctor_get(v_s_570_, 7);
v_uppers_579_ = lean_ctor_get(v_s_570_, 8);
v_diseqs_580_ = lean_ctor_get(v_s_570_, 9);
v_elimEqs_581_ = lean_ctor_get(v_s_570_, 10);
v_elimStack_582_ = lean_ctor_get(v_s_570_, 11);
v_occurs_583_ = lean_ctor_get(v_s_570_, 12);
v_assignment_584_ = lean_ctor_get(v_s_570_, 13);
v_nextCnstrId_585_ = lean_ctor_get(v_s_570_, 14);
v_caseSplits_586_ = lean_ctor_get_uint8(v_s_570_, sizeof(void*)*23);
v_conflict_x3f_587_ = lean_ctor_get(v_s_570_, 15);
v_diseqSplits_588_ = lean_ctor_get(v_s_570_, 16);
v_divMod_589_ = lean_ctor_get(v_s_570_, 17);
v_toIntIds_590_ = lean_ctor_get(v_s_570_, 18);
v_toIntInfos_591_ = lean_ctor_get(v_s_570_, 19);
v_toIntTermMap_592_ = lean_ctor_get(v_s_570_, 20);
v_toIntVarMap_593_ = lean_ctor_get(v_s_570_, 21);
v_usedCommRing_594_ = lean_ctor_get_uint8(v_s_570_, sizeof(void*)*23 + 1);
v_nonlinearOccs_595_ = lean_ctor_get(v_s_570_, 22);
v_isSharedCheck_603_ = !lean_is_exclusive(v_s_570_);
if (v_isSharedCheck_603_ == 0)
{
v___x_597_ = v_s_570_;
v_isShared_598_ = v_isSharedCheck_603_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_nonlinearOccs_595_);
lean_inc(v_toIntVarMap_593_);
lean_inc(v_toIntTermMap_592_);
lean_inc(v_toIntInfos_591_);
lean_inc(v_toIntIds_590_);
lean_inc(v_divMod_589_);
lean_inc(v_diseqSplits_588_);
lean_inc(v_conflict_x3f_587_);
lean_inc(v_nextCnstrId_585_);
lean_inc(v_assignment_584_);
lean_inc(v_occurs_583_);
lean_inc(v_elimStack_582_);
lean_inc(v_elimEqs_581_);
lean_inc(v_diseqs_580_);
lean_inc(v_uppers_579_);
lean_inc(v_lowers_578_);
lean_inc(v_dvds_577_);
lean_inc(v_natDef_576_);
lean_inc(v_natToIntMap_575_);
lean_inc(v_varMap_x27_574_);
lean_inc(v_vars_x27_573_);
lean_inc(v_varMap_572_);
lean_inc(v_vars_571_);
lean_dec(v_s_570_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_603_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_599_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_584_, v_x_569_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 13, v___x_599_);
v___x_601_ = v___x_597_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_vars_571_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_varMap_572_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v_vars_x27_573_);
lean_ctor_set(v_reuseFailAlloc_602_, 3, v_varMap_x27_574_);
lean_ctor_set(v_reuseFailAlloc_602_, 4, v_natToIntMap_575_);
lean_ctor_set(v_reuseFailAlloc_602_, 5, v_natDef_576_);
lean_ctor_set(v_reuseFailAlloc_602_, 6, v_dvds_577_);
lean_ctor_set(v_reuseFailAlloc_602_, 7, v_lowers_578_);
lean_ctor_set(v_reuseFailAlloc_602_, 8, v_uppers_579_);
lean_ctor_set(v_reuseFailAlloc_602_, 9, v_diseqs_580_);
lean_ctor_set(v_reuseFailAlloc_602_, 10, v_elimEqs_581_);
lean_ctor_set(v_reuseFailAlloc_602_, 11, v_elimStack_582_);
lean_ctor_set(v_reuseFailAlloc_602_, 12, v_occurs_583_);
lean_ctor_set(v_reuseFailAlloc_602_, 13, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_602_, 14, v_nextCnstrId_585_);
lean_ctor_set(v_reuseFailAlloc_602_, 15, v_conflict_x3f_587_);
lean_ctor_set(v_reuseFailAlloc_602_, 16, v_diseqSplits_588_);
lean_ctor_set(v_reuseFailAlloc_602_, 17, v_divMod_589_);
lean_ctor_set(v_reuseFailAlloc_602_, 18, v_toIntIds_590_);
lean_ctor_set(v_reuseFailAlloc_602_, 19, v_toIntInfos_591_);
lean_ctor_set(v_reuseFailAlloc_602_, 20, v_toIntTermMap_592_);
lean_ctor_set(v_reuseFailAlloc_602_, 21, v_toIntVarMap_593_);
lean_ctor_set(v_reuseFailAlloc_602_, 22, v_nonlinearOccs_595_);
lean_ctor_set_uint8(v_reuseFailAlloc_602_, sizeof(void*)*23, v_caseSplits_586_);
lean_ctor_set_uint8(v_reuseFailAlloc_602_, sizeof(void*)*23 + 1, v_usedCommRing_594_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_x_604_, lean_object* v_s_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(v_x_604_, v_s_605_);
lean_dec(v_x_604_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object* v_x_607_, lean_object* v_a_608_){
_start:
{
lean_object* v___f_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___f_610_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_610_, 0, v_x_607_);
v___x_611_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_612_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_611_, v___f_610_, v_a_608_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___boxed(lean_object* v_x_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_613_, v_a_614_);
lean_dec(v_a_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(lean_object* v_x_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_617_, v_a_618_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___boxed(lean_object* v_x_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(v_x_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec(v_a_631_);
return v_res_642_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__0));
v___x_645_ = l_Lean_stringToMessageData(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = lean_nat_to_int(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3));
v___x_650_ = l_Lean_stringToMessageData(v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(lean_object* v_r_651_, lean_object* v_p_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
if (lean_obj_tag(v_p_652_) == 0)
{
lean_object* v_k_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_674_; 
v_k_656_ = lean_ctor_get(v_p_652_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v_p_652_);
if (v_isSharedCheck_674_ == 0)
{
v___x_658_ = v_p_652_;
v_isShared_659_ = v_isSharedCheck_674_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_k_656_);
lean_dec(v_p_652_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_674_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_661_ = lean_int_dec_eq(v_k_656_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_662_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1);
v___x_663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_663_, 0, v_r_651_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = l_Int_repr(v_k_656_);
lean_dec(v_k_656_);
if (v_isShared_659_ == 0)
{
lean_ctor_set_tag(v___x_658_, 3);
lean_ctor_set(v___x_658_, 0, v___x_664_);
v___x_666_ = v___x_658_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_670_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = l_Lean_MessageData_ofFormat(v___x_666_);
v___x_668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_663_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
else
{
lean_object* v___x_672_; 
lean_dec(v_k_656_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v_r_651_);
v___x_672_ = v___x_658_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_r_651_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_object* v_k_675_; lean_object* v_v_676_; lean_object* v_p_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_k_675_ = lean_ctor_get(v_p_652_, 0);
lean_inc(v_k_675_);
v_v_676_ = lean_ctor_get(v_p_652_, 1);
lean_inc(v_v_676_);
v_p_677_ = lean_ctor_get(v_p_652_, 2);
lean_inc_ref(v_p_677_);
lean_dec_ref_known(v_p_652_, 3);
v___x_678_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2);
v___x_679_ = lean_int_dec_eq(v_k_675_, v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_676_, v_a_653_, v_a_654_);
lean_dec(v_v_676_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v___x_680_, 1);
v___x_682_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1);
v___x_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_683_, 0, v_r_651_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = l_Int_repr(v_k_675_);
lean_dec(v_k_675_);
v___x_685_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
v___x_686_ = l_Lean_MessageData_ofFormat(v___x_685_);
v___x_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_683_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4);
v___x_689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_681_);
v___x_691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_689_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v_r_651_ = v___x_691_;
v_p_652_ = v_p_677_;
goto _start;
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec_ref(v_p_677_);
lean_dec(v_k_675_);
lean_dec_ref(v_r_651_);
v_a_693_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_680_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_680_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
else
{
lean_object* v___x_701_; 
lean_dec(v_k_675_);
v___x_701_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_676_, v_a_653_, v_a_654_);
lean_dec(v_v_676_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
v___x_703_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1);
v___x_704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_704_, 0, v_r_651_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_702_);
v___x_706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_704_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v_r_651_ = v___x_706_;
v_p_652_ = v_p_677_;
goto _start;
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref(v_p_677_);
lean_dec_ref(v_r_651_);
v_a_708_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_701_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_701_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___boxed(lean_object* v_r_716_, lean_object* v_p_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(v_r_716_, v_p_717_, v_a_718_, v_a_719_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go(lean_object* v_r_722_, lean_object* v_p_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(v_r_722_, v_p_723_, v_a_724_, v_a_732_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___boxed(lean_object* v_r_736_, lean_object* v_p_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go(v_r_736_, v_p_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec(v_a_738_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_pp___redArg(lean_object* v_p_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
if (lean_obj_tag(v_p_750_) == 0)
{
lean_object* v_k_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_764_; 
v_k_754_ = lean_ctor_get(v_p_750_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v_p_750_);
if (v_isSharedCheck_764_ == 0)
{
v___x_756_ = v_p_750_;
v_isShared_757_ = v_isSharedCheck_764_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_k_754_);
lean_dec(v_p_750_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_764_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = l_Int_repr(v_k_754_);
lean_dec(v_k_754_);
if (v_isShared_757_ == 0)
{
lean_ctor_set_tag(v___x_756_, 3);
lean_ctor_set(v___x_756_, 0, v___x_758_);
v___x_760_ = v___x_756_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_763_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = l_Lean_MessageData_ofFormat(v___x_760_);
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
return v___x_762_;
}
}
}
else
{
lean_object* v_k_765_; lean_object* v_v_766_; lean_object* v_p_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v_k_765_ = lean_ctor_get(v_p_750_, 0);
lean_inc(v_k_765_);
v_v_766_ = lean_ctor_get(v_p_750_, 1);
lean_inc(v_v_766_);
v_p_767_ = lean_ctor_get(v_p_750_, 2);
lean_inc_ref(v_p_767_);
lean_dec_ref_known(v_p_750_, 3);
v___x_768_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2);
v___x_769_ = lean_int_dec_eq(v_k_765_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_766_, v_a_751_, v_a_752_);
lean_dec(v_v_766_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v___x_770_, 1);
v___x_772_ = l_Int_repr(v_k_765_);
lean_dec(v_k_765_);
v___x_773_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
v___x_774_ = l_Lean_MessageData_ofFormat(v___x_773_);
v___x_775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4);
v___x_776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_771_);
v___x_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(v___x_778_, v_p_767_, v_a_751_, v_a_752_);
return v___x_779_;
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec_ref(v_p_767_);
lean_dec(v_k_765_);
v_a_780_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_770_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_770_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_object* v___x_788_; 
lean_dec(v_k_765_);
v___x_788_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_766_, v_a_751_, v_a_752_);
lean_dec(v_v_766_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v___x_790_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_789_);
v___x_791_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(v___x_790_, v_p_767_, v_a_751_, v_a_752_);
return v___x_791_;
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec_ref(v_p_767_);
v_a_792_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_788_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_788_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_pp___redArg___boxed(lean_object* v_p_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Int_Linear_Poly_pp___redArg(v_p_800_, v_a_801_, v_a_802_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_pp(lean_object* v_p_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Int_Linear_Poly_pp___redArg(v_p_805_, v_a_806_, v_a_814_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_pp___boxed(lean_object* v_p_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Int_Linear_Poly_pp(v_p_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec(v_a_819_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0(lean_object* v_a_831_, lean_object* v___x_832_, lean_object* v_x_833_){
_start:
{
lean_object* v_size_834_; uint8_t v___x_835_; 
v_size_834_ = lean_ctor_get(v_a_831_, 2);
v___x_835_ = lean_nat_dec_lt(v_x_833_, v_size_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
v___x_836_ = l_outOfBounds___redArg(v___x_832_);
return v___x_836_;
}
else
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_PersistentArray_get_x21___redArg(v___x_832_, v_a_831_, v_x_833_);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed(lean_object* v_a_838_, lean_object* v___x_839_, lean_object* v_x_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0(v_a_838_, v___x_839_, v_x_840_);
lean_dec(v_x_840_);
lean_dec_ref(v___x_839_);
lean_dec_ref(v_a_838_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___redArg(lean_object* v_p_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_848_; lean_object* v___f_849_; lean_object* v___x_850_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
v___x_848_ = l_Lean_instInhabitedExpr;
v___f_849_ = lean_alloc_closure((void*)(l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_849_, 0, v_a_847_);
lean_closure_set(v___f_849_, 1, v___x_848_);
v___x_850_ = l_Int_Linear_Poly_denoteExpr___redArg(v___f_849_, v_p_842_);
return v___x_850_;
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec_ref(v_p_842_);
v_a_851_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_846_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_846_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___redArg___boxed(lean_object* v_p_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_859_, v_a_860_, v_a_861_);
lean_dec_ref(v_a_861_);
lean_dec(v_a_860_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27(lean_object* v_p_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_864_, v_a_865_, v_a_873_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___boxed(lean_object* v_p_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Int_Linear_Poly_denoteExpr_x27(v_p_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec(v_a_878_);
return v_res_889_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object* v_c_890_){
_start:
{
lean_object* v_p_891_; 
v_p_891_ = lean_ctor_get(v_c_890_, 1);
if (lean_obj_tag(v_p_891_) == 0)
{
lean_object* v_d_892_; lean_object* v_k_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_d_892_ = lean_ctor_get(v_c_890_, 0);
v_k_893_ = lean_ctor_get(v_p_891_, 0);
v___x_894_ = lean_int_emod(v_k_893_, v_d_892_);
v___x_895_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_896_ = lean_int_dec_eq(v___x_894_, v___x_895_);
lean_dec(v___x_894_);
return v___x_896_;
}
else
{
lean_object* v_d_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v_d_897_ = lean_ctor_get(v_c_890_, 0);
v___x_898_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2);
v___x_899_ = lean_int_dec_eq(v_d_897_, v___x_898_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial___boxed(lean_object* v_c_900_){
_start:
{
uint8_t v_res_901_; lean_object* v_r_902_; 
v_res_901_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_c_900_);
lean_dec_ref(v_c_900_);
v_r_902_ = lean_box(v_res_901_);
return v_r_902_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0));
v___x_905_ = l_Lean_stringToMessageData(v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object* v_c_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_d_910_; lean_object* v_p_911_; lean_object* v___x_912_; 
v_d_910_ = lean_ctor_get(v_c_906_, 0);
lean_inc(v_d_910_);
v_p_911_ = lean_ctor_get(v_c_906_, 1);
lean_inc_ref(v_p_911_);
lean_dec_ref(v_c_906_);
v___x_912_ = l_Int_Linear_Poly_pp___redArg(v_p_911_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_926_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_926_ == 0)
{
v___x_915_ = v___x_912_;
v_isShared_916_ = v_isSharedCheck_926_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_926_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_917_ = l_Int_repr(v_d_910_);
lean_dec(v_d_910_);
v___x_918_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
v___x_919_ = l_Lean_MessageData_ofFormat(v___x_918_);
v___x_920_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1);
v___x_921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v_a_913_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_922_);
v___x_924_ = v___x_915_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
else
{
lean_dec(v_d_910_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___boxed(lean_object* v_c_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_927_, v_a_928_, v_a_929_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(lean_object* v_c_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_932_, v_a_933_, v_a_941_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___boxed(lean_object* v_c_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(v_c_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec(v_a_946_);
return v_res_957_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = l_Lean_Level_ofNat(v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = lean_box(0);
v___x_966_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3);
v___x_967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v___x_965_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_968_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4);
v___x_969_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2));
v___x_970_ = l_Lean_Expr_const___override(v___x_969_, v___x_968_);
return v___x_970_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = lean_box(0);
v___x_975_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7));
v___x_976_ = l_Lean_Expr_const___override(v___x_975_, v___x_974_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_981_ = lean_box(0);
v___x_982_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10));
v___x_983_ = l_Lean_Expr_const___override(v___x_982_, v___x_981_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(lean_object* v_c_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_d_988_; lean_object* v_p_989_; lean_object* v___x_990_; 
v_d_988_ = lean_ctor_get(v_c_984_, 0);
lean_inc(v_d_988_);
v_p_989_ = lean_ctor_get(v_c_984_, 1);
lean_inc_ref(v_p_989_);
lean_dec_ref(v_c_984_);
v___x_990_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_989_, v_a_985_, v_a_986_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1012_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_1012_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1012_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___y_996_; lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1002_ = lean_int_dec_le(v___x_1001_, v_d_988_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1003_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5);
v___x_1004_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8);
v___x_1005_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11);
v___x_1006_ = lean_int_neg(v_d_988_);
lean_dec(v_d_988_);
v___x_1007_ = l_Int_toNat(v___x_1006_);
lean_dec(v___x_1006_);
v___x_1008_ = l_Lean_instToExprInt_mkNat(v___x_1007_);
v___x_1009_ = l_Lean_mkApp3(v___x_1003_, v___x_1004_, v___x_1005_, v___x_1008_);
v___y_996_ = v___x_1009_;
goto v___jp_995_;
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = l_Int_toNat(v_d_988_);
lean_dec(v_d_988_);
v___x_1011_ = l_Lean_instToExprInt_mkNat(v___x_1010_);
v___y_996_ = v___x_1011_;
goto v___jp_995_;
}
v___jp_995_:
{
lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_997_ = l_Lean_mkIntDvd(v___y_996_, v_a_991_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_997_);
v___x_999_ = v___x_993_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
else
{
lean_dec(v_d_988_);
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1013_, v_a_1014_, v_a_1015_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(lean_object* v_c_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1018_, v_a_1019_, v_a_1027_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___boxed(lean_object* v_c_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(v_c_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec(v_a_1032_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(lean_object* v_msgData_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___x_1050_; lean_object* v_env_1051_; lean_object* v___x_1052_; lean_object* v_mctx_1053_; lean_object* v_lctx_1054_; lean_object* v_options_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1050_ = lean_st_ref_get(v___y_1048_);
v_env_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc_ref(v_env_1051_);
lean_dec(v___x_1050_);
v___x_1052_ = lean_st_ref_get(v___y_1046_);
v_mctx_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc_ref(v_mctx_1053_);
lean_dec(v___x_1052_);
v_lctx_1054_ = lean_ctor_get(v___y_1045_, 2);
v_options_1055_ = lean_ctor_get(v___y_1047_, 2);
lean_inc_ref(v_options_1055_);
lean_inc_ref(v_lctx_1054_);
v___x_1056_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1056_, 0, v_env_1051_);
lean_ctor_set(v___x_1056_, 1, v_mctx_1053_);
lean_ctor_set(v___x_1056_, 2, v_lctx_1054_);
lean_ctor_set(v___x_1056_, 3, v_options_1055_);
v___x_1057_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v_msgData_1044_);
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object* v_msgData_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msgData_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(lean_object* v_msg_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_ref_1072_; lean_object* v___x_1073_; lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1082_; 
v_ref_1072_ = lean_ctor_get(v___y_1069_, 5);
v___x_1073_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msg_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
lean_inc(v_ref_1072_);
v___x_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1078_, 0, v_ref_1072_);
lean_ctor_set(v___x_1078_, 1, v_a_1074_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set_tag(v___x_1076_, 1);
lean_ctor_set(v___x_1076_, 0, v___x_1078_);
v___x_1080_ = v___x_1076_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg___boxed(lean_object* v_msg_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
return v_res_1089_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0));
v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2));
v___x_1095_ = l_Lean_stringToMessageData(v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object* v_c_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1096_, v_a_1097_, v_a_1105_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
lean_dec_ref_known(v___x_1108_, 1);
v___x_1110_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1111_ = l_Lean_indentD(v_a_1109_);
v___x_1112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3);
v___x_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1114_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
return v___x_1115_;
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v_a_1116_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1108_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1108_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec(v_a_1125_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(lean_object* v_00_u03b1_1137_, lean_object* v_c_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1151_, lean_object* v_c_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(v_00_u03b1_1151_, v_c_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec(v_a_1153_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(lean_object* v_00_u03b1_1165_, lean_object* v_msg_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1166_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___boxed(lean_object* v_00_u03b1_1179_, lean_object* v_msg_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(v_00_u03b1_1179_, v_msg_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec(v___y_1181_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial_spec__0(lean_object* v_a_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_nat_to_int(v_a_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(lean_object* v_c_1195_){
_start:
{
lean_object* v_p_1196_; 
v_p_1196_ = lean_ctor_get(v_c_1195_, 0);
if (lean_obj_tag(v_p_1196_) == 0)
{
lean_object* v_k_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v_k_1197_ = lean_ctor_get(v_p_1196_, 0);
v___x_1198_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1199_ = lean_int_dec_eq(v_k_1197_, v___x_1198_);
if (v___x_1199_ == 0)
{
uint8_t v___x_1200_; 
v___x_1200_ = 1;
return v___x_1200_;
}
else
{
uint8_t v___x_1201_; 
v___x_1201_ = 0;
return v___x_1201_;
}
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1202_ = l_Int_Linear_Poly_getConst(v_p_1196_);
v___x_1203_ = l_Int_Linear_Poly_gcdCoeffs_x27(v_p_1196_);
v___x_1204_ = lean_nat_to_int(v___x_1203_);
v___x_1205_ = lean_int_emod(v___x_1202_, v___x_1204_);
lean_dec(v___x_1204_);
lean_dec(v___x_1202_);
v___x_1206_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1207_ = lean_int_dec_eq(v___x_1205_, v___x_1206_);
lean_dec(v___x_1205_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial___boxed(lean_object* v_c_1210_){
_start:
{
uint8_t v_res_1211_; lean_object* v_r_1212_; 
v_res_1211_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(v_c_1210_);
lean_dec_ref(v_c_1210_);
v_r_1212_ = lean_box(v_res_1211_);
return v_r_1212_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0));
v___x_1215_ = l_Lean_stringToMessageData(v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(lean_object* v_c_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v_p_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1237_; 
v_p_1220_ = lean_ctor_get(v_c_1216_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_c_1216_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; 
v_unused_1238_ = lean_ctor_get(v_c_1216_, 1);
lean_dec(v_unused_1238_);
v___x_1222_ = v_c_1216_;
v_isShared_1223_ = v_isSharedCheck_1237_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_p_1220_);
lean_dec(v_c_1216_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1237_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Int_Linear_Poly_pp___redArg(v_p_1220_, v_a_1217_, v_a_1218_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1236_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1236_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1236_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1229_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1);
if (v_isShared_1223_ == 0)
{
lean_ctor_set_tag(v___x_1222_, 7);
lean_ctor_set(v___x_1222_, 1, v___x_1229_);
lean_ctor_set(v___x_1222_, 0, v_a_1225_);
v___x_1231_ = v___x_1222_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1225_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1233_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1231_);
v___x_1233_ = v___x_1227_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
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
else
{
lean_del_object(v___x_1222_);
return v___x_1224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___boxed(lean_object* v_c_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1239_, v_a_1240_, v_a_1241_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(lean_object* v_c_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1244_, v_a_1245_, v_a_1253_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___boxed(lean_object* v_c_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(v_c_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec(v_a_1258_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(lean_object* v_c_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1270_, v_a_1271_, v_a_1274_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1277_, 1);
v___x_1279_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1280_ = l_Lean_indentD(v_a_1278_);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1281_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
return v___x_1282_;
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
v_a_1283_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1277_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1277_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
lean_dec(v_a_1292_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(lean_object* v_00_u03b1_1299_, lean_object* v_c_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1300_, v_a_1301_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1313_, lean_object* v_c_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(v_00_u03b1_1313_, v_c_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec(v_a_1315_);
return v_res_1326_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1328_ = l_Lean_mkIntLit(v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(lean_object* v_c_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_p_1333_; lean_object* v___x_1334_; 
v_p_1333_ = lean_ctor_get(v_c_1329_, 0);
lean_inc_ref(v_p_1333_);
lean_dec_ref(v_c_1329_);
v___x_1334_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_1333_, v_a_1330_, v_a_1331_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1345_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1345_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1345_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1339_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1340_ = l_Lean_mkIntEq(v_a_1335_, v___x_1339_);
v___x_1341_ = l_Lean_mkNot(v___x_1340_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1341_);
v___x_1343_ = v___x_1337_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
else
{
return v___x_1334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1346_, v_a_1347_, v_a_1348_);
lean_dec_ref(v_a_1348_);
lean_dec(v_a_1347_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(lean_object* v_c_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1351_, v_a_1352_, v_a_1360_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___boxed(lean_object* v_c_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(v_c_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec(v_a_1365_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert___boxed(lean_object* v_c_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_00___x40___internal___hyg_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = lean_grind_cutsat_assert_le(v_c_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_);
return v_res_1401_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(lean_object* v_c_1402_){
_start:
{
lean_object* v_p_1403_; 
v_p_1403_ = lean_ctor_get(v_c_1402_, 0);
if (lean_obj_tag(v_p_1403_) == 0)
{
lean_object* v_k_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v_k_1404_ = lean_ctor_get(v_p_1403_, 0);
v___x_1405_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1406_ = lean_int_dec_le(v_k_1404_, v___x_1405_);
return v___x_1406_;
}
else
{
uint8_t v___x_1407_; 
v___x_1407_ = 0;
return v___x_1407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial___boxed(lean_object* v_c_1408_){
_start:
{
uint8_t v_res_1409_; lean_object* v_r_1410_; 
v_res_1409_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_c_1408_);
lean_dec_ref(v_c_1408_);
v_r_1410_ = lean_box(v_res_1409_);
return v_r_1410_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0));
v___x_1413_ = l_Lean_stringToMessageData(v___x_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(lean_object* v_c_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_p_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1435_; 
v_p_1418_ = lean_ctor_get(v_c_1414_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_c_1414_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; 
v_unused_1436_ = lean_ctor_get(v_c_1414_, 1);
lean_dec(v_unused_1436_);
v___x_1420_ = v_c_1414_;
v_isShared_1421_ = v_isSharedCheck_1435_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_p_1418_);
lean_dec(v_c_1414_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1435_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Int_Linear_Poly_pp___redArg(v_p_1418_, v_a_1415_, v_a_1416_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1434_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1434_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1434_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1427_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1);
if (v_isShared_1421_ == 0)
{
lean_ctor_set_tag(v___x_1420_, 7);
lean_ctor_set(v___x_1420_, 1, v___x_1427_);
lean_ctor_set(v___x_1420_, 0, v_a_1423_);
v___x_1429_ = v___x_1420_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1423_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1431_; 
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1429_);
v___x_1431_ = v___x_1425_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
else
{
lean_del_object(v___x_1420_);
return v___x_1422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___boxed(lean_object* v_c_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1437_, v_a_1438_, v_a_1439_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(lean_object* v_c_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1442_, v_a_1443_, v_a_1451_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___boxed(lean_object* v_c_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(v_c_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec(v_a_1457_);
lean_dec(v_a_1456_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(lean_object* v_c_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v_p_1472_; lean_object* v___x_1473_; 
v_p_1472_ = lean_ctor_get(v_c_1468_, 0);
lean_inc_ref(v_p_1472_);
lean_dec_ref(v_c_1468_);
v___x_1473_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_1472_, v_a_1469_, v_a_1470_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1483_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1483_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1483_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1478_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1479_ = l_Lean_mkIntLE(v_a_1474_, v___x_1478_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v___x_1479_);
v___x_1481_ = v___x_1476_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
else
{
return v___x_1473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1484_, v_a_1485_, v_a_1486_);
lean_dec_ref(v_a_1486_);
lean_dec(v_a_1485_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(lean_object* v_c_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1489_, v_a_1490_, v_a_1498_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___boxed(lean_object* v_c_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(v_c_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
lean_dec(v_a_1512_);
lean_dec_ref(v_a_1511_);
lean_dec(v_a_1510_);
lean_dec_ref(v_a_1509_);
lean_dec(v_a_1508_);
lean_dec_ref(v_a_1507_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
lean_dec(v_a_1504_);
lean_dec(v_a_1503_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(lean_object* v_c_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1515_, v_a_1516_, v_a_1519_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___x_1524_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1525_ = l_Lean_indentD(v_a_1523_);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1526_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
return v___x_1527_;
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
v_a_1528_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1522_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1522_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec(v_a_1537_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(lean_object* v_00_u03b1_1544_, lean_object* v_c_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1545_, v_a_1546_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1558_, lean_object* v_c_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(v_00_u03b1_1558_, v_c_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec(v_a_1565_);
lean_dec_ref(v_a_1564_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
lean_dec(v_a_1560_);
return v_res_1571_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(lean_object* v_c_1572_){
_start:
{
lean_object* v_p_1573_; 
v_p_1573_ = lean_ctor_get(v_c_1572_, 0);
if (lean_obj_tag(v_p_1573_) == 0)
{
lean_object* v_k_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v_k_1574_ = lean_ctor_get(v_p_1573_, 0);
v___x_1575_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1576_ = lean_int_dec_eq(v_k_1574_, v___x_1575_);
return v___x_1576_;
}
else
{
uint8_t v___x_1577_; 
v___x_1577_ = 0;
return v___x_1577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial___boxed(lean_object* v_c_1578_){
_start:
{
uint8_t v_res_1579_; lean_object* v_r_1580_; 
v_res_1579_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(v_c_1578_);
lean_dec_ref(v_c_1578_);
v_r_1580_ = lean_box(v_res_1579_);
return v_r_1580_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0));
v___x_1583_ = l_Lean_stringToMessageData(v___x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object* v_c_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v_p_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1605_; 
v_p_1588_ = lean_ctor_get(v_c_1584_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_c_1584_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; 
v_unused_1606_ = lean_ctor_get(v_c_1584_, 1);
lean_dec(v_unused_1606_);
v___x_1590_ = v_c_1584_;
v_isShared_1591_ = v_isSharedCheck_1605_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_p_1588_);
lean_dec(v_c_1584_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1605_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Int_Linear_Poly_pp___redArg(v_p_1588_, v_a_1585_, v_a_1586_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1604_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1604_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1604_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1597_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1);
if (v_isShared_1591_ == 0)
{
lean_ctor_set_tag(v___x_1590_, 7);
lean_ctor_set(v___x_1590_, 1, v___x_1597_);
lean_ctor_set(v___x_1590_, 0, v_a_1593_);
v___x_1599_ = v___x_1590_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1593_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1601_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v___x_1599_);
v___x_1601_ = v___x_1595_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_del_object(v___x_1590_);
return v___x_1592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___boxed(lean_object* v_c_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1607_, v_a_1608_, v_a_1609_);
lean_dec_ref(v_a_1609_);
lean_dec(v_a_1608_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(lean_object* v_c_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1612_, v_a_1613_, v_a_1621_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___boxed(lean_object* v_c_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(v_c_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec(v_a_1626_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(lean_object* v_c_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_p_1642_; lean_object* v___x_1643_; 
v_p_1642_ = lean_ctor_get(v_c_1638_, 0);
lean_inc_ref(v_p_1642_);
lean_dec_ref(v_c_1638_);
v___x_1643_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_1642_, v_a_1639_, v_a_1640_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1653_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1653_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1653_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1648_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1649_ = l_Lean_mkIntEq(v_a_1644_, v___x_1648_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1649_);
v___x_1651_ = v___x_1646_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
else
{
return v___x_1643_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1654_, v_a_1655_, v_a_1656_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(lean_object* v_c_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1659_, v_a_1660_, v_a_1668_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___boxed(lean_object* v_c_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(v_c_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec(v_a_1673_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(lean_object* v_c_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1685_, v_a_1686_, v_a_1689_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1692_, 1);
v___x_1694_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1695_ = l_Lean_indentD(v_a_1693_);
v___x_1696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1696_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_);
return v___x_1697_;
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
v_a_1698_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1692_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1692_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(lean_object* v_00_u03b1_1714_, lean_object* v_c_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_1715_, v_a_1716_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1728_, lean_object* v_c_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(v_00_u03b1_1728_, v_c_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
lean_dec(v_a_1739_);
lean_dec_ref(v_a_1738_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec(v_a_1730_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(lean_object* v_x_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1763_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1763_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1763_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v_occurs_1751_; lean_object* v_size_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v_occurs_1751_ = lean_ctor_get(v_a_1747_, 12);
lean_inc_ref(v_occurs_1751_);
lean_dec(v_a_1747_);
v_size_1752_ = lean_ctor_get(v_occurs_1751_, 2);
v___x_1753_ = lean_box(1);
v___x_1754_ = lean_nat_dec_lt(v_x_1742_, v_size_1752_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
lean_dec_ref(v_occurs_1751_);
v___x_1755_ = l_outOfBounds___redArg(v___x_1753_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1755_);
v___x_1757_ = v___x_1749_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1759_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1753_, v_occurs_1751_, v_x_1742_);
lean_dec_ref(v_occurs_1751_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1759_);
v___x_1761_ = v___x_1749_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
v_a_1764_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1746_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1746_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg___boxed(lean_object* v_x_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_1772_, v_a_1773_, v_a_1774_);
lean_dec_ref(v_a_1774_);
lean_dec(v_a_1773_);
lean_dec(v_x_1772_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(lean_object* v_x_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_1777_, v_a_1778_, v_a_1786_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___boxed(lean_object* v_x_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(v_x_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_);
lean_dec(v_a_1800_);
lean_dec_ref(v_a_1799_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
lean_dec(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec(v_x_1790_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(lean_object* v_k_1803_, lean_object* v_v_1804_, lean_object* v_t_1805_){
_start:
{
if (lean_obj_tag(v_t_1805_) == 0)
{
lean_object* v_size_1806_; lean_object* v_k_1807_; lean_object* v_v_1808_; lean_object* v_l_1809_; lean_object* v_r_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_2091_; 
v_size_1806_ = lean_ctor_get(v_t_1805_, 0);
v_k_1807_ = lean_ctor_get(v_t_1805_, 1);
v_v_1808_ = lean_ctor_get(v_t_1805_, 2);
v_l_1809_ = lean_ctor_get(v_t_1805_, 3);
v_r_1810_ = lean_ctor_get(v_t_1805_, 4);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_t_1805_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_1812_ = v_t_1805_;
v_isShared_1813_ = v_isSharedCheck_2091_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_r_1810_);
lean_inc(v_l_1809_);
lean_inc(v_v_1808_);
lean_inc(v_k_1807_);
lean_inc(v_size_1806_);
lean_dec(v_t_1805_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_2091_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
uint8_t v___x_1814_; 
v___x_1814_ = lean_nat_dec_lt(v_k_1803_, v_k_1807_);
if (v___x_1814_ == 0)
{
uint8_t v___x_1815_; 
v___x_1815_ = lean_nat_dec_eq(v_k_1803_, v_k_1807_);
if (v___x_1815_ == 0)
{
lean_object* v_impl_1816_; lean_object* v___x_1817_; 
lean_dec(v_size_1806_);
v_impl_1816_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_1803_, v_v_1804_, v_r_1810_);
v___x_1817_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1809_) == 0)
{
lean_object* v_size_1818_; lean_object* v_size_1819_; lean_object* v_k_1820_; lean_object* v_v_1821_; lean_object* v_l_1822_; lean_object* v_r_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v_size_1818_ = lean_ctor_get(v_l_1809_, 0);
v_size_1819_ = lean_ctor_get(v_impl_1816_, 0);
lean_inc(v_size_1819_);
v_k_1820_ = lean_ctor_get(v_impl_1816_, 1);
lean_inc(v_k_1820_);
v_v_1821_ = lean_ctor_get(v_impl_1816_, 2);
lean_inc(v_v_1821_);
v_l_1822_ = lean_ctor_get(v_impl_1816_, 3);
lean_inc(v_l_1822_);
v_r_1823_ = lean_ctor_get(v_impl_1816_, 4);
lean_inc(v_r_1823_);
v___x_1824_ = lean_unsigned_to_nat(3u);
v___x_1825_ = lean_nat_mul(v___x_1824_, v_size_1818_);
v___x_1826_ = lean_nat_dec_lt(v___x_1825_, v_size_1819_);
lean_dec(v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1830_; 
lean_dec(v_r_1823_);
lean_dec(v_l_1822_);
lean_dec(v_v_1821_);
lean_dec(v_k_1820_);
v___x_1827_ = lean_nat_add(v___x_1817_, v_size_1818_);
v___x_1828_ = lean_nat_add(v___x_1827_, v_size_1819_);
lean_dec(v_size_1819_);
lean_dec(v___x_1827_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 4, v_impl_1816_);
lean_ctor_set(v___x_1812_, 0, v___x_1828_);
v___x_1830_ = v___x_1812_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_k_1807_);
lean_ctor_set(v_reuseFailAlloc_1831_, 2, v_v_1808_);
lean_ctor_set(v_reuseFailAlloc_1831_, 3, v_l_1809_);
lean_ctor_set(v_reuseFailAlloc_1831_, 4, v_impl_1816_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
else
{
lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1895_; 
v_isSharedCheck_1895_ = !lean_is_exclusive(v_impl_1816_);
if (v_isSharedCheck_1895_ == 0)
{
lean_object* v_unused_1896_; lean_object* v_unused_1897_; lean_object* v_unused_1898_; lean_object* v_unused_1899_; lean_object* v_unused_1900_; 
v_unused_1896_ = lean_ctor_get(v_impl_1816_, 4);
lean_dec(v_unused_1896_);
v_unused_1897_ = lean_ctor_get(v_impl_1816_, 3);
lean_dec(v_unused_1897_);
v_unused_1898_ = lean_ctor_get(v_impl_1816_, 2);
lean_dec(v_unused_1898_);
v_unused_1899_ = lean_ctor_get(v_impl_1816_, 1);
lean_dec(v_unused_1899_);
v_unused_1900_ = lean_ctor_get(v_impl_1816_, 0);
lean_dec(v_unused_1900_);
v___x_1833_ = v_impl_1816_;
v_isShared_1834_ = v_isSharedCheck_1895_;
goto v_resetjp_1832_;
}
else
{
lean_dec(v_impl_1816_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1895_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_size_1835_; lean_object* v_k_1836_; lean_object* v_v_1837_; lean_object* v_l_1838_; lean_object* v_r_1839_; lean_object* v_size_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v_size_1835_ = lean_ctor_get(v_l_1822_, 0);
v_k_1836_ = lean_ctor_get(v_l_1822_, 1);
v_v_1837_ = lean_ctor_get(v_l_1822_, 2);
v_l_1838_ = lean_ctor_get(v_l_1822_, 3);
v_r_1839_ = lean_ctor_get(v_l_1822_, 4);
v_size_1840_ = lean_ctor_get(v_r_1823_, 0);
v___x_1841_ = lean_unsigned_to_nat(2u);
v___x_1842_ = lean_nat_mul(v___x_1841_, v_size_1840_);
v___x_1843_ = lean_nat_dec_lt(v_size_1835_, v___x_1842_);
lean_dec(v___x_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1871_; 
lean_inc(v_r_1839_);
lean_inc(v_l_1838_);
lean_inc(v_v_1837_);
lean_inc(v_k_1836_);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_l_1822_);
if (v_isSharedCheck_1871_ == 0)
{
lean_object* v_unused_1872_; lean_object* v_unused_1873_; lean_object* v_unused_1874_; lean_object* v_unused_1875_; lean_object* v_unused_1876_; 
v_unused_1872_ = lean_ctor_get(v_l_1822_, 4);
lean_dec(v_unused_1872_);
v_unused_1873_ = lean_ctor_get(v_l_1822_, 3);
lean_dec(v_unused_1873_);
v_unused_1874_ = lean_ctor_get(v_l_1822_, 2);
lean_dec(v_unused_1874_);
v_unused_1875_ = lean_ctor_get(v_l_1822_, 1);
lean_dec(v_unused_1875_);
v_unused_1876_ = lean_ctor_get(v_l_1822_, 0);
lean_dec(v_unused_1876_);
v___x_1845_ = v_l_1822_;
v_isShared_1846_ = v_isSharedCheck_1871_;
goto v_resetjp_1844_;
}
else
{
lean_dec(v_l_1822_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1871_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1861_; 
v___x_1847_ = lean_nat_add(v___x_1817_, v_size_1818_);
v___x_1848_ = lean_nat_add(v___x_1847_, v_size_1819_);
lean_dec(v_size_1819_);
if (lean_obj_tag(v_l_1838_) == 0)
{
lean_object* v_size_1869_; 
v_size_1869_ = lean_ctor_get(v_l_1838_, 0);
lean_inc(v_size_1869_);
v___y_1861_ = v_size_1869_;
goto v___jp_1860_;
}
else
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_unsigned_to_nat(0u);
v___y_1861_ = v___x_1870_;
goto v___jp_1860_;
}
v___jp_1849_:
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1853_ = lean_nat_add(v___y_1850_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec(v___y_1850_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 4, v_r_1823_);
lean_ctor_set(v___x_1845_, 3, v_r_1839_);
lean_ctor_set(v___x_1845_, 2, v_v_1821_);
lean_ctor_set(v___x_1845_, 1, v_k_1820_);
lean_ctor_set(v___x_1845_, 0, v___x_1853_);
v___x_1855_ = v___x_1845_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1853_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_k_1820_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_v_1821_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_r_1839_);
lean_ctor_set(v_reuseFailAlloc_1859_, 4, v_r_1823_);
v___x_1855_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1857_; 
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 4, v___x_1855_);
lean_ctor_set(v___x_1833_, 3, v___y_1851_);
lean_ctor_set(v___x_1833_, 2, v_v_1837_);
lean_ctor_set(v___x_1833_, 1, v_k_1836_);
lean_ctor_set(v___x_1833_, 0, v___x_1848_);
v___x_1857_ = v___x_1833_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1848_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_k_1836_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_v_1837_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v___y_1851_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
v___jp_1860_:
{
lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1862_ = lean_nat_add(v___x_1847_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec(v___x_1847_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 4, v_l_1838_);
lean_ctor_set(v___x_1812_, 0, v___x_1862_);
v___x_1864_ = v___x_1812_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1862_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_k_1807_);
lean_ctor_set(v_reuseFailAlloc_1868_, 2, v_v_1808_);
lean_ctor_set(v_reuseFailAlloc_1868_, 3, v_l_1809_);
lean_ctor_set(v_reuseFailAlloc_1868_, 4, v_l_1838_);
v___x_1864_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_nat_add(v___x_1817_, v_size_1840_);
if (lean_obj_tag(v_r_1839_) == 0)
{
lean_object* v_size_1866_; 
v_size_1866_ = lean_ctor_get(v_r_1839_, 0);
lean_inc(v_size_1866_);
v___y_1850_ = v___x_1865_;
v___y_1851_ = v___x_1864_;
v___y_1852_ = v_size_1866_;
goto v___jp_1849_;
}
else
{
lean_object* v___x_1867_; 
v___x_1867_ = lean_unsigned_to_nat(0u);
v___y_1850_ = v___x_1865_;
v___y_1851_ = v___x_1864_;
v___y_1852_ = v___x_1867_;
goto v___jp_1849_;
}
}
}
}
}
else
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1881_; 
lean_del_object(v___x_1812_);
v___x_1877_ = lean_nat_add(v___x_1817_, v_size_1818_);
v___x_1878_ = lean_nat_add(v___x_1877_, v_size_1819_);
lean_dec(v_size_1819_);
v___x_1879_ = lean_nat_add(v___x_1877_, v_size_1835_);
lean_dec(v___x_1877_);
lean_inc_ref(v_l_1809_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 4, v_l_1822_);
lean_ctor_set(v___x_1833_, 3, v_l_1809_);
lean_ctor_set(v___x_1833_, 2, v_v_1808_);
lean_ctor_set(v___x_1833_, 1, v_k_1807_);
lean_ctor_set(v___x_1833_, 0, v___x_1879_);
v___x_1881_ = v___x_1833_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1879_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_k_1807_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_v_1808_);
lean_ctor_set(v_reuseFailAlloc_1894_, 3, v_l_1809_);
lean_ctor_set(v_reuseFailAlloc_1894_, 4, v_l_1822_);
v___x_1881_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
v_isSharedCheck_1888_ = !lean_is_exclusive(v_l_1809_);
if (v_isSharedCheck_1888_ == 0)
{
lean_object* v_unused_1889_; lean_object* v_unused_1890_; lean_object* v_unused_1891_; lean_object* v_unused_1892_; lean_object* v_unused_1893_; 
v_unused_1889_ = lean_ctor_get(v_l_1809_, 4);
lean_dec(v_unused_1889_);
v_unused_1890_ = lean_ctor_get(v_l_1809_, 3);
lean_dec(v_unused_1890_);
v_unused_1891_ = lean_ctor_get(v_l_1809_, 2);
lean_dec(v_unused_1891_);
v_unused_1892_ = lean_ctor_get(v_l_1809_, 1);
lean_dec(v_unused_1892_);
v_unused_1893_ = lean_ctor_get(v_l_1809_, 0);
lean_dec(v_unused_1893_);
v___x_1883_ = v_l_1809_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_dec(v_l_1809_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 4, v_r_1823_);
lean_ctor_set(v___x_1883_, 3, v___x_1881_);
lean_ctor_set(v___x_1883_, 2, v_v_1821_);
lean_ctor_set(v___x_1883_, 1, v_k_1820_);
lean_ctor_set(v___x_1883_, 0, v___x_1878_);
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_k_1820_);
lean_ctor_set(v_reuseFailAlloc_1887_, 2, v_v_1821_);
lean_ctor_set(v_reuseFailAlloc_1887_, 3, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1887_, 4, v_r_1823_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1901_; 
v_l_1901_ = lean_ctor_get(v_impl_1816_, 3);
lean_inc(v_l_1901_);
if (lean_obj_tag(v_l_1901_) == 0)
{
lean_object* v_r_1902_; lean_object* v_k_1903_; lean_object* v_v_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1927_; 
v_r_1902_ = lean_ctor_get(v_impl_1816_, 4);
v_k_1903_ = lean_ctor_get(v_impl_1816_, 1);
v_v_1904_ = lean_ctor_get(v_impl_1816_, 2);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_impl_1816_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; lean_object* v_unused_1929_; 
v_unused_1928_ = lean_ctor_get(v_impl_1816_, 3);
lean_dec(v_unused_1928_);
v_unused_1929_ = lean_ctor_get(v_impl_1816_, 0);
lean_dec(v_unused_1929_);
v___x_1906_ = v_impl_1816_;
v_isShared_1907_ = v_isSharedCheck_1927_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_r_1902_);
lean_inc(v_v_1904_);
lean_inc(v_k_1903_);
lean_dec(v_impl_1816_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1927_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v_k_1908_; lean_object* v_v_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1923_; 
v_k_1908_ = lean_ctor_get(v_l_1901_, 1);
v_v_1909_ = lean_ctor_get(v_l_1901_, 2);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_l_1901_);
if (v_isSharedCheck_1923_ == 0)
{
lean_object* v_unused_1924_; lean_object* v_unused_1925_; lean_object* v_unused_1926_; 
v_unused_1924_ = lean_ctor_get(v_l_1901_, 4);
lean_dec(v_unused_1924_);
v_unused_1925_ = lean_ctor_get(v_l_1901_, 3);
lean_dec(v_unused_1925_);
v_unused_1926_ = lean_ctor_get(v_l_1901_, 0);
lean_dec(v_unused_1926_);
v___x_1911_ = v_l_1901_;
v_isShared_1912_ = v_isSharedCheck_1923_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_v_1909_);
lean_inc(v_k_1908_);
lean_dec(v_l_1901_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1923_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
v___x_1913_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1902_, 2);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 4, v_r_1902_);
lean_ctor_set(v___x_1911_, 3, v_r_1902_);
lean_ctor_set(v___x_1911_, 2, v_v_1808_);
lean_ctor_set(v___x_1911_, 1, v_k_1807_);
lean_ctor_set(v___x_1911_, 0, v___x_1817_);
v___x_1915_ = v___x_1911_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_k_1807_);
lean_ctor_set(v_reuseFailAlloc_1922_, 2, v_v_1808_);
lean_ctor_set(v_reuseFailAlloc_1922_, 3, v_r_1902_);
lean_ctor_set(v_reuseFailAlloc_1922_, 4, v_r_1902_);
v___x_1915_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1917_; 
lean_inc(v_r_1902_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 3, v_r_1902_);
lean_ctor_set(v___x_1906_, 0, v___x_1817_);
v___x_1917_ = v___x_1906_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_k_1903_);
lean_ctor_set(v_reuseFailAlloc_1921_, 2, v_v_1904_);
lean_ctor_set(v_reuseFailAlloc_1921_, 3, v_r_1902_);
lean_ctor_set(v_reuseFailAlloc_1921_, 4, v_r_1902_);
v___x_1917_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
lean_object* v___x_1919_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 4, v___x_1917_);
lean_ctor_set(v___x_1812_, 3, v___x_1915_);
lean_ctor_set(v___x_1812_, 2, v_v_1909_);
lean_ctor_set(v___x_1812_, 1, v_k_1908_);
lean_ctor_set(v___x_1812_, 0, v___x_1913_);
v___x_1919_ = v___x_1812_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_k_1908_);
lean_ctor_set(v_reuseFailAlloc_1920_, 2, v_v_1909_);
lean_ctor_set(v_reuseFailAlloc_1920_, 3, v___x_1915_);
lean_ctor_set(v_reuseFailAlloc_1920_, 4, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
}
else
{
lean_object* v_r_1930_; 
v_r_1930_ = lean_ctor_get(v_impl_1816_, 4);
lean_inc(v_r_1930_);
if (lean_obj_tag(v_r_1930_) == 0)
{
lean_object* v_k_1931_; lean_object* v_v_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1943_; 
v_k_1931_ = lean_ctor_get(v_impl_1816_, 1);
v_v_1932_ = lean_ctor_get(v_impl_1816_, 2);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_impl_1816_);
if (v_isSharedCheck_1943_ == 0)
{
lean_object* v_unused_1944_; lean_object* v_unused_1945_; lean_object* v_unused_1946_; 
v_unused_1944_ = lean_ctor_get(v_impl_1816_, 4);
lean_dec(v_unused_1944_);
v_unused_1945_ = lean_ctor_get(v_impl_1816_, 3);
lean_dec(v_unused_1945_);
v_unused_1946_ = lean_ctor_get(v_impl_1816_, 0);
lean_dec(v_unused_1946_);
v___x_1934_ = v_impl_1816_;
v_isShared_1935_ = v_isSharedCheck_1943_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_v_1932_);
lean_inc(v_k_1931_);
lean_dec(v_impl_1816_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1943_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1936_ = lean_unsigned_to_nat(3u);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 4, v_l_1901_);
lean_ctor_set(v___x_1934_, 2, v_v_1808_);
lean_ctor_set(v___x_1934_, 1, v_k_1807_);
lean_ctor_set(v___x_1934_, 0, v___x_1817_);
v___x_1938_ = v___x_1934_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_k_1807_);
lean_ctor_set(v_reuseFailAlloc_1942_, 2, v_v_1808_);
lean_ctor_set(v_reuseFailAlloc_1942_, 3, v_l_1901_);
lean_ctor_set(v_reuseFailAlloc_1942_, 4, v_l_1901_);
v___x_1938_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
lean_object* v___x_1940_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 4, v_r_1930_);
lean_ctor_set(v___x_1812_, 3, v___x_1938_);
lean_ctor_set(v___x_1812_, 2, v_v_1932_);
lean_ctor_set(v___x_1812_, 1, v_k_1931_);
lean_ctor_set(v___x_1812_, 0, v___x_1936_);
v___x_1940_ = v___x_1812_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1936_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_k_1931_);
lean_ctor_set(v_reuseFailAlloc_1941_, 2, v_v_1932_);
lean_ctor_set(v_reuseFailAlloc_1941_, 3, v___x_1938_);
lean_ctor_set(v_reuseFailAlloc_1941_, 4, v_r_1930_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
else
{
lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1947_ = lean_unsigned_to_nat(2u);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 4, v_impl_1816_);
lean_ctor_set(v___x_1812_, 3, v_r_1930_);
lean_ctor_set(v___x_1812_, 0, v___x_1947_);
v___x_1949_ = v___x_1812_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_k_1807_);
lean_ctor_set(v_reuseFailAlloc_1950_, 2, v_v_1808_);
lean_ctor_set(v_reuseFailAlloc_1950_, 3, v_r_1930_);
lean_ctor_set(v_reuseFailAlloc_1950_, 4, v_impl_1816_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
else
{
lean_object* v___x_1952_; 
lean_dec(v_v_1808_);
lean_dec(v_k_1807_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 2, v_v_1804_);
lean_ctor_set(v___x_1812_, 1, v_k_1803_);
v___x_1952_ = v___x_1812_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_size_1806_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_k_1803_);
lean_ctor_set(v_reuseFailAlloc_1953_, 2, v_v_1804_);
lean_ctor_set(v_reuseFailAlloc_1953_, 3, v_l_1809_);
lean_ctor_set(v_reuseFailAlloc_1953_, 4, v_r_1810_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
else
{
lean_object* v_impl_1954_; lean_object* v___x_1955_; 
lean_dec(v_size_1806_);
v_impl_1954_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_1803_, v_v_1804_, v_l_1809_);
v___x_1955_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1810_) == 0)
{
lean_object* v_size_1956_; lean_object* v_size_1957_; lean_object* v_k_1958_; lean_object* v_v_1959_; lean_object* v_l_1960_; lean_object* v_r_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
v_size_1956_ = lean_ctor_get(v_r_1810_, 0);
v_size_1957_ = lean_ctor_get(v_impl_1954_, 0);
lean_inc(v_size_1957_);
v_k_1958_ = lean_ctor_get(v_impl_1954_, 1);
lean_inc(v_k_1958_);
v_v_1959_ = lean_ctor_get(v_impl_1954_, 2);
lean_inc(v_v_1959_);
v_l_1960_ = lean_ctor_get(v_impl_1954_, 3);
lean_inc(v_l_1960_);
v_r_1961_ = lean_ctor_get(v_impl_1954_, 4);
lean_inc(v_r_1961_);
v___x_1962_ = lean_unsigned_to_nat(3u);
v___x_1963_ = lean_nat_mul(v___x_1962_, v_size_1956_);
v___x_1964_ = lean_nat_dec_lt(v___x_1963_, v_size_1957_);
lean_dec(v___x_1963_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
lean_dec(v_r_1961_);
lean_dec(v_l_1960_);
lean_dec(v_v_1959_);
lean_dec(v_k_1958_);
v___x_1965_ = lean_nat_add(v___x_1955_, v_size_1957_);
lean_dec(v_size_1957_);
v___x_1966_ = lean_nat_add(v___x_1965_, v_size_1956_);
lean_dec(v___x_1965_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 3, v_impl_1954_);
lean_ctor_set(v___x_1812_, 0, v___x_1966_);
v___x_1968_ = v___x_1812_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_k_1807_);
lean_ctor_set(v_reuseFailAlloc_1969_, 2, v_v_1808_);
lean_ctor_set(v_reuseFailAlloc_1969_, 3, v_impl_1954_);
lean_ctor_set(v_reuseFailAlloc_1969_, 4, v_r_1810_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
else
{
lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2035_; 
v_isSharedCheck_2035_ = !lean_is_exclusive(v_impl_1954_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; lean_object* v_unused_2037_; lean_object* v_unused_2038_; lean_object* v_unused_2039_; lean_object* v_unused_2040_; 
v_unused_2036_ = lean_ctor_get(v_impl_1954_, 4);
lean_dec(v_unused_2036_);
v_unused_2037_ = lean_ctor_get(v_impl_1954_, 3);
lean_dec(v_unused_2037_);
v_unused_2038_ = lean_ctor_get(v_impl_1954_, 2);
lean_dec(v_unused_2038_);
v_unused_2039_ = lean_ctor_get(v_impl_1954_, 1);
lean_dec(v_unused_2039_);
v_unused_2040_ = lean_ctor_get(v_impl_1954_, 0);
lean_dec(v_unused_2040_);
v___x_1971_ = v_impl_1954_;
v_isShared_1972_ = v_isSharedCheck_2035_;
goto v_resetjp_1970_;
}
else
{
lean_dec(v_impl_1954_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2035_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v_size_1973_; lean_object* v_size_1974_; lean_object* v_k_1975_; lean_object* v_v_1976_; lean_object* v_l_1977_; lean_object* v_r_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v_size_1973_ = lean_ctor_get(v_l_1960_, 0);
v_size_1974_ = lean_ctor_get(v_r_1961_, 0);
v_k_1975_ = lean_ctor_get(v_r_1961_, 1);
v_v_1976_ = lean_ctor_get(v_r_1961_, 2);
v_l_1977_ = lean_ctor_get(v_r_1961_, 3);
v_r_1978_ = lean_ctor_get(v_r_1961_, 4);
v___x_1979_ = lean_unsigned_to_nat(2u);
v___x_1980_ = lean_nat_mul(v___x_1979_, v_size_1973_);
v___x_1981_ = lean_nat_dec_lt(v_size_1974_, v___x_1980_);
lean_dec(v___x_1980_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2010_; 
lean_inc(v_r_1978_);
lean_inc(v_l_1977_);
lean_inc(v_v_1976_);
lean_inc(v_k_1975_);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_r_1961_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; lean_object* v_unused_2012_; lean_object* v_unused_2013_; lean_object* v_unused_2014_; lean_object* v_unused_2015_; 
v_unused_2011_ = lean_ctor_get(v_r_1961_, 4);
lean_dec(v_unused_2011_);
v_unused_2012_ = lean_ctor_get(v_r_1961_, 3);
lean_dec(v_unused_2012_);
v_unused_2013_ = lean_ctor_get(v_r_1961_, 2);
lean_dec(v_unused_2013_);
v_unused_2014_ = lean_ctor_get(v_r_1961_, 1);
lean_dec(v_unused_2014_);
v_unused_2015_ = lean_ctor_get(v_r_1961_, 0);
lean_dec(v_unused_2015_);
v___x_1983_ = v_r_1961_;
v_isShared_1984_ = v_isSharedCheck_2010_;
goto v_resetjp_1982_;
}
else
{
lean_dec(v_r_1961_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2010_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___x_1998_; lean_object* v___y_2000_; 
v___x_1985_ = lean_nat_add(v___x_1955_, v_size_1957_);
lean_dec(v_size_1957_);
v___x_1986_ = lean_nat_add(v___x_1985_, v_size_1956_);
lean_dec(v___x_1985_);
v___x_1998_ = lean_nat_add(v___x_1955_, v_size_1973_);
if (lean_obj_tag(v_l_1977_) == 0)
{
lean_object* v_size_2008_; 
v_size_2008_ = lean_ctor_get(v_l_1977_, 0);
lean_inc(v_size_2008_);
v___y_2000_ = v_size_2008_;
goto v___jp_1999_;
}
else
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_unsigned_to_nat(0u);
v___y_2000_ = v___x_2009_;
goto v___jp_1999_;
}
v___jp_1987_:
{
lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1991_ = lean_nat_add(v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec(v___y_1989_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 4, v_r_1810_);
lean_ctor_set(v___x_1983_, 3, v_r_1978_);
lean_ctor_set(v___x_1983_, 2, v_v_1808_);
lean_ctor_set(v___x_1983_, 1, v_k_1807_);
lean_ctor_set(v___x_1983_, 0, v___x_1991_);
v___x_1993_ = v___x_1983_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v_k_1807_);
lean_ctor_set(v_reuseFailAlloc_1997_, 2, v_v_1808_);
lean_ctor_set(v_reuseFailAlloc_1997_, 3, v_r_1978_);
lean_ctor_set(v_reuseFailAlloc_1997_, 4, v_r_1810_);
v___x_1993_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1995_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 4, v___x_1993_);
lean_ctor_set(v___x_1971_, 3, v___y_1988_);
lean_ctor_set(v___x_1971_, 2, v_v_1976_);
lean_ctor_set(v___x_1971_, 1, v_k_1975_);
lean_ctor_set(v___x_1971_, 0, v___x_1986_);
v___x_1995_ = v___x_1971_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_k_1975_);
lean_ctor_set(v_reuseFailAlloc_1996_, 2, v_v_1976_);
lean_ctor_set(v_reuseFailAlloc_1996_, 3, v___y_1988_);
lean_ctor_set(v_reuseFailAlloc_1996_, 4, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
v___jp_1999_:
{
lean_object* v___x_2001_; lean_object* v___x_2003_; 
v___x_2001_ = lean_nat_add(v___x_1998_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec(v___x_1998_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 4, v_l_1977_);
lean_ctor_set(v___x_1812_, 3, v_l_1960_);
lean_ctor_set(v___x_1812_, 2, v_v_1959_);
lean_ctor_set(v___x_1812_, 1, v_k_1958_);
lean_ctor_set(v___x_1812_, 0, v___x_2001_);
v___x_2003_ = v___x_1812_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2001_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_k_1958_);
lean_ctor_set(v_reuseFailAlloc_2007_, 2, v_v_1959_);
lean_ctor_set(v_reuseFailAlloc_2007_, 3, v_l_1960_);
lean_ctor_set(v_reuseFailAlloc_2007_, 4, v_l_1977_);
v___x_2003_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
lean_object* v___x_2004_; 
v___x_2004_ = lean_nat_add(v___x_1955_, v_size_1956_);
if (lean_obj_tag(v_r_1978_) == 0)
{
lean_object* v_size_2005_; 
v_size_2005_ = lean_ctor_get(v_r_1978_, 0);
lean_inc(v_size_2005_);
v___y_1988_ = v___x_2003_;
v___y_1989_ = v___x_2004_;
v___y_1990_ = v_size_2005_;
goto v___jp_1987_;
}
else
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_unsigned_to_nat(0u);
v___y_1988_ = v___x_2003_;
v___y_1989_ = v___x_2004_;
v___y_1990_ = v___x_2006_;
goto v___jp_1987_;
}
}
}
}
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
lean_del_object(v___x_1812_);
v___x_2016_ = lean_nat_add(v___x_1955_, v_size_1957_);
lean_dec(v_size_1957_);
v___x_2017_ = lean_nat_add(v___x_2016_, v_size_1956_);
lean_dec(v___x_2016_);
v___x_2018_ = lean_nat_add(v___x_1955_, v_size_1956_);
v___x_2019_ = lean_nat_add(v___x_2018_, v_size_1974_);
lean_dec(v___x_2018_);
lean_inc_ref(v_r_1810_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 4, v_r_1810_);
lean_ctor_set(v___x_1971_, 3, v_r_1961_);
lean_ctor_set(v___x_1971_, 2, v_v_1808_);
lean_ctor_set(v___x_1971_, 1, v_k_1807_);
lean_ctor_set(v___x_1971_, 0, v___x_2019_);
v___x_2021_ = v___x_1971_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_k_1807_);
lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_v_1808_);
lean_ctor_set(v_reuseFailAlloc_2034_, 3, v_r_1961_);
lean_ctor_set(v_reuseFailAlloc_2034_, 4, v_r_1810_);
v___x_2021_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
v_isSharedCheck_2028_ = !lean_is_exclusive(v_r_1810_);
if (v_isSharedCheck_2028_ == 0)
{
lean_object* v_unused_2029_; lean_object* v_unused_2030_; lean_object* v_unused_2031_; lean_object* v_unused_2032_; lean_object* v_unused_2033_; 
v_unused_2029_ = lean_ctor_get(v_r_1810_, 4);
lean_dec(v_unused_2029_);
v_unused_2030_ = lean_ctor_get(v_r_1810_, 3);
lean_dec(v_unused_2030_);
v_unused_2031_ = lean_ctor_get(v_r_1810_, 2);
lean_dec(v_unused_2031_);
v_unused_2032_ = lean_ctor_get(v_r_1810_, 1);
lean_dec(v_unused_2032_);
v_unused_2033_ = lean_ctor_get(v_r_1810_, 0);
lean_dec(v_unused_2033_);
v___x_2023_ = v_r_1810_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_dec(v_r_1810_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 4, v___x_2021_);
lean_ctor_set(v___x_2023_, 3, v_l_1960_);
lean_ctor_set(v___x_2023_, 2, v_v_1959_);
lean_ctor_set(v___x_2023_, 1, v_k_1958_);
lean_ctor_set(v___x_2023_, 0, v___x_2017_);
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_k_1958_);
lean_ctor_set(v_reuseFailAlloc_2027_, 2, v_v_1959_);
lean_ctor_set(v_reuseFailAlloc_2027_, 3, v_l_1960_);
lean_ctor_set(v_reuseFailAlloc_2027_, 4, v___x_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2041_; 
v_l_2041_ = lean_ctor_get(v_impl_1954_, 3);
lean_inc(v_l_2041_);
if (lean_obj_tag(v_l_2041_) == 0)
{
lean_object* v_r_2042_; lean_object* v_k_2043_; lean_object* v_v_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2055_; 
v_r_2042_ = lean_ctor_get(v_impl_1954_, 4);
v_k_2043_ = lean_ctor_get(v_impl_1954_, 1);
v_v_2044_ = lean_ctor_get(v_impl_1954_, 2);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_impl_1954_);
if (v_isSharedCheck_2055_ == 0)
{
lean_object* v_unused_2056_; lean_object* v_unused_2057_; 
v_unused_2056_ = lean_ctor_get(v_impl_1954_, 3);
lean_dec(v_unused_2056_);
v_unused_2057_ = lean_ctor_get(v_impl_1954_, 0);
lean_dec(v_unused_2057_);
v___x_2046_ = v_impl_1954_;
v_isShared_2047_ = v_isSharedCheck_2055_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_r_2042_);
lean_inc(v_v_2044_);
lean_inc(v_k_2043_);
lean_dec(v_impl_1954_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2055_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2048_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2042_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 3, v_r_2042_);
lean_ctor_set(v___x_2046_, 2, v_v_1808_);
lean_ctor_set(v___x_2046_, 1, v_k_1807_);
lean_ctor_set(v___x_2046_, 0, v___x_1955_);
v___x_2050_ = v___x_2046_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_k_1807_);
lean_ctor_set(v_reuseFailAlloc_2054_, 2, v_v_1808_);
lean_ctor_set(v_reuseFailAlloc_2054_, 3, v_r_2042_);
lean_ctor_set(v_reuseFailAlloc_2054_, 4, v_r_2042_);
v___x_2050_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2052_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 4, v___x_2050_);
lean_ctor_set(v___x_1812_, 3, v_l_2041_);
lean_ctor_set(v___x_1812_, 2, v_v_2044_);
lean_ctor_set(v___x_1812_, 1, v_k_2043_);
lean_ctor_set(v___x_1812_, 0, v___x_2048_);
v___x_2052_ = v___x_1812_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_k_2043_);
lean_ctor_set(v_reuseFailAlloc_2053_, 2, v_v_2044_);
lean_ctor_set(v_reuseFailAlloc_2053_, 3, v_l_2041_);
lean_ctor_set(v_reuseFailAlloc_2053_, 4, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v_r_2058_; 
v_r_2058_ = lean_ctor_get(v_impl_1954_, 4);
lean_inc(v_r_2058_);
if (lean_obj_tag(v_r_2058_) == 0)
{
lean_object* v_k_2059_; lean_object* v_v_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2083_; 
v_k_2059_ = lean_ctor_get(v_impl_1954_, 1);
v_v_2060_ = lean_ctor_get(v_impl_1954_, 2);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_impl_1954_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; lean_object* v_unused_2085_; lean_object* v_unused_2086_; 
v_unused_2084_ = lean_ctor_get(v_impl_1954_, 4);
lean_dec(v_unused_2084_);
v_unused_2085_ = lean_ctor_get(v_impl_1954_, 3);
lean_dec(v_unused_2085_);
v_unused_2086_ = lean_ctor_get(v_impl_1954_, 0);
lean_dec(v_unused_2086_);
v___x_2062_ = v_impl_1954_;
v_isShared_2063_ = v_isSharedCheck_2083_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_v_2060_);
lean_inc(v_k_2059_);
lean_dec(v_impl_1954_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2083_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v_k_2064_; lean_object* v_v_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2079_; 
v_k_2064_ = lean_ctor_get(v_r_2058_, 1);
v_v_2065_ = lean_ctor_get(v_r_2058_, 2);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_r_2058_);
if (v_isSharedCheck_2079_ == 0)
{
lean_object* v_unused_2080_; lean_object* v_unused_2081_; lean_object* v_unused_2082_; 
v_unused_2080_ = lean_ctor_get(v_r_2058_, 4);
lean_dec(v_unused_2080_);
v_unused_2081_ = lean_ctor_get(v_r_2058_, 3);
lean_dec(v_unused_2081_);
v_unused_2082_ = lean_ctor_get(v_r_2058_, 0);
lean_dec(v_unused_2082_);
v___x_2067_ = v_r_2058_;
v_isShared_2068_ = v_isSharedCheck_2079_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_v_2065_);
lean_inc(v_k_2064_);
lean_dec(v_r_2058_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2079_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2069_ = lean_unsigned_to_nat(3u);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 4, v_l_2041_);
lean_ctor_set(v___x_2067_, 3, v_l_2041_);
lean_ctor_set(v___x_2067_, 2, v_v_2060_);
lean_ctor_set(v___x_2067_, 1, v_k_2059_);
lean_ctor_set(v___x_2067_, 0, v___x_1955_);
v___x_2071_ = v___x_2067_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_k_2059_);
lean_ctor_set(v_reuseFailAlloc_2078_, 2, v_v_2060_);
lean_ctor_set(v_reuseFailAlloc_2078_, 3, v_l_2041_);
lean_ctor_set(v_reuseFailAlloc_2078_, 4, v_l_2041_);
v___x_2071_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2073_; 
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 4, v_l_2041_);
lean_ctor_set(v___x_2062_, 2, v_v_1808_);
lean_ctor_set(v___x_2062_, 1, v_k_1807_);
lean_ctor_set(v___x_2062_, 0, v___x_1955_);
v___x_2073_ = v___x_2062_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_k_1807_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_v_1808_);
lean_ctor_set(v_reuseFailAlloc_2077_, 3, v_l_2041_);
lean_ctor_set(v_reuseFailAlloc_2077_, 4, v_l_2041_);
v___x_2073_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2075_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 4, v___x_2073_);
lean_ctor_set(v___x_1812_, 3, v___x_2071_);
lean_ctor_set(v___x_1812_, 2, v_v_2065_);
lean_ctor_set(v___x_1812_, 1, v_k_2064_);
lean_ctor_set(v___x_1812_, 0, v___x_2069_);
v___x_2075_ = v___x_1812_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_k_2064_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_v_2065_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2076_, 4, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2087_ = lean_unsigned_to_nat(2u);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 4, v_r_2058_);
lean_ctor_set(v___x_1812_, 3, v_impl_1954_);
lean_ctor_set(v___x_1812_, 0, v___x_2087_);
v___x_2089_ = v___x_1812_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_k_1807_);
lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_v_1808_);
lean_ctor_set(v_reuseFailAlloc_2090_, 3, v_impl_1954_);
lean_ctor_set(v_reuseFailAlloc_2090_, 4, v_r_2058_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = lean_unsigned_to_nat(1u);
v___x_2093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
lean_ctor_set(v___x_2093_, 1, v_k_1803_);
lean_ctor_set(v___x_2093_, 2, v_v_1804_);
lean_ctor_set(v___x_2093_, 3, v_t_1805_);
lean_ctor_set(v___x_2093_, 4, v_t_1805_);
return v___x_2093_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(lean_object* v_k_2094_, lean_object* v_t_2095_){
_start:
{
if (lean_obj_tag(v_t_2095_) == 0)
{
lean_object* v_k_2096_; lean_object* v_l_2097_; lean_object* v_r_2098_; uint8_t v___x_2099_; 
v_k_2096_ = lean_ctor_get(v_t_2095_, 1);
v_l_2097_ = lean_ctor_get(v_t_2095_, 3);
v_r_2098_ = lean_ctor_get(v_t_2095_, 4);
v___x_2099_ = lean_nat_dec_lt(v_k_2094_, v_k_2096_);
if (v___x_2099_ == 0)
{
uint8_t v___x_2100_; 
v___x_2100_ = lean_nat_dec_eq(v_k_2094_, v_k_2096_);
if (v___x_2100_ == 0)
{
v_t_2095_ = v_r_2098_;
goto _start;
}
else
{
return v___x_2100_;
}
}
else
{
v_t_2095_ = v_l_2097_;
goto _start;
}
}
else
{
uint8_t v___x_2103_; 
v___x_2103_ = 0;
return v___x_2103_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg___boxed(lean_object* v_k_2104_, lean_object* v_t_2105_){
_start:
{
uint8_t v_res_2106_; lean_object* v_r_2107_; 
v_res_2106_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2104_, v_t_2105_);
lean_dec(v_t_2105_);
lean_dec(v_k_2104_);
v_r_2107_ = lean_box(v_res_2106_);
return v_r_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(lean_object* v_y_2108_, lean_object* v_x_2109_, size_t v_x_2110_, size_t v_x_2111_){
_start:
{
if (lean_obj_tag(v_x_2109_) == 0)
{
lean_object* v_cs_2112_; size_t v_j_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v_cs_2112_ = lean_ctor_get(v_x_2109_, 0);
v_j_2113_ = lean_usize_shift_right(v_x_2110_, v_x_2111_);
v___x_2114_ = lean_usize_to_nat(v_j_2113_);
v___x_2115_ = lean_array_get_size(v_cs_2112_);
v___x_2116_ = lean_nat_dec_lt(v___x_2114_, v___x_2115_);
if (v___x_2116_ == 0)
{
lean_dec(v___x_2114_);
lean_dec(v_y_2108_);
return v_x_2109_;
}
else
{
lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2134_; 
lean_inc_ref(v_cs_2112_);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_x_2109_);
if (v_isSharedCheck_2134_ == 0)
{
lean_object* v_unused_2135_; 
v_unused_2135_ = lean_ctor_get(v_x_2109_, 0);
lean_dec(v_unused_2135_);
v___x_2118_ = v_x_2109_;
v_isShared_2119_ = v_isSharedCheck_2134_;
goto v_resetjp_2117_;
}
else
{
lean_dec(v_x_2109_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2134_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
size_t v___x_2120_; size_t v___x_2121_; size_t v___x_2122_; size_t v_i_2123_; size_t v___x_2124_; size_t v_shift_2125_; lean_object* v_v_2126_; lean_object* v___x_2127_; lean_object* v_xs_x27_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2120_ = ((size_t)1ULL);
v___x_2121_ = lean_usize_shift_left(v___x_2120_, v_x_2111_);
v___x_2122_ = lean_usize_sub(v___x_2121_, v___x_2120_);
v_i_2123_ = lean_usize_land(v_x_2110_, v___x_2122_);
v___x_2124_ = ((size_t)5ULL);
v_shift_2125_ = lean_usize_sub(v_x_2111_, v___x_2124_);
v_v_2126_ = lean_array_fget(v_cs_2112_, v___x_2114_);
v___x_2127_ = lean_box(0);
v_xs_x27_2128_ = lean_array_fset(v_cs_2112_, v___x_2114_, v___x_2127_);
v___x_2129_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2108_, v_v_2126_, v_i_2123_, v_shift_2125_);
v___x_2130_ = lean_array_fset(v_xs_x27_2128_, v___x_2114_, v___x_2129_);
lean_dec(v___x_2114_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2130_);
v___x_2132_ = v___x_2118_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
lean_object* v_vs_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v_vs_2136_ = lean_ctor_get(v_x_2109_, 0);
v___x_2137_ = lean_usize_to_nat(v_x_2110_);
v___x_2138_ = lean_array_get_size(v_vs_2136_);
v___x_2139_ = lean_nat_dec_lt(v___x_2137_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_dec(v___x_2137_);
lean_dec(v_y_2108_);
return v_x_2109_;
}
else
{
lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2154_; 
lean_inc_ref(v_vs_2136_);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_x_2109_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v_x_2109_, 0);
lean_dec(v_unused_2155_);
v___x_2141_ = v_x_2109_;
v_isShared_2142_ = v_isSharedCheck_2154_;
goto v_resetjp_2140_;
}
else
{
lean_dec(v_x_2109_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2154_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v_v_2143_; lean_object* v___x_2144_; lean_object* v_xs_x27_2145_; lean_object* v___y_2147_; uint8_t v___x_2152_; 
v_v_2143_ = lean_array_fget(v_vs_2136_, v___x_2137_);
v___x_2144_ = lean_box(0);
v_xs_x27_2145_ = lean_array_fset(v_vs_2136_, v___x_2137_, v___x_2144_);
v___x_2152_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2108_, v_v_2143_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2108_, v___x_2144_, v_v_2143_);
v___y_2147_ = v___x_2153_;
goto v___jp_2146_;
}
else
{
lean_dec(v_y_2108_);
v___y_2147_ = v_v_2143_;
goto v___jp_2146_;
}
v___jp_2146_:
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2148_ = lean_array_fset(v_xs_x27_2145_, v___x_2137_, v___y_2147_);
lean_dec(v___x_2137_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v___x_2148_);
v___x_2150_ = v___x_2141_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2156_, lean_object* v_x_2157_, lean_object* v_x_2158_, lean_object* v_x_2159_){
_start:
{
size_t v_x_4518__boxed_2160_; size_t v_x_4519__boxed_2161_; lean_object* v_res_2162_; 
v_x_4518__boxed_2160_ = lean_unbox_usize(v_x_2158_);
lean_dec(v_x_2158_);
v_x_4519__boxed_2161_ = lean_unbox_usize(v_x_2159_);
lean_dec(v_x_2159_);
v_res_2162_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2156_, v_x_2157_, v_x_4518__boxed_2160_, v_x_4519__boxed_2161_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(lean_object* v_y_2163_, lean_object* v_t_2164_, lean_object* v_i_2165_){
_start:
{
lean_object* v_root_2166_; lean_object* v_tail_2167_; lean_object* v_size_2168_; size_t v_shift_2169_; lean_object* v_tailOff_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2197_; 
v_root_2166_ = lean_ctor_get(v_t_2164_, 0);
v_tail_2167_ = lean_ctor_get(v_t_2164_, 1);
v_size_2168_ = lean_ctor_get(v_t_2164_, 2);
v_shift_2169_ = lean_ctor_get_usize(v_t_2164_, 4);
v_tailOff_2170_ = lean_ctor_get(v_t_2164_, 3);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_t_2164_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2172_ = v_t_2164_;
v_isShared_2173_ = v_isSharedCheck_2197_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_tailOff_2170_);
lean_inc(v_size_2168_);
lean_inc(v_tail_2167_);
lean_inc(v_root_2166_);
lean_dec(v_t_2164_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2197_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
uint8_t v___x_2174_; 
v___x_2174_ = lean_nat_dec_le(v_tailOff_2170_, v_i_2165_);
if (v___x_2174_ == 0)
{
size_t v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2178_; 
v___x_2175_ = lean_usize_of_nat(v_i_2165_);
v___x_2176_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2163_, v_root_2166_, v___x_2175_, v_shift_2169_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2176_);
v___x_2178_ = v___x_2172_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_tail_2167_);
lean_ctor_set(v_reuseFailAlloc_2179_, 2, v_size_2168_);
lean_ctor_set(v_reuseFailAlloc_2179_, 3, v_tailOff_2170_);
lean_ctor_set_usize(v_reuseFailAlloc_2179_, 4, v_shift_2169_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
else
{
lean_object* v___x_2180_; lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2180_ = lean_nat_sub(v_i_2165_, v_tailOff_2170_);
v___x_2181_ = lean_array_get_size(v_tail_2167_);
v___x_2182_ = lean_nat_dec_lt(v___x_2180_, v___x_2181_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2184_; 
lean_dec(v___x_2180_);
lean_dec(v_y_2163_);
if (v_isShared_2173_ == 0)
{
v___x_2184_ = v___x_2172_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_root_2166_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_tail_2167_);
lean_ctor_set(v_reuseFailAlloc_2185_, 2, v_size_2168_);
lean_ctor_set(v_reuseFailAlloc_2185_, 3, v_tailOff_2170_);
lean_ctor_set_usize(v_reuseFailAlloc_2185_, 4, v_shift_2169_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
else
{
lean_object* v_v_2186_; lean_object* v___x_2187_; lean_object* v_xs_x27_2188_; lean_object* v___y_2190_; uint8_t v___x_2195_; 
v_v_2186_ = lean_array_fget(v_tail_2167_, v___x_2180_);
v___x_2187_ = lean_box(0);
v_xs_x27_2188_ = lean_array_fset(v_tail_2167_, v___x_2180_, v___x_2187_);
v___x_2195_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2163_, v_v_2186_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2163_, v___x_2187_, v_v_2186_);
v___y_2190_ = v___x_2196_;
goto v___jp_2189_;
}
else
{
lean_dec(v_y_2163_);
v___y_2190_ = v_v_2186_;
goto v___jp_2189_;
}
v___jp_2189_:
{
lean_object* v___x_2191_; lean_object* v___x_2193_; 
v___x_2191_ = lean_array_fset(v_xs_x27_2188_, v___x_2180_, v___y_2190_);
lean_dec(v___x_2180_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 1, v___x_2191_);
v___x_2193_ = v___x_2172_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_root_2166_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2194_, 2, v_size_2168_);
lean_ctor_set(v_reuseFailAlloc_2194_, 3, v_tailOff_2170_);
lean_ctor_set_usize(v_reuseFailAlloc_2194_, 4, v_shift_2169_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2___boxed(lean_object* v_y_2198_, lean_object* v_t_2199_, lean_object* v_i_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2198_, v_t_2199_, v_i_2200_);
lean_dec(v_i_2200_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(lean_object* v_y_2202_, lean_object* v_x_2203_, lean_object* v_s_2204_){
_start:
{
lean_object* v_vars_2205_; lean_object* v_varMap_2206_; lean_object* v_vars_x27_2207_; lean_object* v_varMap_x27_2208_; lean_object* v_natToIntMap_2209_; lean_object* v_natDef_2210_; lean_object* v_dvds_2211_; lean_object* v_lowers_2212_; lean_object* v_uppers_2213_; lean_object* v_diseqs_2214_; lean_object* v_elimEqs_2215_; lean_object* v_elimStack_2216_; lean_object* v_occurs_2217_; lean_object* v_assignment_2218_; lean_object* v_nextCnstrId_2219_; uint8_t v_caseSplits_2220_; lean_object* v_conflict_x3f_2221_; lean_object* v_diseqSplits_2222_; lean_object* v_divMod_2223_; lean_object* v_toIntIds_2224_; lean_object* v_toIntInfos_2225_; lean_object* v_toIntTermMap_2226_; lean_object* v_toIntVarMap_2227_; uint8_t v_usedCommRing_2228_; lean_object* v_nonlinearOccs_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2237_; 
v_vars_2205_ = lean_ctor_get(v_s_2204_, 0);
v_varMap_2206_ = lean_ctor_get(v_s_2204_, 1);
v_vars_x27_2207_ = lean_ctor_get(v_s_2204_, 2);
v_varMap_x27_2208_ = lean_ctor_get(v_s_2204_, 3);
v_natToIntMap_2209_ = lean_ctor_get(v_s_2204_, 4);
v_natDef_2210_ = lean_ctor_get(v_s_2204_, 5);
v_dvds_2211_ = lean_ctor_get(v_s_2204_, 6);
v_lowers_2212_ = lean_ctor_get(v_s_2204_, 7);
v_uppers_2213_ = lean_ctor_get(v_s_2204_, 8);
v_diseqs_2214_ = lean_ctor_get(v_s_2204_, 9);
v_elimEqs_2215_ = lean_ctor_get(v_s_2204_, 10);
v_elimStack_2216_ = lean_ctor_get(v_s_2204_, 11);
v_occurs_2217_ = lean_ctor_get(v_s_2204_, 12);
v_assignment_2218_ = lean_ctor_get(v_s_2204_, 13);
v_nextCnstrId_2219_ = lean_ctor_get(v_s_2204_, 14);
v_caseSplits_2220_ = lean_ctor_get_uint8(v_s_2204_, sizeof(void*)*23);
v_conflict_x3f_2221_ = lean_ctor_get(v_s_2204_, 15);
v_diseqSplits_2222_ = lean_ctor_get(v_s_2204_, 16);
v_divMod_2223_ = lean_ctor_get(v_s_2204_, 17);
v_toIntIds_2224_ = lean_ctor_get(v_s_2204_, 18);
v_toIntInfos_2225_ = lean_ctor_get(v_s_2204_, 19);
v_toIntTermMap_2226_ = lean_ctor_get(v_s_2204_, 20);
v_toIntVarMap_2227_ = lean_ctor_get(v_s_2204_, 21);
v_usedCommRing_2228_ = lean_ctor_get_uint8(v_s_2204_, sizeof(void*)*23 + 1);
v_nonlinearOccs_2229_ = lean_ctor_get(v_s_2204_, 22);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_s_2204_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2231_ = v_s_2204_;
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_nonlinearOccs_2229_);
lean_inc(v_toIntVarMap_2227_);
lean_inc(v_toIntTermMap_2226_);
lean_inc(v_toIntInfos_2225_);
lean_inc(v_toIntIds_2224_);
lean_inc(v_divMod_2223_);
lean_inc(v_diseqSplits_2222_);
lean_inc(v_conflict_x3f_2221_);
lean_inc(v_nextCnstrId_2219_);
lean_inc(v_assignment_2218_);
lean_inc(v_occurs_2217_);
lean_inc(v_elimStack_2216_);
lean_inc(v_elimEqs_2215_);
lean_inc(v_diseqs_2214_);
lean_inc(v_uppers_2213_);
lean_inc(v_lowers_2212_);
lean_inc(v_dvds_2211_);
lean_inc(v_natDef_2210_);
lean_inc(v_natToIntMap_2209_);
lean_inc(v_varMap_x27_2208_);
lean_inc(v_vars_x27_2207_);
lean_inc(v_varMap_2206_);
lean_inc(v_vars_2205_);
lean_dec(v_s_2204_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2233_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2202_, v_occurs_2217_, v_x_2203_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 12, v___x_2233_);
v___x_2235_ = v___x_2231_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_vars_2205_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_varMap_2206_);
lean_ctor_set(v_reuseFailAlloc_2236_, 2, v_vars_x27_2207_);
lean_ctor_set(v_reuseFailAlloc_2236_, 3, v_varMap_x27_2208_);
lean_ctor_set(v_reuseFailAlloc_2236_, 4, v_natToIntMap_2209_);
lean_ctor_set(v_reuseFailAlloc_2236_, 5, v_natDef_2210_);
lean_ctor_set(v_reuseFailAlloc_2236_, 6, v_dvds_2211_);
lean_ctor_set(v_reuseFailAlloc_2236_, 7, v_lowers_2212_);
lean_ctor_set(v_reuseFailAlloc_2236_, 8, v_uppers_2213_);
lean_ctor_set(v_reuseFailAlloc_2236_, 9, v_diseqs_2214_);
lean_ctor_set(v_reuseFailAlloc_2236_, 10, v_elimEqs_2215_);
lean_ctor_set(v_reuseFailAlloc_2236_, 11, v_elimStack_2216_);
lean_ctor_set(v_reuseFailAlloc_2236_, 12, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2236_, 13, v_assignment_2218_);
lean_ctor_set(v_reuseFailAlloc_2236_, 14, v_nextCnstrId_2219_);
lean_ctor_set(v_reuseFailAlloc_2236_, 15, v_conflict_x3f_2221_);
lean_ctor_set(v_reuseFailAlloc_2236_, 16, v_diseqSplits_2222_);
lean_ctor_set(v_reuseFailAlloc_2236_, 17, v_divMod_2223_);
lean_ctor_set(v_reuseFailAlloc_2236_, 18, v_toIntIds_2224_);
lean_ctor_set(v_reuseFailAlloc_2236_, 19, v_toIntInfos_2225_);
lean_ctor_set(v_reuseFailAlloc_2236_, 20, v_toIntTermMap_2226_);
lean_ctor_set(v_reuseFailAlloc_2236_, 21, v_toIntVarMap_2227_);
lean_ctor_set(v_reuseFailAlloc_2236_, 22, v_nonlinearOccs_2229_);
lean_ctor_set_uint8(v_reuseFailAlloc_2236_, sizeof(void*)*23, v_caseSplits_2220_);
lean_ctor_set_uint8(v_reuseFailAlloc_2236_, sizeof(void*)*23 + 1, v_usedCommRing_2228_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed(lean_object* v_y_2238_, lean_object* v_x_2239_, lean_object* v_s_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(v_y_2238_, v_x_2239_, v_s_2240_);
lean_dec(v_x_2239_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(lean_object* v_x_2242_, lean_object* v_y_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2242_, v_a_2244_, v_a_2245_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2260_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2250_ = v___x_2247_;
v_isShared_2251_ = v_isSharedCheck_2260_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2247_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2260_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
uint8_t v___x_2252_; 
v___x_2252_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2243_, v_a_2248_);
lean_dec(v_a_2248_);
if (v___x_2252_ == 0)
{
lean_object* v___f_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
lean_del_object(v___x_2250_);
v___f_2253_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2253_, 0, v_y_2243_);
lean_closure_set(v___f_2253_, 1, v_x_2242_);
v___x_2254_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2255_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2254_, v___f_2253_, v_a_2244_);
return v___x_2255_;
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2258_; 
lean_dec(v_y_2243_);
lean_dec(v_x_2242_);
v___x_2256_ = lean_box(0);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v___x_2256_);
v___x_2258_ = v___x_2250_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
lean_dec(v_y_2243_);
lean_dec(v_x_2242_);
v_a_2261_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2247_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2247_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___boxed(lean_object* v_x_2269_, lean_object* v_y_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2269_, v_y_2270_, v_a_2271_, v_a_2272_);
lean_dec_ref(v_a_2272_);
lean_dec(v_a_2271_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc(lean_object* v_x_2275_, lean_object* v_y_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2275_, v_y_2276_, v_a_2277_, v_a_2285_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___boxed(lean_object* v_x_2289_, lean_object* v_y_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc(v_x_2289_, v_y_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec(v_a_2291_);
return v_res_2302_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(lean_object* v_00_u03b2_2303_, lean_object* v_k_2304_, lean_object* v_t_2305_){
_start:
{
uint8_t v___x_2306_; 
v___x_2306_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2304_, v_t_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2307_, lean_object* v_k_2308_, lean_object* v_t_2309_){
_start:
{
uint8_t v_res_2310_; lean_object* v_r_2311_; 
v_res_2310_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(v_00_u03b2_2307_, v_k_2308_, v_t_2309_);
lean_dec(v_t_2309_);
lean_dec(v_k_2308_);
v_r_2311_ = lean_box(v_res_2310_);
return v_r_2311_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1(lean_object* v_00_u03b2_2312_, lean_object* v_k_2313_, lean_object* v_v_2314_, lean_object* v_t_2315_, lean_object* v_hl_2316_){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2313_, v_v_2314_, v_t_2315_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(lean_object* v_y_2318_, lean_object* v_p_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_){
_start:
{
if (lean_obj_tag(v_p_2319_) == 1)
{
lean_object* v_v_2323_; lean_object* v_p_2324_; lean_object* v___x_2325_; 
v_v_2323_ = lean_ctor_get(v_p_2319_, 1);
lean_inc(v_v_2323_);
v_p_2324_ = lean_ctor_get(v_p_2319_, 2);
lean_inc_ref(v_p_2324_);
lean_dec_ref_known(v_p_2319_, 3);
lean_inc(v_y_2318_);
v___x_2325_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_v_2323_, v_y_2318_, v_a_2320_, v_a_2321_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_dec_ref_known(v___x_2325_, 1);
v_p_2319_ = v_p_2324_;
goto _start;
}
else
{
lean_dec_ref(v_p_2324_);
lean_dec(v_y_2318_);
return v___x_2325_;
}
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_dec_ref(v_p_2319_);
lean_dec(v_y_2318_);
v___x_2327_ = lean_box(0);
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
return v___x_2328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg___boxed(lean_object* v_y_2329_, lean_object* v_p_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(v_y_2329_, v_p_2330_, v_a_2331_, v_a_2332_);
lean_dec_ref(v_a_2332_);
lean_dec(v_a_2331_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go(lean_object* v_y_2335_, lean_object* v_p_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(v_y_2335_, v_p_2336_, v_a_2337_, v_a_2345_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___boxed(lean_object* v_y_2349_, lean_object* v_p_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go(v_y_2349_, v_p_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec(v_a_2356_);
lean_dec_ref(v_a_2355_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
lean_dec(v_a_2352_);
lean_dec(v_a_2351_);
return v_res_2362_;
}
}
static lean_object* _init_l_Int_Linear_Poly_updateOccs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = ((lean_object*)(l_Int_Linear_Poly_updateOccs___redArg___closed__0));
v___x_2365_ = l_Lean_stringToMessageData(v___x_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_updateOccs___redArg(lean_object* v_p_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
if (lean_obj_tag(v_p_2366_) == 1)
{
lean_object* v_v_2373_; lean_object* v_p_2374_; lean_object* v___x_2375_; 
v_v_2373_ = lean_ctor_get(v_p_2366_, 1);
lean_inc(v_v_2373_);
v_p_2374_ = lean_ctor_get(v_p_2366_, 2);
lean_inc_ref(v_p_2374_);
lean_dec_ref_known(v_p_2366_, 3);
v___x_2375_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(v_v_2373_, v_p_2374_, v_a_2367_, v_a_2370_);
return v___x_2375_;
}
else
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
lean_dec_ref(v_p_2366_);
v___x_2376_ = lean_obj_once(&l_Int_Linear_Poly_updateOccs___redArg___closed__1, &l_Int_Linear_Poly_updateOccs___redArg___closed__1_once, _init_l_Int_Linear_Poly_updateOccs___redArg___closed__1);
v___x_2377_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2376_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_2377_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_updateOccs___redArg___boxed(lean_object* v_p_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l_Int_Linear_Poly_updateOccs___redArg(v_p_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_updateOccs(lean_object* v_p_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Int_Linear_Poly_updateOccs___redArg(v_p_2386_, v_a_2387_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_updateOccs___boxed(lean_object* v_p_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Int_Linear_Poly_updateOccs(v_p_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec(v_a_2400_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go_spec__0(lean_object* v_a_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Rat_ofInt(v_a_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go(lean_object* v_a_2414_, lean_object* v_v_2415_, lean_object* v_a_2416_){
_start:
{
if (lean_obj_tag(v_a_2416_) == 0)
{
lean_object* v_k_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2426_; 
v_k_2417_ = lean_ctor_get(v_a_2416_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_a_2416_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2419_ = v_a_2416_;
v_isShared_2420_ = v_isSharedCheck_2426_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_k_2417_);
lean_dec(v_a_2416_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2426_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2421_ = l_Rat_ofInt(v_k_2417_);
v___x_2422_ = l_Rat_add(v_v_2415_, v___x_2421_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set_tag(v___x_2419_, 1);
lean_ctor_set(v___x_2419_, 0, v___x_2422_);
v___x_2424_ = v___x_2419_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
else
{
lean_object* v_k_2427_; lean_object* v_v_2428_; lean_object* v_p_2429_; lean_object* v_size_2430_; uint8_t v___x_2431_; 
v_k_2427_ = lean_ctor_get(v_a_2416_, 0);
lean_inc(v_k_2427_);
v_v_2428_ = lean_ctor_get(v_a_2416_, 1);
lean_inc(v_v_2428_);
v_p_2429_ = lean_ctor_get(v_a_2416_, 2);
lean_inc_ref(v_p_2429_);
lean_dec_ref_known(v_a_2416_, 3);
v_size_2430_ = lean_ctor_get(v_a_2414_, 2);
v___x_2431_ = lean_nat_dec_lt(v_v_2428_, v_size_2430_);
if (v___x_2431_ == 0)
{
lean_object* v___x_2432_; 
lean_dec_ref(v_p_2429_);
lean_dec(v_v_2428_);
lean_dec(v_k_2427_);
lean_dec_ref(v_v_2415_);
v___x_2432_ = lean_box(0);
return v___x_2432_;
}
else
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2433_ = l_Rat_ofInt(v_k_2427_);
v___x_2434_ = l_instInhabitedRat;
v___x_2435_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2434_, v_a_2414_, v_v_2428_);
lean_dec(v_v_2428_);
v___x_2436_ = l_Rat_mul(v___x_2433_, v___x_2435_);
lean_dec_ref(v___x_2433_);
v___x_2437_ = l_Rat_add(v_v_2415_, v___x_2436_);
v_v_2415_ = v___x_2437_;
v_a_2416_ = v_p_2429_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go___boxed(lean_object* v_a_2439_, lean_object* v_v_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go(v_a_2439_, v_v_2440_, v_a_2441_);
lean_dec_ref(v_a_2439_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_Linear_Poly_eval_x3f_spec__0(lean_object* v_a_2443_){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_nat_to_int(v_a_2443_);
v___x_2445_ = l_Rat_ofInt(v___x_2444_);
return v___x_2445_;
}
}
static lean_object* _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = lean_unsigned_to_nat(0u);
v___x_2447_ = l_Nat_cast___at___00Int_Linear_Poly_eval_x3f_spec__0(v___x_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_eval_x3f___redArg(lean_object* v_p_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2449_, v_a_2450_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2463_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2463_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2463_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v_assignment_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2461_; 
v_assignment_2457_ = lean_ctor_get(v_a_2453_, 13);
lean_inc_ref(v_assignment_2457_);
lean_dec(v_a_2453_);
v___x_2458_ = lean_obj_once(&l_Int_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2459_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go(v_assignment_2457_, v___x_2458_, v_p_2448_);
lean_dec_ref(v_assignment_2457_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2459_);
v___x_2461_ = v___x_2455_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec_ref(v_p_2448_);
v_a_2464_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2452_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2452_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_eval_x3f___redArg___boxed(lean_object* v_p_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2472_, v_a_2473_, v_a_2474_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_eval_x3f(lean_object* v_p_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2477_, v_a_2478_, v_a_2486_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_eval_x3f___boxed(lean_object* v_p_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Int_Linear_Poly_eval_x3f(v_p_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
lean_dec(v_a_2500_);
lean_dec_ref(v_a_2499_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
lean_dec(v_a_2494_);
lean_dec_ref(v_a_2493_);
lean_dec(v_a_2492_);
lean_dec(v_a_2491_);
return v_res_2502_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(lean_object* v_c_2503_){
_start:
{
lean_object* v_p_2504_; uint8_t v___x_2505_; 
v_p_2504_ = lean_ctor_get(v_c_2503_, 0);
v___x_2505_ = l_Int_Linear_Poly_isUnsatLe(v_p_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat___boxed(lean_object* v_c_2506_){
_start:
{
uint8_t v_res_2507_; lean_object* v_r_2508_; 
v_res_2507_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(v_c_2506_);
lean_dec_ref(v_c_2506_);
v_r_2508_ = lean_box(v_res_2507_);
return v_r_2508_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(lean_object* v_c_2509_){
_start:
{
lean_object* v_d_2510_; lean_object* v_p_2511_; uint8_t v___x_2512_; 
v_d_2510_ = lean_ctor_get(v_c_2509_, 0);
lean_inc(v_d_2510_);
v_p_2511_ = lean_ctor_get(v_c_2509_, 1);
lean_inc_ref(v_p_2511_);
lean_dec_ref(v_c_2509_);
v___x_2512_ = l_Int_Linear_Poly_isUnsatDvd(v_d_2510_, v_p_2511_);
lean_dec_ref(v_p_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat___boxed(lean_object* v_c_2513_){
_start:
{
uint8_t v_res_2514_; lean_object* v_r_2515_; 
v_res_2514_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(v_c_2513_);
v_r_2515_ = lean_box(v_res_2514_);
return v_r_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object* v_c_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v_d_2520_; lean_object* v_p_2521_; lean_object* v___x_2522_; 
v_d_2520_ = lean_ctor_get(v_c_2516_, 0);
lean_inc(v_d_2520_);
v_p_2521_ = lean_ctor_get(v_c_2516_, 1);
lean_inc_ref(v_p_2521_);
lean_dec_ref(v_c_2516_);
v___x_2522_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2521_, v_a_2517_, v_a_2518_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2548_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2525_ = v___x_2522_;
v_isShared_2526_ = v_isSharedCheck_2548_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2548_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
if (lean_obj_tag(v_a_2523_) == 1)
{
lean_object* v_val_2527_; lean_object* v_num_2528_; lean_object* v_den_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v_val_2527_ = lean_ctor_get(v_a_2523_, 0);
lean_inc(v_val_2527_);
lean_dec_ref_known(v_a_2523_, 1);
v_num_2528_ = lean_ctor_get(v_val_2527_, 0);
lean_inc(v_num_2528_);
v_den_2529_ = lean_ctor_get(v_val_2527_, 1);
lean_inc(v_den_2529_);
lean_dec(v_val_2527_);
v___x_2530_ = lean_unsigned_to_nat(1u);
v___x_2531_ = lean_nat_dec_eq(v_den_2529_, v___x_2530_);
lean_dec(v_den_2529_);
if (v___x_2531_ == 0)
{
uint8_t v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
lean_dec(v_num_2528_);
lean_dec(v_d_2520_);
v___x_2532_ = 0;
v___x_2533_ = lean_box(v___x_2532_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2533_);
v___x_2535_ = v___x_2525_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
else
{
uint8_t v___x_2537_; uint8_t v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2541_; 
v___x_2537_ = l_Int_decidableDvd(v_d_2520_, v_num_2528_);
lean_dec(v_num_2528_);
lean_dec(v_d_2520_);
v___x_2538_ = l_Bool_toLBool(v___x_2537_);
v___x_2539_ = lean_box(v___x_2538_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2539_);
v___x_2541_ = v___x_2525_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2539_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
else
{
uint8_t v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2546_; 
lean_dec(v_a_2523_);
lean_dec(v_d_2520_);
v___x_2543_ = 2;
v___x_2544_ = lean_box(v___x_2543_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2544_);
v___x_2546_ = v___x_2525_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2544_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec(v_d_2520_);
v_a_2549_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2522_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2522_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg___boxed(lean_object* v_c_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2557_, v_a_2558_, v_a_2559_);
lean_dec_ref(v_a_2559_);
lean_dec(v_a_2558_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(lean_object* v_c_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2562_, v_a_2563_, v_a_2571_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___boxed(lean_object* v_c_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(v_c_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_a_2583_);
lean_dec_ref(v_a_2582_);
lean_dec(v_a_2581_);
lean_dec_ref(v_a_2580_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec(v_a_2576_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_satisfiedLe___redArg(lean_object* v_p_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2588_, v_a_2589_, v_a_2590_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2610_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2610_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2610_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
if (lean_obj_tag(v_a_2593_) == 1)
{
lean_object* v_val_2597_; lean_object* v___x_2598_; uint8_t v___x_2599_; uint8_t v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
v_val_2597_ = lean_ctor_get(v_a_2593_, 0);
lean_inc(v_val_2597_);
lean_dec_ref_known(v_a_2593_, 1);
v___x_2598_ = lean_obj_once(&l_Int_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2599_ = l_Rat_instDecidableLe(v_val_2597_, v___x_2598_);
v___x_2600_ = l_Bool_toLBool(v___x_2599_);
v___x_2601_ = lean_box(v___x_2600_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2601_);
v___x_2603_ = v___x_2595_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
else
{
uint8_t v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2608_; 
lean_dec(v_a_2593_);
v___x_2605_ = 2;
v___x_2606_ = lean_box(v___x_2605_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2606_);
v___x_2608_ = v___x_2595_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
v_a_2611_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2592_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2592_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_satisfiedLe___redArg___boxed(lean_object* v_p_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Int_Linear_Poly_satisfiedLe___redArg(v_p_2619_, v_a_2620_, v_a_2621_);
lean_dec_ref(v_a_2621_);
lean_dec(v_a_2620_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_satisfiedLe(lean_object* v_p_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Int_Linear_Poly_satisfiedLe___redArg(v_p_2624_, v_a_2625_, v_a_2633_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_satisfiedLe___boxed(lean_object* v_p_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Int_Linear_Poly_satisfiedLe(v_p_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
lean_dec(v_a_2638_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(lean_object* v_c_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v_p_2654_; lean_object* v___x_2655_; 
v_p_2654_ = lean_ctor_get(v_c_2650_, 0);
lean_inc_ref(v_p_2654_);
lean_dec_ref(v_c_2650_);
v___x_2655_ = l_Int_Linear_Poly_satisfiedLe___redArg(v_p_2654_, v_a_2651_, v_a_2652_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg___boxed(lean_object* v_c_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2656_, v_a_2657_, v_a_2658_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(lean_object* v_c_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2661_, v_a_2662_, v_a_2670_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___boxed(lean_object* v_c_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(v_c_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec(v_a_2675_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(lean_object* v_c_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_p_2691_; lean_object* v___x_2692_; 
v_p_2691_ = lean_ctor_get(v_c_2687_, 0);
lean_inc_ref(v_p_2691_);
lean_dec_ref(v_c_2687_);
v___x_2692_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2691_, v_a_2688_, v_a_2689_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2712_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2695_ = v___x_2692_;
v_isShared_2696_ = v_isSharedCheck_2712_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2692_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2712_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
uint8_t v___y_2698_; 
if (lean_obj_tag(v_a_2693_) == 1)
{
lean_object* v_val_2704_; lean_object* v___x_2705_; uint8_t v___x_2706_; 
v_val_2704_ = lean_ctor_get(v_a_2693_, 0);
lean_inc(v_val_2704_);
lean_dec_ref_known(v_a_2693_, 1);
v___x_2705_ = lean_obj_once(&l_Int_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2706_ = l_instDecidableEqRat_decEq(v_val_2704_, v___x_2705_);
lean_dec(v_val_2704_);
if (v___x_2706_ == 0)
{
uint8_t v___x_2707_; 
v___x_2707_ = 1;
v___y_2698_ = v___x_2707_;
goto v___jp_2697_;
}
else
{
uint8_t v___x_2708_; 
v___x_2708_ = 0;
v___y_2698_ = v___x_2708_;
goto v___jp_2697_;
}
}
else
{
uint8_t v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_del_object(v___x_2695_);
lean_dec(v_a_2693_);
v___x_2709_ = 2;
v___x_2710_ = lean_box(v___x_2709_);
v___x_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
return v___x_2711_;
}
v___jp_2697_:
{
uint8_t v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2699_ = l_Bool_toLBool(v___y_2698_);
v___x_2700_ = lean_box(v___x_2699_);
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v___x_2700_);
v___x_2702_ = v___x_2695_;
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
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
v_a_2713_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2692_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2692_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg___boxed(lean_object* v_c_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_2721_, v_a_2722_, v_a_2723_);
lean_dec_ref(v_a_2723_);
lean_dec(v_a_2722_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(lean_object* v_c_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_){
_start:
{
lean_object* v___x_2738_; 
v___x_2738_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_2726_, v_a_2727_, v_a_2735_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___boxed(lean_object* v_c_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(v_c_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
lean_dec(v_a_2749_);
lean_dec_ref(v_a_2748_);
lean_dec(v_a_2747_);
lean_dec_ref(v_a_2746_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
lean_dec(v_a_2741_);
lean_dec(v_a_2740_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(lean_object* v_c_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v_p_2756_; lean_object* v___x_2757_; 
v_p_2756_ = lean_ctor_get(v_c_2752_, 0);
lean_inc_ref(v_p_2756_);
lean_dec_ref(v_c_2752_);
v___x_2757_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2756_, v_a_2753_, v_a_2754_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2775_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2760_ = v___x_2757_;
v_isShared_2761_ = v_isSharedCheck_2775_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2775_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
if (lean_obj_tag(v_a_2758_) == 1)
{
lean_object* v_val_2762_; lean_object* v___x_2763_; uint8_t v___x_2764_; uint8_t v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2768_; 
v_val_2762_ = lean_ctor_get(v_a_2758_, 0);
lean_inc(v_val_2762_);
lean_dec_ref_known(v_a_2758_, 1);
v___x_2763_ = lean_obj_once(&l_Int_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2764_ = l_instDecidableEqRat_decEq(v_val_2762_, v___x_2763_);
lean_dec(v_val_2762_);
v___x_2765_ = l_Bool_toLBool(v___x_2764_);
v___x_2766_ = lean_box(v___x_2765_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2766_);
v___x_2768_ = v___x_2760_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
else
{
uint8_t v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2773_; 
lean_dec(v_a_2758_);
v___x_2770_ = 2;
v___x_2771_ = lean_box(v___x_2770_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2771_);
v___x_2773_ = v___x_2760_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2771_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
v_a_2776_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2757_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2757_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg___boxed(lean_object* v_c_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_2784_, v_a_2785_, v_a_2786_);
lean_dec_ref(v_a_2786_);
lean_dec(v_a_2785_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(lean_object* v_c_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_2789_, v_a_2790_, v_a_2798_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___boxed(lean_object* v_c_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(v_c_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
lean_dec(v_a_2810_);
lean_dec_ref(v_a_2809_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_2807_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec(v_a_2803_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_findVarToSubst___redArg(lean_object* v_p_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_){
_start:
{
if (lean_obj_tag(v_p_2815_) == 0)
{
lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2826_; 
v_isSharedCheck_2826_ = !lean_is_exclusive(v_p_2815_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; 
v_unused_2827_ = lean_ctor_get(v_p_2815_, 0);
lean_dec(v_unused_2827_);
v___x_2820_ = v_p_2815_;
v_isShared_2821_ = v_isSharedCheck_2826_;
goto v_resetjp_2819_;
}
else
{
lean_dec(v_p_2815_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2826_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2822_; lean_object* v___x_2824_; 
v___x_2822_ = lean_box(0);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v___x_2822_);
v___x_2824_ = v___x_2820_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
else
{
lean_object* v_k_2828_; lean_object* v_v_2829_; lean_object* v_p_2830_; lean_object* v___x_2831_; 
v_k_2828_ = lean_ctor_get(v_p_2815_, 0);
lean_inc(v_k_2828_);
v_v_2829_ = lean_ctor_get(v_p_2815_, 1);
lean_inc(v_v_2829_);
v_p_2830_ = lean_ctor_get(v_p_2815_, 2);
lean_inc_ref(v_p_2830_);
lean_dec_ref_known(v_p_2815_, 3);
v___x_2831_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2858_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2858_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2858_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___y_2837_; lean_object* v_elimEqs_2852_; lean_object* v_size_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; 
v_elimEqs_2852_ = lean_ctor_get(v_a_2832_, 10);
lean_inc_ref(v_elimEqs_2852_);
lean_dec(v_a_2832_);
v_size_2853_ = lean_ctor_get(v_elimEqs_2852_, 2);
v___x_2854_ = lean_box(0);
v___x_2855_ = lean_nat_dec_lt(v_v_2829_, v_size_2853_);
if (v___x_2855_ == 0)
{
lean_object* v___x_2856_; 
lean_dec_ref(v_elimEqs_2852_);
v___x_2856_ = l_outOfBounds___redArg(v___x_2854_);
v___y_2837_ = v___x_2856_;
goto v___jp_2836_;
}
else
{
lean_object* v___x_2857_; 
v___x_2857_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2854_, v_elimEqs_2852_, v_v_2829_);
lean_dec_ref(v_elimEqs_2852_);
v___y_2837_ = v___x_2857_;
goto v___jp_2836_;
}
v___jp_2836_:
{
if (lean_obj_tag(v___y_2837_) == 1)
{
lean_object* v_val_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2850_; 
lean_dec_ref(v_p_2830_);
v_val_2838_ = lean_ctor_get(v___y_2837_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___y_2837_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2840_ = v___y_2837_;
v_isShared_2841_ = v_isSharedCheck_2850_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_val_2838_);
lean_dec(v___y_2837_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2850_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2842_, 0, v_v_2829_);
lean_ctor_set(v___x_2842_, 1, v_val_2838_);
v___x_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2843_, 0, v_k_2828_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2843_);
v___x_2845_ = v___x_2840_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2843_);
v___x_2845_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
lean_object* v___x_2847_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2845_);
v___x_2847_ = v___x_2834_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
else
{
lean_dec(v___y_2837_);
lean_del_object(v___x_2834_);
lean_dec(v_v_2829_);
lean_dec(v_k_2828_);
v_p_2815_ = v_p_2830_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_dec_ref(v_p_2830_);
lean_dec(v_v_2829_);
lean_dec(v_k_2828_);
v_a_2859_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2831_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2831_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_findVarToSubst___redArg___boxed(lean_object* v_p_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_2867_, v_a_2868_, v_a_2869_);
lean_dec_ref(v_a_2869_);
lean_dec(v_a_2868_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_findVarToSubst(lean_object* v_p_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_2872_, v_a_2873_, v_a_2881_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_findVarToSubst___boxed(lean_object* v_p_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Int_Linear_Poly_findVarToSubst(v_p_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
lean_dec(v_a_2893_);
lean_dec_ref(v_a_2892_);
lean_dec(v_a_2891_);
lean_dec_ref(v_a_2890_);
lean_dec(v_a_2889_);
lean_dec_ref(v_a_2888_);
lean_dec(v_a_2887_);
lean_dec(v_a_2886_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(lean_object* v_pred_2898_){
_start:
{
lean_object* v_c_u2081_2899_; lean_object* v_c_u2082_2900_; uint8_t v_left_2901_; lean_object* v_c_u2083_x3f_2902_; lean_object* v_p_2903_; lean_object* v_p_2904_; lean_object* v_a_2905_; lean_object* v_b_2906_; 
v_c_u2081_2899_ = lean_ctor_get(v_pred_2898_, 0);
v_c_u2082_2900_ = lean_ctor_get(v_pred_2898_, 1);
v_left_2901_ = lean_ctor_get_uint8(v_pred_2898_, sizeof(void*)*3);
v_c_u2083_x3f_2902_ = lean_ctor_get(v_pred_2898_, 2);
v_p_2903_ = lean_ctor_get(v_c_u2081_2899_, 0);
v_p_2904_ = lean_ctor_get(v_c_u2082_2900_, 0);
v_a_2905_ = l_Int_Linear_Poly_leadCoeff(v_p_2903_);
v_b_2906_ = l_Int_Linear_Poly_leadCoeff(v_p_2904_);
if (lean_obj_tag(v_c_u2083_x3f_2902_) == 0)
{
if (v_left_2901_ == 0)
{
lean_object* v___x_2907_; 
lean_dec(v_a_2905_);
v___x_2907_ = lean_nat_abs(v_b_2906_);
lean_dec(v_b_2906_);
return v___x_2907_;
}
else
{
lean_object* v___x_2908_; 
lean_dec(v_b_2906_);
v___x_2908_ = lean_nat_abs(v_a_2905_);
lean_dec(v_a_2905_);
return v___x_2908_;
}
}
else
{
lean_object* v_val_2909_; lean_object* v_d_2910_; lean_object* v_p_2911_; lean_object* v_c_2912_; 
v_val_2909_ = lean_ctor_get(v_c_u2083_x3f_2902_, 0);
v_d_2910_ = lean_ctor_get(v_val_2909_, 0);
v_p_2911_ = lean_ctor_get(v_val_2909_, 1);
v_c_2912_ = l_Int_Linear_Poly_leadCoeff(v_p_2911_);
if (v_left_2901_ == 0)
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
lean_dec(v_a_2905_);
v___x_2913_ = lean_int_mul(v_b_2906_, v_d_2910_);
v___x_2914_ = l_Int_gcd(v___x_2913_, v_c_2912_);
lean_dec(v_c_2912_);
v___x_2915_ = lean_nat_to_int(v___x_2914_);
v___x_2916_ = lean_int_ediv(v___x_2913_, v___x_2915_);
lean_dec(v___x_2915_);
lean_dec(v___x_2913_);
v___x_2917_ = l_Int_lcm(v_b_2906_, v___x_2916_);
lean_dec(v___x_2916_);
lean_dec(v_b_2906_);
return v___x_2917_;
}
else
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_dec(v_b_2906_);
v___x_2918_ = lean_int_mul(v_a_2905_, v_d_2910_);
v___x_2919_ = l_Int_gcd(v___x_2918_, v_c_2912_);
lean_dec(v_c_2912_);
v___x_2920_ = lean_nat_to_int(v___x_2919_);
v___x_2921_ = lean_int_ediv(v___x_2918_, v___x_2920_);
lean_dec(v___x_2920_);
lean_dec(v___x_2918_);
v___x_2922_ = l_Int_lcm(v_a_2905_, v___x_2921_);
lean_dec(v___x_2921_);
lean_dec(v_a_2905_);
return v___x_2922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases___boxed(lean_object* v_pred_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(v_pred_2923_);
lean_dec_ref(v_pred_2923_);
return v_res_2924_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0));
v___x_2927_ = l_Lean_stringToMessageData(v___x_2926_);
return v___x_2927_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4(void){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3));
v___x_2932_ = l_Lean_MessageData_ofFormat(v___x_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(lean_object* v_pred_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_c_u2081_2937_; lean_object* v_c_u2082_2938_; lean_object* v_c_u2083_x3f_2939_; lean_object* v___x_2940_; 
v_c_u2081_2937_ = lean_ctor_get(v_pred_2933_, 0);
lean_inc_ref(v_c_u2081_2937_);
v_c_u2082_2938_ = lean_ctor_get(v_pred_2933_, 1);
lean_inc_ref(v_c_u2082_2938_);
v_c_u2083_x3f_2939_ = lean_ctor_get(v_pred_2933_, 2);
lean_inc(v_c_u2083_x3f_2939_);
lean_dec_ref(v_pred_2933_);
v___x_2940_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_2937_, v_a_2934_, v_a_2935_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2942_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref_known(v___x_2940_, 1);
v___x_2942_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_2938_, v_a_2934_, v_a_2935_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2961_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2945_ = v___x_2942_;
v_isShared_2946_ = v_isSharedCheck_2961_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2942_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2961_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v_____do__lift_2948_; 
if (lean_obj_tag(v_c_u2083_x3f_2939_) == 1)
{
lean_object* v_val_2957_; lean_object* v___x_2958_; 
v_val_2957_ = lean_ctor_get(v_c_u2083_x3f_2939_, 0);
lean_inc(v_val_2957_);
lean_dec_ref_known(v_c_u2083_x3f_2939_, 1);
v___x_2958_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_val_2957_, v_a_2934_, v_a_2935_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
v_____do__lift_2948_ = v_a_2959_;
goto v___jp_2947_;
}
else
{
lean_del_object(v___x_2945_);
lean_dec(v_a_2943_);
lean_dec(v_a_2941_);
return v___x_2958_;
}
}
else
{
lean_object* v___x_2960_; 
lean_dec(v_c_u2083_x3f_2939_);
v___x_2960_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4);
v_____do__lift_2948_ = v___x_2960_;
goto v___jp_2947_;
}
v___jp_2947_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2955_; 
v___x_2949_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_2950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2950_, 0, v_a_2941_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v_a_2943_);
v___x_2952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
lean_ctor_set(v___x_2952_, 1, v___x_2949_);
v___x_2953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
lean_ctor_set(v___x_2953_, 1, v_____do__lift_2948_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v___x_2953_);
v___x_2955_ = v___x_2945_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2953_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
else
{
lean_dec(v_a_2941_);
lean_dec(v_c_u2083_x3f_2939_);
return v___x_2942_;
}
}
else
{
lean_dec(v_c_u2083_x3f_2939_);
lean_dec_ref(v_c_u2082_2938_);
return v___x_2940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___boxed(lean_object* v_pred_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_2962_, v_a_2963_, v_a_2964_);
lean_dec_ref(v_a_2964_);
lean_dec(v_a_2963_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(lean_object* v_pred_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_2967_, v_a_2968_, v_a_2976_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___boxed(lean_object* v_pred_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(v_pred_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec_ref(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec(v_a_2981_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(lean_object* v_h_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
switch(lean_obj_tag(v_h_2993_))
{
case 0:
{
lean_object* v_c_2997_; lean_object* v___x_2998_; 
v_c_2997_ = lean_ctor_get(v_h_2993_, 0);
lean_inc_ref(v_c_2997_);
lean_dec_ref_known(v_h_2993_, 1);
v___x_2998_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_2997_, v_a_2994_, v_a_2995_);
return v___x_2998_;
}
case 1:
{
lean_object* v_c_2999_; lean_object* v___x_3000_; 
v_c_2999_ = lean_ctor_get(v_h_2993_, 0);
lean_inc_ref(v_c_2999_);
lean_dec_ref_known(v_h_2993_, 1);
v___x_3000_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_2999_, v_a_2994_, v_a_2995_);
return v___x_3000_;
}
case 2:
{
lean_object* v_c_3001_; lean_object* v___x_3002_; 
v_c_3001_ = lean_ctor_get(v_h_2993_, 0);
lean_inc_ref(v_c_3001_);
lean_dec_ref_known(v_h_2993_, 1);
v___x_3002_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_3001_, v_a_2994_, v_a_2995_);
return v___x_3002_;
}
case 3:
{
lean_object* v_c_3003_; lean_object* v___x_3004_; 
v_c_3003_ = lean_ctor_get(v_h_2993_, 0);
lean_inc_ref(v_c_3003_);
lean_dec_ref_known(v_h_2993_, 1);
v___x_3004_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_3003_, v_a_2994_, v_a_2995_);
return v___x_3004_;
}
default: 
{
lean_object* v_c_u2081_3005_; lean_object* v_c_u2082_3006_; lean_object* v_c_u2083_3007_; lean_object* v___x_3008_; 
v_c_u2081_3005_ = lean_ctor_get(v_h_2993_, 0);
lean_inc_ref(v_c_u2081_3005_);
v_c_u2082_3006_ = lean_ctor_get(v_h_2993_, 1);
lean_inc_ref(v_c_u2082_3006_);
v_c_u2083_3007_ = lean_ctor_get(v_h_2993_, 2);
lean_inc_ref(v_c_u2083_3007_);
lean_dec_ref_known(v_h_2993_, 3);
v___x_3008_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3005_, v_a_2994_, v_a_2995_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3010_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v___x_3010_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3006_, v_a_2994_, v_a_2995_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3012_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
v___x_3012_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2083_3007_, v_a_2994_, v_a_2995_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3025_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3015_ = v___x_3012_;
v_isShared_3016_ = v_isSharedCheck_3025_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_3012_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3025_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3023_; 
v___x_3017_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3018_, 0, v_a_3009_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
lean_ctor_set(v___x_3019_, 1, v_a_3011_);
v___x_3020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
lean_ctor_set(v___x_3020_, 1, v___x_3017_);
v___x_3021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
lean_ctor_set(v___x_3021_, 1, v_a_3013_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v___x_3021_);
v___x_3023_ = v___x_3015_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
else
{
lean_dec(v_a_3011_);
lean_dec(v_a_3009_);
return v___x_3012_;
}
}
else
{
lean_dec(v_a_3009_);
lean_dec_ref(v_c_u2083_3007_);
return v___x_3010_;
}
}
else
{
lean_dec_ref(v_c_u2083_3007_);
lean_dec_ref(v_c_u2082_3006_);
return v___x_3008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg___boxed(lean_object* v_h_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3026_, v_a_3027_, v_a_3028_);
lean_dec_ref(v_a_3028_);
lean_dec(v_a_3027_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(lean_object* v_h_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3031_, v_a_3032_, v_a_3040_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___boxed(lean_object* v_h_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(v_h_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_);
lean_dec(v_a_3054_);
lean_dec_ref(v_a_3053_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec(v_a_3045_);
return v_res_3056_;
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
