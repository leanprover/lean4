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
uint8_t l_Lean_Bool_toLBool(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
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
size_t v_x_852__boxed_338_; uint8_t v_res_339_; lean_object* v_r_340_; 
v_x_852__boxed_338_ = lean_unbox_usize(v_x_336_);
lean_dec(v_x_336_);
v_res_339_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_335_, v_x_852__boxed_338_, v_x_337_);
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
size_t v_x_959__boxed_423_; uint8_t v_res_424_; lean_object* v_r_425_; 
v_x_959__boxed_423_ = lean_unbox_usize(v_x_421_);
lean_dec(v_x_421_);
v_res_424_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(v_00_u03b2_419_, v_x_420_, v_x_959__boxed_423_, v_x_422_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__0));
v___x_645_ = l_Lean_stringToMessageData(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = lean_nat_to_int(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__3));
v___x_650_ = l_Lean_stringToMessageData(v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(lean_object* v_r_651_, lean_object* v_p_652_, lean_object* v_a_653_, lean_object* v_a_654_){
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
v___x_660_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_661_ = lean_int_dec_eq(v_k_656_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_662_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
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
v___x_678_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
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
v___x_682_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
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
v___x_688_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4);
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
v___x_703_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___boxed(lean_object* v_r_716_, lean_object* v_p_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v_r_716_, v_p_717_, v_a_718_, v_a_719_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(lean_object* v_r_722_, lean_object* v_p_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v_r_722_, v_p_723_, v_a_724_, v_a_732_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___boxed(lean_object* v_r_736_, lean_object* v_p_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go(v_r_736_, v_p_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___redArg(lean_object* v_p_750_, lean_object* v_a_751_, lean_object* v_a_752_){
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
v___x_768_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
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
v___x_775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__4);
v___x_776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_771_);
v___x_778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v___x_778_, v_p_767_, v_a_751_, v_a_752_);
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
v___x_791_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg(v___x_790_, v_p_767_, v_a_751_, v_a_752_);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___redArg___boxed(lean_object* v_p_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_800_, v_a_801_, v_a_802_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp(lean_object* v_p_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_805_, v_a_806_, v_a_814_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_pp___boxed(lean_object* v_p_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Int_Internal_Linear_Poly_pp(v_p_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0(lean_object* v_a_831_, lean_object* v___x_832_, lean_object* v_x_833_){
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed(lean_object* v_a_838_, lean_object* v___x_839_, lean_object* v_x_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0(v_a_838_, v___x_839_, v_x_840_);
lean_dec(v_x_840_);
lean_dec_ref(v___x_839_);
lean_dec_ref(v_a_838_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(lean_object* v_p_842_, lean_object* v_a_843_, lean_object* v_a_844_){
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
v___f_849_ = lean_alloc_closure((void*)(l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_849_, 0, v_a_847_);
lean_closure_set(v___f_849_, 1, v___x_848_);
v___x_850_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v___f_849_, v_p_842_);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg___boxed(lean_object* v_p_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_859_, v_a_860_, v_a_861_);
lean_dec_ref(v_a_861_);
lean_dec(v_a_860_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27(lean_object* v_p_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_864_, v_a_865_, v_a_873_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr_x27___boxed(lean_object* v_p_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Int_Internal_Linear_Poly_denoteExpr_x27(v_p_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
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
v___x_895_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_896_ = lean_int_dec_eq(v___x_894_, v___x_895_);
lean_dec(v___x_894_);
return v___x_896_;
}
else
{
lean_object* v_d_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v_d_897_ = lean_ctor_get(v_c_890_, 0);
v___x_898_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_pp_go___redArg___closed__2);
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
v___x_912_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_911_, v_a_907_, v_a_908_);
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
v___x_990_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_989_, v_a_985_, v_a_986_);
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
v___x_1001_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
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
lean_object* v_k_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; uint8_t v___x_1200_; 
v_k_1197_ = lean_ctor_get(v_p_1196_, 0);
v___x_1198_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1199_ = lean_int_dec_eq(v_k_1197_, v___x_1198_);
v___x_1200_ = lean_bool_not(v___x_1199_);
return v___x_1200_;
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; uint8_t v___x_1207_; 
v___x_1201_ = l_Int_Internal_Linear_Poly_getConst(v_p_1196_);
v___x_1202_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v_p_1196_);
v___x_1203_ = lean_nat_to_int(v___x_1202_);
v___x_1204_ = lean_int_emod(v___x_1201_, v___x_1203_);
lean_dec(v___x_1203_);
lean_dec(v___x_1201_);
v___x_1205_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1206_ = lean_int_dec_eq(v___x_1204_, v___x_1205_);
lean_dec(v___x_1204_);
v___x_1207_ = lean_bool_not(v___x_1206_);
return v___x_1207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial___boxed(lean_object* v_c_1208_){
_start:
{
uint8_t v_res_1209_; lean_object* v_r_1210_; 
v_res_1209_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(v_c_1208_);
lean_dec_ref(v_c_1208_);
v_r_1210_ = lean_box(v_res_1209_);
return v_r_1210_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0));
v___x_1213_ = l_Lean_stringToMessageData(v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(lean_object* v_c_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v_p_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1235_; 
v_p_1218_ = lean_ctor_get(v_c_1214_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_c_1214_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v_c_1214_, 1);
lean_dec(v_unused_1236_);
v___x_1220_ = v_c_1214_;
v_isShared_1221_ = v_isSharedCheck_1235_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_p_1218_);
lean_dec(v_c_1214_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1235_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1218_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1234_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1234_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1234_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1227_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1);
if (v_isShared_1221_ == 0)
{
lean_ctor_set_tag(v___x_1220_, 7);
lean_ctor_set(v___x_1220_, 1, v___x_1227_);
lean_ctor_set(v___x_1220_, 0, v_a_1223_);
v___x_1229_ = v___x_1220_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1223_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1231_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1229_);
v___x_1231_ = v___x_1225_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
lean_del_object(v___x_1220_);
return v___x_1222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___boxed(lean_object* v_c_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1237_, v_a_1238_, v_a_1239_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(lean_object* v_c_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1242_, v_a_1243_, v_a_1251_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___boxed(lean_object* v_c_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(v_c_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec(v_a_1256_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(lean_object* v_c_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1268_, v_a_1269_, v_a_1272_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref_known(v___x_1275_, 1);
v___x_1277_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1278_ = l_Lean_indentD(v_a_1276_);
v___x_1279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1279_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
return v___x_1280_;
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
v_a_1281_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1275_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1275_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
lean_dec(v_a_1290_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(lean_object* v_00_u03b1_1297_, lean_object* v_c_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1298_, v_a_1299_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1311_, lean_object* v_c_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(v_00_u03b1_1311_, v_c_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec(v_a_1313_);
return v_res_1324_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1326_ = l_Lean_mkIntLit(v___x_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(lean_object* v_c_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_p_1331_; lean_object* v___x_1332_; 
v_p_1331_ = lean_ctor_get(v_c_1327_, 0);
lean_inc_ref(v_p_1331_);
lean_dec_ref(v_c_1327_);
v___x_1332_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1331_, v_a_1328_, v_a_1329_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1343_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1343_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1343_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1337_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1338_ = l_Lean_mkIntEq(v_a_1333_, v___x_1337_);
v___x_1339_ = l_Lean_mkNot(v___x_1338_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1339_);
v___x_1341_ = v___x_1335_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
else
{
return v___x_1332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1344_, v_a_1345_, v_a_1346_);
lean_dec_ref(v_a_1346_);
lean_dec(v_a_1345_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(lean_object* v_c_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1349_, v_a_1350_, v_a_1358_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___boxed(lean_object* v_c_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(v_c_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert___boxed(lean_object* v_c_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_00___x40___internal___hyg_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = lean_grind_cutsat_assert_le(v_c_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
return v_res_1399_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(lean_object* v_c_1400_){
_start:
{
lean_object* v_p_1401_; 
v_p_1401_ = lean_ctor_get(v_c_1400_, 0);
if (lean_obj_tag(v_p_1401_) == 0)
{
lean_object* v_k_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v_k_1402_ = lean_ctor_get(v_p_1401_, 0);
v___x_1403_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1404_ = lean_int_dec_le(v_k_1402_, v___x_1403_);
return v___x_1404_;
}
else
{
uint8_t v___x_1405_; 
v___x_1405_ = 0;
return v___x_1405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial___boxed(lean_object* v_c_1406_){
_start:
{
uint8_t v_res_1407_; lean_object* v_r_1408_; 
v_res_1407_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_c_1406_);
lean_dec_ref(v_c_1406_);
v_r_1408_ = lean_box(v_res_1407_);
return v_r_1408_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0));
v___x_1411_ = l_Lean_stringToMessageData(v___x_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(lean_object* v_c_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v_p_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1433_; 
v_p_1416_ = lean_ctor_get(v_c_1412_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_c_1412_);
if (v_isSharedCheck_1433_ == 0)
{
lean_object* v_unused_1434_; 
v_unused_1434_ = lean_ctor_get(v_c_1412_, 1);
lean_dec(v_unused_1434_);
v___x_1418_ = v_c_1412_;
v_isShared_1419_ = v_isSharedCheck_1433_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_p_1416_);
lean_dec(v_c_1412_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1433_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1416_, v_a_1413_, v_a_1414_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1432_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1432_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1432_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1425_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1);
if (v_isShared_1419_ == 0)
{
lean_ctor_set_tag(v___x_1418_, 7);
lean_ctor_set(v___x_1418_, 1, v___x_1425_);
lean_ctor_set(v___x_1418_, 0, v_a_1421_);
v___x_1427_ = v___x_1418_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1421_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1429_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1427_);
v___x_1429_ = v___x_1423_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
else
{
lean_del_object(v___x_1418_);
return v___x_1420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___boxed(lean_object* v_c_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1435_, v_a_1436_, v_a_1437_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(lean_object* v_c_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1440_, v_a_1441_, v_a_1449_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___boxed(lean_object* v_c_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(v_c_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
lean_dec(v_a_1455_);
lean_dec(v_a_1454_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(lean_object* v_c_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_p_1470_; lean_object* v___x_1471_; 
v_p_1470_ = lean_ctor_get(v_c_1466_, 0);
lean_inc_ref(v_p_1470_);
lean_dec_ref(v_c_1466_);
v___x_1471_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1470_, v_a_1467_, v_a_1468_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1481_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1474_ = v___x_1471_;
v_isShared_1475_ = v_isSharedCheck_1481_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1471_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1481_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1476_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1477_ = l_Lean_mkIntLE(v_a_1472_, v___x_1476_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 0, v___x_1477_);
v___x_1479_ = v___x_1474_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
else
{
return v___x_1471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1482_, v_a_1483_, v_a_1484_);
lean_dec_ref(v_a_1484_);
lean_dec(v_a_1483_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(lean_object* v_c_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1487_, v_a_1488_, v_a_1496_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___boxed(lean_object* v_c_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(v_c_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_);
lean_dec(v_a_1510_);
lean_dec_ref(v_a_1509_);
lean_dec(v_a_1508_);
lean_dec_ref(v_a_1507_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec(v_a_1501_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(lean_object* v_c_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1513_, v_a_1514_, v_a_1517_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1520_, 1);
v___x_1522_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1523_ = l_Lean_indentD(v_a_1521_);
v___x_1524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1522_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1524_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1525_;
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
v_a_1526_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1520_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1520_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(lean_object* v_00_u03b1_1542_, lean_object* v_c_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1543_, v_a_1544_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1556_, lean_object* v_c_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(v_00_u03b1_1556_, v_c_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
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
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(lean_object* v_c_1570_){
_start:
{
lean_object* v_p_1571_; 
v_p_1571_ = lean_ctor_get(v_c_1570_, 0);
if (lean_obj_tag(v_p_1571_) == 0)
{
lean_object* v_k_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; 
v_k_1572_ = lean_ctor_get(v_p_1571_, 0);
v___x_1573_ = lean_obj_once(&l_Int_Internal_Linear_Poly_isZero___closed__0, &l_Int_Internal_Linear_Poly_isZero___closed__0_once, _init_l_Int_Internal_Linear_Poly_isZero___closed__0);
v___x_1574_ = lean_int_dec_eq(v_k_1572_, v___x_1573_);
return v___x_1574_;
}
else
{
uint8_t v___x_1575_; 
v___x_1575_ = 0;
return v___x_1575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial___boxed(lean_object* v_c_1576_){
_start:
{
uint8_t v_res_1577_; lean_object* v_r_1578_; 
v_res_1577_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(v_c_1576_);
lean_dec_ref(v_c_1576_);
v_r_1578_ = lean_box(v_res_1577_);
return v_r_1578_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0));
v___x_1581_ = l_Lean_stringToMessageData(v___x_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object* v_c_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_p_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1603_; 
v_p_1586_ = lean_ctor_get(v_c_1582_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_c_1582_);
if (v_isSharedCheck_1603_ == 0)
{
lean_object* v_unused_1604_; 
v_unused_1604_ = lean_ctor_get(v_c_1582_, 1);
lean_dec(v_unused_1604_);
v___x_1588_ = v_c_1582_;
v_isShared_1589_ = v_isSharedCheck_1603_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_p_1586_);
lean_dec(v_c_1582_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1603_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Int_Internal_Linear_Poly_pp___redArg(v_p_1586_, v_a_1583_, v_a_1584_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1602_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1602_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1602_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1595_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1);
if (v_isShared_1589_ == 0)
{
lean_ctor_set_tag(v___x_1588_, 7);
lean_ctor_set(v___x_1588_, 1, v___x_1595_);
lean_ctor_set(v___x_1588_, 0, v_a_1591_);
v___x_1597_ = v___x_1588_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1591_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1599_; 
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1597_);
v___x_1599_ = v___x_1593_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_del_object(v___x_1588_);
return v___x_1590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___boxed(lean_object* v_c_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1605_, v_a_1606_, v_a_1607_);
lean_dec_ref(v_a_1607_);
lean_dec(v_a_1606_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(lean_object* v_c_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1610_, v_a_1611_, v_a_1619_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___boxed(lean_object* v_c_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(v_c_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec(v_a_1624_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(lean_object* v_c_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v_p_1640_; lean_object* v___x_1641_; 
v_p_1640_ = lean_ctor_get(v_c_1636_, 0);
lean_inc_ref(v_p_1640_);
lean_dec_ref(v_c_1636_);
v___x_1641_ = l_Int_Internal_Linear_Poly_denoteExpr_x27___redArg(v_p_1640_, v_a_1637_, v_a_1638_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1651_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1651_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1651_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1646_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1647_ = l_Lean_mkIntEq(v_a_1642_, v___x_1646_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1647_);
v___x_1649_ = v___x_1644_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
else
{
return v___x_1641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1652_, v_a_1653_, v_a_1654_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(lean_object* v_c_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1657_, v_a_1658_, v_a_1666_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___boxed(lean_object* v_c_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(v_c_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec(v_a_1671_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(lean_object* v_c_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1683_, v_a_1684_, v_a_1687_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref_known(v___x_1690_, 1);
v___x_1692_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1693_ = l_Lean_indentD(v_a_1691_);
v___x_1694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1694_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
return v___x_1695_;
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
v_a_1696_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1690_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1690_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
lean_dec(v_a_1705_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(lean_object* v_00_u03b1_1712_, lean_object* v_c_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_1713_, v_a_1714_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1726_, lean_object* v_c_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(v_00_u03b1_1726_, v_c_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec(v_a_1728_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(lean_object* v_x_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1741_, v_a_1742_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1761_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1761_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1761_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v_occurs_1749_; lean_object* v_size_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v_occurs_1749_ = lean_ctor_get(v_a_1745_, 12);
lean_inc_ref(v_occurs_1749_);
lean_dec(v_a_1745_);
v_size_1750_ = lean_ctor_get(v_occurs_1749_, 2);
v___x_1751_ = lean_box(1);
v___x_1752_ = lean_nat_dec_lt(v_x_1740_, v_size_1750_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
lean_dec_ref(v_occurs_1749_);
v___x_1753_ = l_outOfBounds___redArg(v___x_1751_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1753_);
v___x_1755_ = v___x_1747_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1757_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1751_, v_occurs_1749_, v_x_1740_);
lean_dec_ref(v_occurs_1749_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1757_);
v___x_1759_ = v___x_1747_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
v_a_1762_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1744_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1744_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg___boxed(lean_object* v_x_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_1770_, v_a_1771_, v_a_1772_);
lean_dec_ref(v_a_1772_);
lean_dec(v_a_1771_);
lean_dec(v_x_1770_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(lean_object* v_x_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_1775_, v_a_1776_, v_a_1784_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___boxed(lean_object* v_x_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(v_x_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec_ref(v_a_1793_);
lean_dec(v_a_1792_);
lean_dec_ref(v_a_1791_);
lean_dec(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec(v_x_1788_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(lean_object* v_k_1801_, lean_object* v_v_1802_, lean_object* v_t_1803_){
_start:
{
if (lean_obj_tag(v_t_1803_) == 0)
{
lean_object* v_size_1804_; lean_object* v_k_1805_; lean_object* v_v_1806_; lean_object* v_l_1807_; lean_object* v_r_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_2089_; 
v_size_1804_ = lean_ctor_get(v_t_1803_, 0);
v_k_1805_ = lean_ctor_get(v_t_1803_, 1);
v_v_1806_ = lean_ctor_get(v_t_1803_, 2);
v_l_1807_ = lean_ctor_get(v_t_1803_, 3);
v_r_1808_ = lean_ctor_get(v_t_1803_, 4);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_t_1803_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_1810_ = v_t_1803_;
v_isShared_1811_ = v_isSharedCheck_2089_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_r_1808_);
lean_inc(v_l_1807_);
lean_inc(v_v_1806_);
lean_inc(v_k_1805_);
lean_inc(v_size_1804_);
lean_dec(v_t_1803_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_2089_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
uint8_t v___x_1812_; 
v___x_1812_ = lean_nat_dec_lt(v_k_1801_, v_k_1805_);
if (v___x_1812_ == 0)
{
uint8_t v___x_1813_; 
v___x_1813_ = lean_nat_dec_eq(v_k_1801_, v_k_1805_);
if (v___x_1813_ == 0)
{
lean_object* v_impl_1814_; lean_object* v___x_1815_; 
lean_dec(v_size_1804_);
v_impl_1814_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_1801_, v_v_1802_, v_r_1808_);
v___x_1815_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1807_) == 0)
{
lean_object* v_size_1816_; lean_object* v_size_1817_; lean_object* v_k_1818_; lean_object* v_v_1819_; lean_object* v_l_1820_; lean_object* v_r_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; 
v_size_1816_ = lean_ctor_get(v_l_1807_, 0);
v_size_1817_ = lean_ctor_get(v_impl_1814_, 0);
lean_inc(v_size_1817_);
v_k_1818_ = lean_ctor_get(v_impl_1814_, 1);
lean_inc(v_k_1818_);
v_v_1819_ = lean_ctor_get(v_impl_1814_, 2);
lean_inc(v_v_1819_);
v_l_1820_ = lean_ctor_get(v_impl_1814_, 3);
lean_inc(v_l_1820_);
v_r_1821_ = lean_ctor_get(v_impl_1814_, 4);
lean_inc(v_r_1821_);
v___x_1822_ = lean_unsigned_to_nat(3u);
v___x_1823_ = lean_nat_mul(v___x_1822_, v_size_1816_);
v___x_1824_ = lean_nat_dec_lt(v___x_1823_, v_size_1817_);
lean_dec(v___x_1823_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
lean_dec(v_r_1821_);
lean_dec(v_l_1820_);
lean_dec(v_v_1819_);
lean_dec(v_k_1818_);
v___x_1825_ = lean_nat_add(v___x_1815_, v_size_1816_);
v___x_1826_ = lean_nat_add(v___x_1825_, v_size_1817_);
lean_dec(v_size_1817_);
lean_dec(v___x_1825_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 4, v_impl_1814_);
lean_ctor_set(v___x_1810_, 0, v___x_1826_);
v___x_1828_ = v___x_1810_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_k_1805_);
lean_ctor_set(v_reuseFailAlloc_1829_, 2, v_v_1806_);
lean_ctor_set(v_reuseFailAlloc_1829_, 3, v_l_1807_);
lean_ctor_set(v_reuseFailAlloc_1829_, 4, v_impl_1814_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
else
{
lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1893_; 
v_isSharedCheck_1893_ = !lean_is_exclusive(v_impl_1814_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; lean_object* v_unused_1895_; lean_object* v_unused_1896_; lean_object* v_unused_1897_; lean_object* v_unused_1898_; 
v_unused_1894_ = lean_ctor_get(v_impl_1814_, 4);
lean_dec(v_unused_1894_);
v_unused_1895_ = lean_ctor_get(v_impl_1814_, 3);
lean_dec(v_unused_1895_);
v_unused_1896_ = lean_ctor_get(v_impl_1814_, 2);
lean_dec(v_unused_1896_);
v_unused_1897_ = lean_ctor_get(v_impl_1814_, 1);
lean_dec(v_unused_1897_);
v_unused_1898_ = lean_ctor_get(v_impl_1814_, 0);
lean_dec(v_unused_1898_);
v___x_1831_ = v_impl_1814_;
v_isShared_1832_ = v_isSharedCheck_1893_;
goto v_resetjp_1830_;
}
else
{
lean_dec(v_impl_1814_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1893_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v_size_1833_; lean_object* v_k_1834_; lean_object* v_v_1835_; lean_object* v_l_1836_; lean_object* v_r_1837_; lean_object* v_size_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v_size_1833_ = lean_ctor_get(v_l_1820_, 0);
v_k_1834_ = lean_ctor_get(v_l_1820_, 1);
v_v_1835_ = lean_ctor_get(v_l_1820_, 2);
v_l_1836_ = lean_ctor_get(v_l_1820_, 3);
v_r_1837_ = lean_ctor_get(v_l_1820_, 4);
v_size_1838_ = lean_ctor_get(v_r_1821_, 0);
v___x_1839_ = lean_unsigned_to_nat(2u);
v___x_1840_ = lean_nat_mul(v___x_1839_, v_size_1838_);
v___x_1841_ = lean_nat_dec_lt(v_size_1833_, v___x_1840_);
lean_dec(v___x_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1869_; 
lean_inc(v_r_1837_);
lean_inc(v_l_1836_);
lean_inc(v_v_1835_);
lean_inc(v_k_1834_);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_l_1820_);
if (v_isSharedCheck_1869_ == 0)
{
lean_object* v_unused_1870_; lean_object* v_unused_1871_; lean_object* v_unused_1872_; lean_object* v_unused_1873_; lean_object* v_unused_1874_; 
v_unused_1870_ = lean_ctor_get(v_l_1820_, 4);
lean_dec(v_unused_1870_);
v_unused_1871_ = lean_ctor_get(v_l_1820_, 3);
lean_dec(v_unused_1871_);
v_unused_1872_ = lean_ctor_get(v_l_1820_, 2);
lean_dec(v_unused_1872_);
v_unused_1873_ = lean_ctor_get(v_l_1820_, 1);
lean_dec(v_unused_1873_);
v_unused_1874_ = lean_ctor_get(v_l_1820_, 0);
lean_dec(v_unused_1874_);
v___x_1843_ = v_l_1820_;
v_isShared_1844_ = v_isSharedCheck_1869_;
goto v_resetjp_1842_;
}
else
{
lean_dec(v_l_1820_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1869_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1859_; 
v___x_1845_ = lean_nat_add(v___x_1815_, v_size_1816_);
v___x_1846_ = lean_nat_add(v___x_1845_, v_size_1817_);
lean_dec(v_size_1817_);
if (lean_obj_tag(v_l_1836_) == 0)
{
lean_object* v_size_1867_; 
v_size_1867_ = lean_ctor_get(v_l_1836_, 0);
lean_inc(v_size_1867_);
v___y_1859_ = v_size_1867_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_unsigned_to_nat(0u);
v___y_1859_ = v___x_1868_;
goto v___jp_1858_;
}
v___jp_1847_:
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1851_ = lean_nat_add(v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec(v___y_1849_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 4, v_r_1821_);
lean_ctor_set(v___x_1843_, 3, v_r_1837_);
lean_ctor_set(v___x_1843_, 2, v_v_1819_);
lean_ctor_set(v___x_1843_, 1, v_k_1818_);
lean_ctor_set(v___x_1843_, 0, v___x_1851_);
v___x_1853_ = v___x_1843_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_k_1818_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_v_1819_);
lean_ctor_set(v_reuseFailAlloc_1857_, 3, v_r_1837_);
lean_ctor_set(v_reuseFailAlloc_1857_, 4, v_r_1821_);
v___x_1853_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1855_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 4, v___x_1853_);
lean_ctor_set(v___x_1831_, 3, v___y_1848_);
lean_ctor_set(v___x_1831_, 2, v_v_1835_);
lean_ctor_set(v___x_1831_, 1, v_k_1834_);
lean_ctor_set(v___x_1831_, 0, v___x_1846_);
v___x_1855_ = v___x_1831_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_k_1834_);
lean_ctor_set(v_reuseFailAlloc_1856_, 2, v_v_1835_);
lean_ctor_set(v_reuseFailAlloc_1856_, 3, v___y_1848_);
lean_ctor_set(v_reuseFailAlloc_1856_, 4, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
v___jp_1858_:
{
lean_object* v___x_1860_; lean_object* v___x_1862_; 
v___x_1860_ = lean_nat_add(v___x_1845_, v___y_1859_);
lean_dec(v___y_1859_);
lean_dec(v___x_1845_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 4, v_l_1836_);
lean_ctor_set(v___x_1810_, 0, v___x_1860_);
v___x_1862_ = v___x_1810_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1860_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_k_1805_);
lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_v_1806_);
lean_ctor_set(v_reuseFailAlloc_1866_, 3, v_l_1807_);
lean_ctor_set(v_reuseFailAlloc_1866_, 4, v_l_1836_);
v___x_1862_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1863_; 
v___x_1863_ = lean_nat_add(v___x_1815_, v_size_1838_);
if (lean_obj_tag(v_r_1837_) == 0)
{
lean_object* v_size_1864_; 
v_size_1864_ = lean_ctor_get(v_r_1837_, 0);
lean_inc(v_size_1864_);
v___y_1848_ = v___x_1862_;
v___y_1849_ = v___x_1863_;
v___y_1850_ = v_size_1864_;
goto v___jp_1847_;
}
else
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_unsigned_to_nat(0u);
v___y_1848_ = v___x_1862_;
v___y_1849_ = v___x_1863_;
v___y_1850_ = v___x_1865_;
goto v___jp_1847_;
}
}
}
}
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
lean_del_object(v___x_1810_);
v___x_1875_ = lean_nat_add(v___x_1815_, v_size_1816_);
v___x_1876_ = lean_nat_add(v___x_1875_, v_size_1817_);
lean_dec(v_size_1817_);
v___x_1877_ = lean_nat_add(v___x_1875_, v_size_1833_);
lean_dec(v___x_1875_);
lean_inc_ref(v_l_1807_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 4, v_l_1820_);
lean_ctor_set(v___x_1831_, 3, v_l_1807_);
lean_ctor_set(v___x_1831_, 2, v_v_1806_);
lean_ctor_set(v___x_1831_, 1, v_k_1805_);
lean_ctor_set(v___x_1831_, 0, v___x_1877_);
v___x_1879_ = v___x_1831_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_k_1805_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_v_1806_);
lean_ctor_set(v_reuseFailAlloc_1892_, 3, v_l_1807_);
lean_ctor_set(v_reuseFailAlloc_1892_, 4, v_l_1820_);
v___x_1879_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
v_isSharedCheck_1886_ = !lean_is_exclusive(v_l_1807_);
if (v_isSharedCheck_1886_ == 0)
{
lean_object* v_unused_1887_; lean_object* v_unused_1888_; lean_object* v_unused_1889_; lean_object* v_unused_1890_; lean_object* v_unused_1891_; 
v_unused_1887_ = lean_ctor_get(v_l_1807_, 4);
lean_dec(v_unused_1887_);
v_unused_1888_ = lean_ctor_get(v_l_1807_, 3);
lean_dec(v_unused_1888_);
v_unused_1889_ = lean_ctor_get(v_l_1807_, 2);
lean_dec(v_unused_1889_);
v_unused_1890_ = lean_ctor_get(v_l_1807_, 1);
lean_dec(v_unused_1890_);
v_unused_1891_ = lean_ctor_get(v_l_1807_, 0);
lean_dec(v_unused_1891_);
v___x_1881_ = v_l_1807_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_dec(v_l_1807_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 4, v_r_1821_);
lean_ctor_set(v___x_1881_, 3, v___x_1879_);
lean_ctor_set(v___x_1881_, 2, v_v_1819_);
lean_ctor_set(v___x_1881_, 1, v_k_1818_);
lean_ctor_set(v___x_1881_, 0, v___x_1876_);
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1876_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_k_1818_);
lean_ctor_set(v_reuseFailAlloc_1885_, 2, v_v_1819_);
lean_ctor_set(v_reuseFailAlloc_1885_, 3, v___x_1879_);
lean_ctor_set(v_reuseFailAlloc_1885_, 4, v_r_1821_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1899_; 
v_l_1899_ = lean_ctor_get(v_impl_1814_, 3);
lean_inc(v_l_1899_);
if (lean_obj_tag(v_l_1899_) == 0)
{
lean_object* v_r_1900_; lean_object* v_k_1901_; lean_object* v_v_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1925_; 
v_r_1900_ = lean_ctor_get(v_impl_1814_, 4);
v_k_1901_ = lean_ctor_get(v_impl_1814_, 1);
v_v_1902_ = lean_ctor_get(v_impl_1814_, 2);
v_isSharedCheck_1925_ = !lean_is_exclusive(v_impl_1814_);
if (v_isSharedCheck_1925_ == 0)
{
lean_object* v_unused_1926_; lean_object* v_unused_1927_; 
v_unused_1926_ = lean_ctor_get(v_impl_1814_, 3);
lean_dec(v_unused_1926_);
v_unused_1927_ = lean_ctor_get(v_impl_1814_, 0);
lean_dec(v_unused_1927_);
v___x_1904_ = v_impl_1814_;
v_isShared_1905_ = v_isSharedCheck_1925_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_r_1900_);
lean_inc(v_v_1902_);
lean_inc(v_k_1901_);
lean_dec(v_impl_1814_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1925_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v_k_1906_; lean_object* v_v_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1921_; 
v_k_1906_ = lean_ctor_get(v_l_1899_, 1);
v_v_1907_ = lean_ctor_get(v_l_1899_, 2);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_l_1899_);
if (v_isSharedCheck_1921_ == 0)
{
lean_object* v_unused_1922_; lean_object* v_unused_1923_; lean_object* v_unused_1924_; 
v_unused_1922_ = lean_ctor_get(v_l_1899_, 4);
lean_dec(v_unused_1922_);
v_unused_1923_ = lean_ctor_get(v_l_1899_, 3);
lean_dec(v_unused_1923_);
v_unused_1924_ = lean_ctor_get(v_l_1899_, 0);
lean_dec(v_unused_1924_);
v___x_1909_ = v_l_1899_;
v_isShared_1910_ = v_isSharedCheck_1921_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_v_1907_);
lean_inc(v_k_1906_);
lean_dec(v_l_1899_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1921_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1911_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1900_, 2);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 4, v_r_1900_);
lean_ctor_set(v___x_1909_, 3, v_r_1900_);
lean_ctor_set(v___x_1909_, 2, v_v_1806_);
lean_ctor_set(v___x_1909_, 1, v_k_1805_);
lean_ctor_set(v___x_1909_, 0, v___x_1815_);
v___x_1913_ = v___x_1909_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_k_1805_);
lean_ctor_set(v_reuseFailAlloc_1920_, 2, v_v_1806_);
lean_ctor_set(v_reuseFailAlloc_1920_, 3, v_r_1900_);
lean_ctor_set(v_reuseFailAlloc_1920_, 4, v_r_1900_);
v___x_1913_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1915_; 
lean_inc(v_r_1900_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 3, v_r_1900_);
lean_ctor_set(v___x_1904_, 0, v___x_1815_);
v___x_1915_ = v___x_1904_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_k_1901_);
lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_v_1902_);
lean_ctor_set(v_reuseFailAlloc_1919_, 3, v_r_1900_);
lean_ctor_set(v_reuseFailAlloc_1919_, 4, v_r_1900_);
v___x_1915_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1917_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 4, v___x_1915_);
lean_ctor_set(v___x_1810_, 3, v___x_1913_);
lean_ctor_set(v___x_1810_, 2, v_v_1907_);
lean_ctor_set(v___x_1810_, 1, v_k_1906_);
lean_ctor_set(v___x_1810_, 0, v___x_1911_);
v___x_1917_ = v___x_1810_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_k_1906_);
lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_v_1907_);
lean_ctor_set(v_reuseFailAlloc_1918_, 3, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1918_, 4, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
}
else
{
lean_object* v_r_1928_; 
v_r_1928_ = lean_ctor_get(v_impl_1814_, 4);
lean_inc(v_r_1928_);
if (lean_obj_tag(v_r_1928_) == 0)
{
lean_object* v_k_1929_; lean_object* v_v_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1941_; 
v_k_1929_ = lean_ctor_get(v_impl_1814_, 1);
v_v_1930_ = lean_ctor_get(v_impl_1814_, 2);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_impl_1814_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; lean_object* v_unused_1943_; lean_object* v_unused_1944_; 
v_unused_1942_ = lean_ctor_get(v_impl_1814_, 4);
lean_dec(v_unused_1942_);
v_unused_1943_ = lean_ctor_get(v_impl_1814_, 3);
lean_dec(v_unused_1943_);
v_unused_1944_ = lean_ctor_get(v_impl_1814_, 0);
lean_dec(v_unused_1944_);
v___x_1932_ = v_impl_1814_;
v_isShared_1933_ = v_isSharedCheck_1941_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_v_1930_);
lean_inc(v_k_1929_);
lean_dec(v_impl_1814_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1941_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1934_ = lean_unsigned_to_nat(3u);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 4, v_l_1899_);
lean_ctor_set(v___x_1932_, 2, v_v_1806_);
lean_ctor_set(v___x_1932_, 1, v_k_1805_);
lean_ctor_set(v___x_1932_, 0, v___x_1815_);
v___x_1936_ = v___x_1932_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_k_1805_);
lean_ctor_set(v_reuseFailAlloc_1940_, 2, v_v_1806_);
lean_ctor_set(v_reuseFailAlloc_1940_, 3, v_l_1899_);
lean_ctor_set(v_reuseFailAlloc_1940_, 4, v_l_1899_);
v___x_1936_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1938_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 4, v_r_1928_);
lean_ctor_set(v___x_1810_, 3, v___x_1936_);
lean_ctor_set(v___x_1810_, 2, v_v_1930_);
lean_ctor_set(v___x_1810_, 1, v_k_1929_);
lean_ctor_set(v___x_1810_, 0, v___x_1934_);
v___x_1938_ = v___x_1810_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_k_1929_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v_v_1930_);
lean_ctor_set(v_reuseFailAlloc_1939_, 3, v___x_1936_);
lean_ctor_set(v_reuseFailAlloc_1939_, 4, v_r_1928_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1945_ = lean_unsigned_to_nat(2u);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 4, v_impl_1814_);
lean_ctor_set(v___x_1810_, 3, v_r_1928_);
lean_ctor_set(v___x_1810_, 0, v___x_1945_);
v___x_1947_ = v___x_1810_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_k_1805_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v_v_1806_);
lean_ctor_set(v_reuseFailAlloc_1948_, 3, v_r_1928_);
lean_ctor_set(v_reuseFailAlloc_1948_, 4, v_impl_1814_);
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
}
else
{
lean_object* v___x_1950_; 
lean_dec(v_v_1806_);
lean_dec(v_k_1805_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 2, v_v_1802_);
lean_ctor_set(v___x_1810_, 1, v_k_1801_);
v___x_1950_ = v___x_1810_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_size_1804_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_k_1801_);
lean_ctor_set(v_reuseFailAlloc_1951_, 2, v_v_1802_);
lean_ctor_set(v_reuseFailAlloc_1951_, 3, v_l_1807_);
lean_ctor_set(v_reuseFailAlloc_1951_, 4, v_r_1808_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
else
{
lean_object* v_impl_1952_; lean_object* v___x_1953_; 
lean_dec(v_size_1804_);
v_impl_1952_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_1801_, v_v_1802_, v_l_1807_);
v___x_1953_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1808_) == 0)
{
lean_object* v_size_1954_; lean_object* v_size_1955_; lean_object* v_k_1956_; lean_object* v_v_1957_; lean_object* v_l_1958_; lean_object* v_r_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v_size_1954_ = lean_ctor_get(v_r_1808_, 0);
v_size_1955_ = lean_ctor_get(v_impl_1952_, 0);
lean_inc(v_size_1955_);
v_k_1956_ = lean_ctor_get(v_impl_1952_, 1);
lean_inc(v_k_1956_);
v_v_1957_ = lean_ctor_get(v_impl_1952_, 2);
lean_inc(v_v_1957_);
v_l_1958_ = lean_ctor_get(v_impl_1952_, 3);
lean_inc(v_l_1958_);
v_r_1959_ = lean_ctor_get(v_impl_1952_, 4);
lean_inc(v_r_1959_);
v___x_1960_ = lean_unsigned_to_nat(3u);
v___x_1961_ = lean_nat_mul(v___x_1960_, v_size_1954_);
v___x_1962_ = lean_nat_dec_lt(v___x_1961_, v_size_1955_);
lean_dec(v___x_1961_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1966_; 
lean_dec(v_r_1959_);
lean_dec(v_l_1958_);
lean_dec(v_v_1957_);
lean_dec(v_k_1956_);
v___x_1963_ = lean_nat_add(v___x_1953_, v_size_1955_);
lean_dec(v_size_1955_);
v___x_1964_ = lean_nat_add(v___x_1963_, v_size_1954_);
lean_dec(v___x_1963_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 3, v_impl_1952_);
lean_ctor_set(v___x_1810_, 0, v___x_1964_);
v___x_1966_ = v___x_1810_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_k_1805_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v_v_1806_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v_impl_1952_);
lean_ctor_set(v_reuseFailAlloc_1967_, 4, v_r_1808_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
else
{
lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_2033_; 
v_isSharedCheck_2033_ = !lean_is_exclusive(v_impl_1952_);
if (v_isSharedCheck_2033_ == 0)
{
lean_object* v_unused_2034_; lean_object* v_unused_2035_; lean_object* v_unused_2036_; lean_object* v_unused_2037_; lean_object* v_unused_2038_; 
v_unused_2034_ = lean_ctor_get(v_impl_1952_, 4);
lean_dec(v_unused_2034_);
v_unused_2035_ = lean_ctor_get(v_impl_1952_, 3);
lean_dec(v_unused_2035_);
v_unused_2036_ = lean_ctor_get(v_impl_1952_, 2);
lean_dec(v_unused_2036_);
v_unused_2037_ = lean_ctor_get(v_impl_1952_, 1);
lean_dec(v_unused_2037_);
v_unused_2038_ = lean_ctor_get(v_impl_1952_, 0);
lean_dec(v_unused_2038_);
v___x_1969_ = v_impl_1952_;
v_isShared_1970_ = v_isSharedCheck_2033_;
goto v_resetjp_1968_;
}
else
{
lean_dec(v_impl_1952_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_2033_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v_size_1971_; lean_object* v_size_1972_; lean_object* v_k_1973_; lean_object* v_v_1974_; lean_object* v_l_1975_; lean_object* v_r_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v_size_1971_ = lean_ctor_get(v_l_1958_, 0);
v_size_1972_ = lean_ctor_get(v_r_1959_, 0);
v_k_1973_ = lean_ctor_get(v_r_1959_, 1);
v_v_1974_ = lean_ctor_get(v_r_1959_, 2);
v_l_1975_ = lean_ctor_get(v_r_1959_, 3);
v_r_1976_ = lean_ctor_get(v_r_1959_, 4);
v___x_1977_ = lean_unsigned_to_nat(2u);
v___x_1978_ = lean_nat_mul(v___x_1977_, v_size_1971_);
v___x_1979_ = lean_nat_dec_lt(v_size_1972_, v___x_1978_);
lean_dec(v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2008_; 
lean_inc(v_r_1976_);
lean_inc(v_l_1975_);
lean_inc(v_v_1974_);
lean_inc(v_k_1973_);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_r_1959_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; lean_object* v_unused_2010_; lean_object* v_unused_2011_; lean_object* v_unused_2012_; lean_object* v_unused_2013_; 
v_unused_2009_ = lean_ctor_get(v_r_1959_, 4);
lean_dec(v_unused_2009_);
v_unused_2010_ = lean_ctor_get(v_r_1959_, 3);
lean_dec(v_unused_2010_);
v_unused_2011_ = lean_ctor_get(v_r_1959_, 2);
lean_dec(v_unused_2011_);
v_unused_2012_ = lean_ctor_get(v_r_1959_, 1);
lean_dec(v_unused_2012_);
v_unused_2013_ = lean_ctor_get(v_r_1959_, 0);
lean_dec(v_unused_2013_);
v___x_1981_ = v_r_1959_;
v_isShared_1982_ = v_isSharedCheck_2008_;
goto v_resetjp_1980_;
}
else
{
lean_dec(v_r_1959_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2008_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___x_1996_; lean_object* v___y_1998_; 
v___x_1983_ = lean_nat_add(v___x_1953_, v_size_1955_);
lean_dec(v_size_1955_);
v___x_1984_ = lean_nat_add(v___x_1983_, v_size_1954_);
lean_dec(v___x_1983_);
v___x_1996_ = lean_nat_add(v___x_1953_, v_size_1971_);
if (lean_obj_tag(v_l_1975_) == 0)
{
lean_object* v_size_2006_; 
v_size_2006_ = lean_ctor_get(v_l_1975_, 0);
lean_inc(v_size_2006_);
v___y_1998_ = v_size_2006_;
goto v___jp_1997_;
}
else
{
lean_object* v___x_2007_; 
v___x_2007_ = lean_unsigned_to_nat(0u);
v___y_1998_ = v___x_2007_;
goto v___jp_1997_;
}
v___jp_1985_:
{
lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1989_ = lean_nat_add(v___y_1986_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec(v___y_1986_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 4, v_r_1808_);
lean_ctor_set(v___x_1981_, 3, v_r_1976_);
lean_ctor_set(v___x_1981_, 2, v_v_1806_);
lean_ctor_set(v___x_1981_, 1, v_k_1805_);
lean_ctor_set(v___x_1981_, 0, v___x_1989_);
v___x_1991_ = v___x_1981_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_k_1805_);
lean_ctor_set(v_reuseFailAlloc_1995_, 2, v_v_1806_);
lean_ctor_set(v_reuseFailAlloc_1995_, 3, v_r_1976_);
lean_ctor_set(v_reuseFailAlloc_1995_, 4, v_r_1808_);
v___x_1991_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1993_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 4, v___x_1991_);
lean_ctor_set(v___x_1969_, 3, v___y_1987_);
lean_ctor_set(v___x_1969_, 2, v_v_1974_);
lean_ctor_set(v___x_1969_, 1, v_k_1973_);
lean_ctor_set(v___x_1969_, 0, v___x_1984_);
v___x_1993_ = v___x_1969_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_k_1973_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_v_1974_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v___y_1987_);
lean_ctor_set(v_reuseFailAlloc_1994_, 4, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
v___jp_1997_:
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1999_ = lean_nat_add(v___x_1996_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec(v___x_1996_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 4, v_l_1975_);
lean_ctor_set(v___x_1810_, 3, v_l_1958_);
lean_ctor_set(v___x_1810_, 2, v_v_1957_);
lean_ctor_set(v___x_1810_, 1, v_k_1956_);
lean_ctor_set(v___x_1810_, 0, v___x_1999_);
v___x_2001_ = v___x_1810_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_k_1956_);
lean_ctor_set(v_reuseFailAlloc_2005_, 2, v_v_1957_);
lean_ctor_set(v_reuseFailAlloc_2005_, 3, v_l_1958_);
lean_ctor_set(v_reuseFailAlloc_2005_, 4, v_l_1975_);
v___x_2001_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_nat_add(v___x_1953_, v_size_1954_);
if (lean_obj_tag(v_r_1976_) == 0)
{
lean_object* v_size_2003_; 
v_size_2003_ = lean_ctor_get(v_r_1976_, 0);
lean_inc(v_size_2003_);
v___y_1986_ = v___x_2002_;
v___y_1987_ = v___x_2001_;
v___y_1988_ = v_size_2003_;
goto v___jp_1985_;
}
else
{
lean_object* v___x_2004_; 
v___x_2004_ = lean_unsigned_to_nat(0u);
v___y_1986_ = v___x_2002_;
v___y_1987_ = v___x_2001_;
v___y_1988_ = v___x_2004_;
goto v___jp_1985_;
}
}
}
}
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
lean_del_object(v___x_1810_);
v___x_2014_ = lean_nat_add(v___x_1953_, v_size_1955_);
lean_dec(v_size_1955_);
v___x_2015_ = lean_nat_add(v___x_2014_, v_size_1954_);
lean_dec(v___x_2014_);
v___x_2016_ = lean_nat_add(v___x_1953_, v_size_1954_);
v___x_2017_ = lean_nat_add(v___x_2016_, v_size_1972_);
lean_dec(v___x_2016_);
lean_inc_ref(v_r_1808_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 4, v_r_1808_);
lean_ctor_set(v___x_1969_, 3, v_r_1959_);
lean_ctor_set(v___x_1969_, 2, v_v_1806_);
lean_ctor_set(v___x_1969_, 1, v_k_1805_);
lean_ctor_set(v___x_1969_, 0, v___x_2017_);
v___x_2019_ = v___x_1969_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_k_1805_);
lean_ctor_set(v_reuseFailAlloc_2032_, 2, v_v_1806_);
lean_ctor_set(v_reuseFailAlloc_2032_, 3, v_r_1959_);
lean_ctor_set(v_reuseFailAlloc_2032_, 4, v_r_1808_);
v___x_2019_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
v_isSharedCheck_2026_ = !lean_is_exclusive(v_r_1808_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; lean_object* v_unused_2028_; lean_object* v_unused_2029_; lean_object* v_unused_2030_; lean_object* v_unused_2031_; 
v_unused_2027_ = lean_ctor_get(v_r_1808_, 4);
lean_dec(v_unused_2027_);
v_unused_2028_ = lean_ctor_get(v_r_1808_, 3);
lean_dec(v_unused_2028_);
v_unused_2029_ = lean_ctor_get(v_r_1808_, 2);
lean_dec(v_unused_2029_);
v_unused_2030_ = lean_ctor_get(v_r_1808_, 1);
lean_dec(v_unused_2030_);
v_unused_2031_ = lean_ctor_get(v_r_1808_, 0);
lean_dec(v_unused_2031_);
v___x_2021_ = v_r_1808_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_dec(v_r_1808_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 4, v___x_2019_);
lean_ctor_set(v___x_2021_, 3, v_l_1958_);
lean_ctor_set(v___x_2021_, 2, v_v_1957_);
lean_ctor_set(v___x_2021_, 1, v_k_1956_);
lean_ctor_set(v___x_2021_, 0, v___x_2015_);
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2015_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_k_1956_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_v_1957_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v_l_1958_);
lean_ctor_set(v_reuseFailAlloc_2025_, 4, v___x_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2039_; 
v_l_2039_ = lean_ctor_get(v_impl_1952_, 3);
lean_inc(v_l_2039_);
if (lean_obj_tag(v_l_2039_) == 0)
{
lean_object* v_r_2040_; lean_object* v_k_2041_; lean_object* v_v_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2053_; 
v_r_2040_ = lean_ctor_get(v_impl_1952_, 4);
v_k_2041_ = lean_ctor_get(v_impl_1952_, 1);
v_v_2042_ = lean_ctor_get(v_impl_1952_, 2);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_impl_1952_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; lean_object* v_unused_2055_; 
v_unused_2054_ = lean_ctor_get(v_impl_1952_, 3);
lean_dec(v_unused_2054_);
v_unused_2055_ = lean_ctor_get(v_impl_1952_, 0);
lean_dec(v_unused_2055_);
v___x_2044_ = v_impl_1952_;
v_isShared_2045_ = v_isSharedCheck_2053_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_r_2040_);
lean_inc(v_v_2042_);
lean_inc(v_k_2041_);
lean_dec(v_impl_1952_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2053_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2046_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2040_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 3, v_r_2040_);
lean_ctor_set(v___x_2044_, 2, v_v_1806_);
lean_ctor_set(v___x_2044_, 1, v_k_1805_);
lean_ctor_set(v___x_2044_, 0, v___x_1953_);
v___x_2048_ = v___x_2044_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_k_1805_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v_v_1806_);
lean_ctor_set(v_reuseFailAlloc_2052_, 3, v_r_2040_);
lean_ctor_set(v_reuseFailAlloc_2052_, 4, v_r_2040_);
v___x_2048_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2050_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 4, v___x_2048_);
lean_ctor_set(v___x_1810_, 3, v_l_2039_);
lean_ctor_set(v___x_1810_, 2, v_v_2042_);
lean_ctor_set(v___x_1810_, 1, v_k_2041_);
lean_ctor_set(v___x_1810_, 0, v___x_2046_);
v___x_2050_ = v___x_1810_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_k_2041_);
lean_ctor_set(v_reuseFailAlloc_2051_, 2, v_v_2042_);
lean_ctor_set(v_reuseFailAlloc_2051_, 3, v_l_2039_);
lean_ctor_set(v_reuseFailAlloc_2051_, 4, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
else
{
lean_object* v_r_2056_; 
v_r_2056_ = lean_ctor_get(v_impl_1952_, 4);
lean_inc(v_r_2056_);
if (lean_obj_tag(v_r_2056_) == 0)
{
lean_object* v_k_2057_; lean_object* v_v_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2081_; 
v_k_2057_ = lean_ctor_get(v_impl_1952_, 1);
v_v_2058_ = lean_ctor_get(v_impl_1952_, 2);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_impl_1952_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; lean_object* v_unused_2083_; lean_object* v_unused_2084_; 
v_unused_2082_ = lean_ctor_get(v_impl_1952_, 4);
lean_dec(v_unused_2082_);
v_unused_2083_ = lean_ctor_get(v_impl_1952_, 3);
lean_dec(v_unused_2083_);
v_unused_2084_ = lean_ctor_get(v_impl_1952_, 0);
lean_dec(v_unused_2084_);
v___x_2060_ = v_impl_1952_;
v_isShared_2061_ = v_isSharedCheck_2081_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_v_2058_);
lean_inc(v_k_2057_);
lean_dec(v_impl_1952_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2081_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v_k_2062_; lean_object* v_v_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2077_; 
v_k_2062_ = lean_ctor_get(v_r_2056_, 1);
v_v_2063_ = lean_ctor_get(v_r_2056_, 2);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_r_2056_);
if (v_isSharedCheck_2077_ == 0)
{
lean_object* v_unused_2078_; lean_object* v_unused_2079_; lean_object* v_unused_2080_; 
v_unused_2078_ = lean_ctor_get(v_r_2056_, 4);
lean_dec(v_unused_2078_);
v_unused_2079_ = lean_ctor_get(v_r_2056_, 3);
lean_dec(v_unused_2079_);
v_unused_2080_ = lean_ctor_get(v_r_2056_, 0);
lean_dec(v_unused_2080_);
v___x_2065_ = v_r_2056_;
v_isShared_2066_ = v_isSharedCheck_2077_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_v_2063_);
lean_inc(v_k_2062_);
lean_dec(v_r_2056_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2077_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_unsigned_to_nat(3u);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 4, v_l_2039_);
lean_ctor_set(v___x_2065_, 3, v_l_2039_);
lean_ctor_set(v___x_2065_, 2, v_v_2058_);
lean_ctor_set(v___x_2065_, 1, v_k_2057_);
lean_ctor_set(v___x_2065_, 0, v___x_1953_);
v___x_2069_ = v___x_2065_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_k_2057_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_v_2058_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v_l_2039_);
lean_ctor_set(v_reuseFailAlloc_2076_, 4, v_l_2039_);
v___x_2069_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2071_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 4, v_l_2039_);
lean_ctor_set(v___x_2060_, 2, v_v_1806_);
lean_ctor_set(v___x_2060_, 1, v_k_1805_);
lean_ctor_set(v___x_2060_, 0, v___x_1953_);
v___x_2071_ = v___x_2060_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_k_1805_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_v_1806_);
lean_ctor_set(v_reuseFailAlloc_2075_, 3, v_l_2039_);
lean_ctor_set(v_reuseFailAlloc_2075_, 4, v_l_2039_);
v___x_2071_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2073_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 4, v___x_2071_);
lean_ctor_set(v___x_1810_, 3, v___x_2069_);
lean_ctor_set(v___x_1810_, 2, v_v_2063_);
lean_ctor_set(v___x_1810_, 1, v_k_2062_);
lean_ctor_set(v___x_1810_, 0, v___x_2067_);
v___x_2073_ = v___x_1810_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_k_2062_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_v_2063_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2085_ = lean_unsigned_to_nat(2u);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 4, v_r_2056_);
lean_ctor_set(v___x_1810_, 3, v_impl_1952_);
lean_ctor_set(v___x_1810_, 0, v___x_2085_);
v___x_2087_ = v___x_1810_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_k_1805_);
lean_ctor_set(v_reuseFailAlloc_2088_, 2, v_v_1806_);
lean_ctor_set(v_reuseFailAlloc_2088_, 3, v_impl_1952_);
lean_ctor_set(v_reuseFailAlloc_2088_, 4, v_r_2056_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = lean_unsigned_to_nat(1u);
v___x_2091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
lean_ctor_set(v___x_2091_, 1, v_k_1801_);
lean_ctor_set(v___x_2091_, 2, v_v_1802_);
lean_ctor_set(v___x_2091_, 3, v_t_1803_);
lean_ctor_set(v___x_2091_, 4, v_t_1803_);
return v___x_2091_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(lean_object* v_k_2092_, lean_object* v_t_2093_){
_start:
{
if (lean_obj_tag(v_t_2093_) == 0)
{
lean_object* v_k_2094_; lean_object* v_l_2095_; lean_object* v_r_2096_; uint8_t v___x_2097_; 
v_k_2094_ = lean_ctor_get(v_t_2093_, 1);
v_l_2095_ = lean_ctor_get(v_t_2093_, 3);
v_r_2096_ = lean_ctor_get(v_t_2093_, 4);
v___x_2097_ = lean_nat_dec_lt(v_k_2092_, v_k_2094_);
if (v___x_2097_ == 0)
{
uint8_t v___x_2098_; 
v___x_2098_ = lean_nat_dec_eq(v_k_2092_, v_k_2094_);
if (v___x_2098_ == 0)
{
v_t_2093_ = v_r_2096_;
goto _start;
}
else
{
return v___x_2098_;
}
}
else
{
v_t_2093_ = v_l_2095_;
goto _start;
}
}
else
{
uint8_t v___x_2101_; 
v___x_2101_ = 0;
return v___x_2101_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg___boxed(lean_object* v_k_2102_, lean_object* v_t_2103_){
_start:
{
uint8_t v_res_2104_; lean_object* v_r_2105_; 
v_res_2104_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2102_, v_t_2103_);
lean_dec(v_t_2103_);
lean_dec(v_k_2102_);
v_r_2105_ = lean_box(v_res_2104_);
return v_r_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(lean_object* v_y_2106_, lean_object* v_x_2107_, size_t v_x_2108_, size_t v_x_2109_){
_start:
{
if (lean_obj_tag(v_x_2107_) == 0)
{
lean_object* v_cs_2110_; size_t v_j_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
v_cs_2110_ = lean_ctor_get(v_x_2107_, 0);
v_j_2111_ = lean_usize_shift_right(v_x_2108_, v_x_2109_);
v___x_2112_ = lean_usize_to_nat(v_j_2111_);
v___x_2113_ = lean_array_get_size(v_cs_2110_);
v___x_2114_ = lean_nat_dec_lt(v___x_2112_, v___x_2113_);
if (v___x_2114_ == 0)
{
lean_dec(v___x_2112_);
lean_dec(v_y_2106_);
return v_x_2107_;
}
else
{
lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2132_; 
lean_inc_ref(v_cs_2110_);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_x_2107_);
if (v_isSharedCheck_2132_ == 0)
{
lean_object* v_unused_2133_; 
v_unused_2133_ = lean_ctor_get(v_x_2107_, 0);
lean_dec(v_unused_2133_);
v___x_2116_ = v_x_2107_;
v_isShared_2117_ = v_isSharedCheck_2132_;
goto v_resetjp_2115_;
}
else
{
lean_dec(v_x_2107_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2132_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
size_t v___x_2118_; size_t v___x_2119_; size_t v___x_2120_; size_t v_i_2121_; size_t v___x_2122_; size_t v_shift_2123_; lean_object* v_v_2124_; lean_object* v___x_2125_; lean_object* v_xs_x27_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2118_ = ((size_t)1ULL);
v___x_2119_ = lean_usize_shift_left(v___x_2118_, v_x_2109_);
v___x_2120_ = lean_usize_sub(v___x_2119_, v___x_2118_);
v_i_2121_ = lean_usize_land(v_x_2108_, v___x_2120_);
v___x_2122_ = ((size_t)5ULL);
v_shift_2123_ = lean_usize_sub(v_x_2109_, v___x_2122_);
v_v_2124_ = lean_array_fget(v_cs_2110_, v___x_2112_);
v___x_2125_ = lean_box(0);
v_xs_x27_2126_ = lean_array_fset(v_cs_2110_, v___x_2112_, v___x_2125_);
v___x_2127_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2106_, v_v_2124_, v_i_2121_, v_shift_2123_);
v___x_2128_ = lean_array_fset(v_xs_x27_2126_, v___x_2112_, v___x_2127_);
lean_dec(v___x_2112_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2128_);
v___x_2130_ = v___x_2116_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
else
{
lean_object* v_vs_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; uint8_t v___x_2137_; 
v_vs_2134_ = lean_ctor_get(v_x_2107_, 0);
v___x_2135_ = lean_usize_to_nat(v_x_2108_);
v___x_2136_ = lean_array_get_size(v_vs_2134_);
v___x_2137_ = lean_nat_dec_lt(v___x_2135_, v___x_2136_);
if (v___x_2137_ == 0)
{
lean_dec(v___x_2135_);
lean_dec(v_y_2106_);
return v_x_2107_;
}
else
{
lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2152_; 
lean_inc_ref(v_vs_2134_);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_x_2107_);
if (v_isSharedCheck_2152_ == 0)
{
lean_object* v_unused_2153_; 
v_unused_2153_ = lean_ctor_get(v_x_2107_, 0);
lean_dec(v_unused_2153_);
v___x_2139_ = v_x_2107_;
v_isShared_2140_ = v_isSharedCheck_2152_;
goto v_resetjp_2138_;
}
else
{
lean_dec(v_x_2107_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2152_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v_v_2141_; lean_object* v___x_2142_; lean_object* v_xs_x27_2143_; lean_object* v___y_2145_; uint8_t v___x_2150_; 
v_v_2141_ = lean_array_fget(v_vs_2134_, v___x_2135_);
v___x_2142_ = lean_box(0);
v_xs_x27_2143_ = lean_array_fset(v_vs_2134_, v___x_2135_, v___x_2142_);
v___x_2150_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2106_, v_v_2141_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2106_, v___x_2142_, v_v_2141_);
v___y_2145_ = v___x_2151_;
goto v___jp_2144_;
}
else
{
lean_dec(v_y_2106_);
v___y_2145_ = v_v_2141_;
goto v___jp_2144_;
}
v___jp_2144_:
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2146_ = lean_array_fset(v_xs_x27_2143_, v___x_2135_, v___y_2145_);
lean_dec(v___x_2135_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2146_);
v___x_2148_ = v___x_2139_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_, lean_object* v_x_2157_){
_start:
{
size_t v_x_4533__boxed_2158_; size_t v_x_4534__boxed_2159_; lean_object* v_res_2160_; 
v_x_4533__boxed_2158_ = lean_unbox_usize(v_x_2156_);
lean_dec(v_x_2156_);
v_x_4534__boxed_2159_ = lean_unbox_usize(v_x_2157_);
lean_dec(v_x_2157_);
v_res_2160_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2154_, v_x_2155_, v_x_4533__boxed_2158_, v_x_4534__boxed_2159_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(lean_object* v_y_2161_, lean_object* v_t_2162_, lean_object* v_i_2163_){
_start:
{
lean_object* v_root_2164_; lean_object* v_tail_2165_; lean_object* v_size_2166_; size_t v_shift_2167_; lean_object* v_tailOff_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2195_; 
v_root_2164_ = lean_ctor_get(v_t_2162_, 0);
v_tail_2165_ = lean_ctor_get(v_t_2162_, 1);
v_size_2166_ = lean_ctor_get(v_t_2162_, 2);
v_shift_2167_ = lean_ctor_get_usize(v_t_2162_, 4);
v_tailOff_2168_ = lean_ctor_get(v_t_2162_, 3);
v_isSharedCheck_2195_ = !lean_is_exclusive(v_t_2162_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2170_ = v_t_2162_;
v_isShared_2171_ = v_isSharedCheck_2195_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_tailOff_2168_);
lean_inc(v_size_2166_);
lean_inc(v_tail_2165_);
lean_inc(v_root_2164_);
lean_dec(v_t_2162_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2195_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
uint8_t v___x_2172_; 
v___x_2172_ = lean_nat_dec_le(v_tailOff_2168_, v_i_2163_);
if (v___x_2172_ == 0)
{
size_t v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2173_ = lean_usize_of_nat(v_i_2163_);
v___x_2174_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2161_, v_root_2164_, v___x_2173_, v_shift_2167_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2174_);
v___x_2176_ = v___x_2170_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_tail_2165_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_size_2166_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v_tailOff_2168_);
lean_ctor_set_usize(v_reuseFailAlloc_2177_, 4, v_shift_2167_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2178_ = lean_nat_sub(v_i_2163_, v_tailOff_2168_);
v___x_2179_ = lean_array_get_size(v_tail_2165_);
v___x_2180_ = lean_nat_dec_lt(v___x_2178_, v___x_2179_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2182_; 
lean_dec(v___x_2178_);
lean_dec(v_y_2161_);
if (v_isShared_2171_ == 0)
{
v___x_2182_ = v___x_2170_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_root_2164_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_tail_2165_);
lean_ctor_set(v_reuseFailAlloc_2183_, 2, v_size_2166_);
lean_ctor_set(v_reuseFailAlloc_2183_, 3, v_tailOff_2168_);
lean_ctor_set_usize(v_reuseFailAlloc_2183_, 4, v_shift_2167_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
else
{
lean_object* v_v_2184_; lean_object* v___x_2185_; lean_object* v_xs_x27_2186_; lean_object* v___y_2188_; uint8_t v___x_2193_; 
v_v_2184_ = lean_array_fget(v_tail_2165_, v___x_2178_);
v___x_2185_ = lean_box(0);
v_xs_x27_2186_ = lean_array_fset(v_tail_2165_, v___x_2178_, v___x_2185_);
v___x_2193_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2161_, v_v_2184_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2161_, v___x_2185_, v_v_2184_);
v___y_2188_ = v___x_2194_;
goto v___jp_2187_;
}
else
{
lean_dec(v_y_2161_);
v___y_2188_ = v_v_2184_;
goto v___jp_2187_;
}
v___jp_2187_:
{
lean_object* v___x_2189_; lean_object* v___x_2191_; 
v___x_2189_ = lean_array_fset(v_xs_x27_2186_, v___x_2178_, v___y_2188_);
lean_dec(v___x_2178_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 1, v___x_2189_);
v___x_2191_ = v___x_2170_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_root_2164_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2192_, 2, v_size_2166_);
lean_ctor_set(v_reuseFailAlloc_2192_, 3, v_tailOff_2168_);
lean_ctor_set_usize(v_reuseFailAlloc_2192_, 4, v_shift_2167_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2___boxed(lean_object* v_y_2196_, lean_object* v_t_2197_, lean_object* v_i_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2196_, v_t_2197_, v_i_2198_);
lean_dec(v_i_2198_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(lean_object* v_y_2200_, lean_object* v_x_2201_, lean_object* v_s_2202_){
_start:
{
lean_object* v_vars_2203_; lean_object* v_varMap_2204_; lean_object* v_vars_x27_2205_; lean_object* v_varMap_x27_2206_; lean_object* v_natToIntMap_2207_; lean_object* v_natDef_2208_; lean_object* v_dvds_2209_; lean_object* v_lowers_2210_; lean_object* v_uppers_2211_; lean_object* v_diseqs_2212_; lean_object* v_elimEqs_2213_; lean_object* v_elimStack_2214_; lean_object* v_occurs_2215_; lean_object* v_assignment_2216_; lean_object* v_nextCnstrId_2217_; uint8_t v_caseSplits_2218_; lean_object* v_conflict_x3f_2219_; lean_object* v_diseqSplits_2220_; lean_object* v_divMod_2221_; lean_object* v_toIntIds_2222_; lean_object* v_toIntInfos_2223_; lean_object* v_toIntTermMap_2224_; lean_object* v_toIntVarMap_2225_; uint8_t v_usedCommRing_2226_; lean_object* v_nonlinearOccs_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2235_; 
v_vars_2203_ = lean_ctor_get(v_s_2202_, 0);
v_varMap_2204_ = lean_ctor_get(v_s_2202_, 1);
v_vars_x27_2205_ = lean_ctor_get(v_s_2202_, 2);
v_varMap_x27_2206_ = lean_ctor_get(v_s_2202_, 3);
v_natToIntMap_2207_ = lean_ctor_get(v_s_2202_, 4);
v_natDef_2208_ = lean_ctor_get(v_s_2202_, 5);
v_dvds_2209_ = lean_ctor_get(v_s_2202_, 6);
v_lowers_2210_ = lean_ctor_get(v_s_2202_, 7);
v_uppers_2211_ = lean_ctor_get(v_s_2202_, 8);
v_diseqs_2212_ = lean_ctor_get(v_s_2202_, 9);
v_elimEqs_2213_ = lean_ctor_get(v_s_2202_, 10);
v_elimStack_2214_ = lean_ctor_get(v_s_2202_, 11);
v_occurs_2215_ = lean_ctor_get(v_s_2202_, 12);
v_assignment_2216_ = lean_ctor_get(v_s_2202_, 13);
v_nextCnstrId_2217_ = lean_ctor_get(v_s_2202_, 14);
v_caseSplits_2218_ = lean_ctor_get_uint8(v_s_2202_, sizeof(void*)*23);
v_conflict_x3f_2219_ = lean_ctor_get(v_s_2202_, 15);
v_diseqSplits_2220_ = lean_ctor_get(v_s_2202_, 16);
v_divMod_2221_ = lean_ctor_get(v_s_2202_, 17);
v_toIntIds_2222_ = lean_ctor_get(v_s_2202_, 18);
v_toIntInfos_2223_ = lean_ctor_get(v_s_2202_, 19);
v_toIntTermMap_2224_ = lean_ctor_get(v_s_2202_, 20);
v_toIntVarMap_2225_ = lean_ctor_get(v_s_2202_, 21);
v_usedCommRing_2226_ = lean_ctor_get_uint8(v_s_2202_, sizeof(void*)*23 + 1);
v_nonlinearOccs_2227_ = lean_ctor_get(v_s_2202_, 22);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_s_2202_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2229_ = v_s_2202_;
v_isShared_2230_ = v_isSharedCheck_2235_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_nonlinearOccs_2227_);
lean_inc(v_toIntVarMap_2225_);
lean_inc(v_toIntTermMap_2224_);
lean_inc(v_toIntInfos_2223_);
lean_inc(v_toIntIds_2222_);
lean_inc(v_divMod_2221_);
lean_inc(v_diseqSplits_2220_);
lean_inc(v_conflict_x3f_2219_);
lean_inc(v_nextCnstrId_2217_);
lean_inc(v_assignment_2216_);
lean_inc(v_occurs_2215_);
lean_inc(v_elimStack_2214_);
lean_inc(v_elimEqs_2213_);
lean_inc(v_diseqs_2212_);
lean_inc(v_uppers_2211_);
lean_inc(v_lowers_2210_);
lean_inc(v_dvds_2209_);
lean_inc(v_natDef_2208_);
lean_inc(v_natToIntMap_2207_);
lean_inc(v_varMap_x27_2206_);
lean_inc(v_vars_x27_2205_);
lean_inc(v_varMap_2204_);
lean_inc(v_vars_2203_);
lean_dec(v_s_2202_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2235_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2231_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2200_, v_occurs_2215_, v_x_2201_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 12, v___x_2231_);
v___x_2233_ = v___x_2229_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_vars_2203_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_varMap_2204_);
lean_ctor_set(v_reuseFailAlloc_2234_, 2, v_vars_x27_2205_);
lean_ctor_set(v_reuseFailAlloc_2234_, 3, v_varMap_x27_2206_);
lean_ctor_set(v_reuseFailAlloc_2234_, 4, v_natToIntMap_2207_);
lean_ctor_set(v_reuseFailAlloc_2234_, 5, v_natDef_2208_);
lean_ctor_set(v_reuseFailAlloc_2234_, 6, v_dvds_2209_);
lean_ctor_set(v_reuseFailAlloc_2234_, 7, v_lowers_2210_);
lean_ctor_set(v_reuseFailAlloc_2234_, 8, v_uppers_2211_);
lean_ctor_set(v_reuseFailAlloc_2234_, 9, v_diseqs_2212_);
lean_ctor_set(v_reuseFailAlloc_2234_, 10, v_elimEqs_2213_);
lean_ctor_set(v_reuseFailAlloc_2234_, 11, v_elimStack_2214_);
lean_ctor_set(v_reuseFailAlloc_2234_, 12, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2234_, 13, v_assignment_2216_);
lean_ctor_set(v_reuseFailAlloc_2234_, 14, v_nextCnstrId_2217_);
lean_ctor_set(v_reuseFailAlloc_2234_, 15, v_conflict_x3f_2219_);
lean_ctor_set(v_reuseFailAlloc_2234_, 16, v_diseqSplits_2220_);
lean_ctor_set(v_reuseFailAlloc_2234_, 17, v_divMod_2221_);
lean_ctor_set(v_reuseFailAlloc_2234_, 18, v_toIntIds_2222_);
lean_ctor_set(v_reuseFailAlloc_2234_, 19, v_toIntInfos_2223_);
lean_ctor_set(v_reuseFailAlloc_2234_, 20, v_toIntTermMap_2224_);
lean_ctor_set(v_reuseFailAlloc_2234_, 21, v_toIntVarMap_2225_);
lean_ctor_set(v_reuseFailAlloc_2234_, 22, v_nonlinearOccs_2227_);
lean_ctor_set_uint8(v_reuseFailAlloc_2234_, sizeof(void*)*23, v_caseSplits_2218_);
lean_ctor_set_uint8(v_reuseFailAlloc_2234_, sizeof(void*)*23 + 1, v_usedCommRing_2226_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed(lean_object* v_y_2236_, lean_object* v_x_2237_, lean_object* v_s_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(v_y_2236_, v_x_2237_, v_s_2238_);
lean_dec(v_x_2237_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(lean_object* v_x_2240_, lean_object* v_y_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2240_, v_a_2242_, v_a_2243_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2258_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2248_ = v___x_2245_;
v_isShared_2249_ = v_isSharedCheck_2258_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2245_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2258_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
uint8_t v___x_2250_; 
v___x_2250_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2241_, v_a_2246_);
lean_dec(v_a_2246_);
if (v___x_2250_ == 0)
{
lean_object* v___f_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_del_object(v___x_2248_);
v___f_2251_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2251_, 0, v_y_2241_);
lean_closure_set(v___f_2251_, 1, v_x_2240_);
v___x_2252_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2253_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2252_, v___f_2251_, v_a_2242_);
return v___x_2253_;
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2256_; 
lean_dec(v_y_2241_);
lean_dec(v_x_2240_);
v___x_2254_ = lean_box(0);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v___x_2254_);
v___x_2256_ = v___x_2248_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v_y_2241_);
lean_dec(v_x_2240_);
v_a_2259_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2245_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2245_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___boxed(lean_object* v_x_2267_, lean_object* v_y_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2267_, v_y_2268_, v_a_2269_, v_a_2270_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc(lean_object* v_x_2273_, lean_object* v_y_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2273_, v_y_2274_, v_a_2275_, v_a_2283_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___boxed(lean_object* v_x_2287_, lean_object* v_y_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc(v_x_2287_, v_y_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec(v_a_2289_);
return v_res_2300_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(lean_object* v_00_u03b2_2301_, lean_object* v_k_2302_, lean_object* v_t_2303_){
_start:
{
uint8_t v___x_2304_; 
v___x_2304_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2302_, v_t_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2305_, lean_object* v_k_2306_, lean_object* v_t_2307_){
_start:
{
uint8_t v_res_2308_; lean_object* v_r_2309_; 
v_res_2308_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(v_00_u03b2_2305_, v_k_2306_, v_t_2307_);
lean_dec(v_t_2307_);
lean_dec(v_k_2306_);
v_r_2309_ = lean_box(v_res_2308_);
return v_r_2309_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1(lean_object* v_00_u03b2_2310_, lean_object* v_k_2311_, lean_object* v_v_2312_, lean_object* v_t_2313_, lean_object* v_hl_2314_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2311_, v_v_2312_, v_t_2313_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(lean_object* v_y_2316_, lean_object* v_p_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
if (lean_obj_tag(v_p_2317_) == 1)
{
lean_object* v_v_2321_; lean_object* v_p_2322_; lean_object* v___x_2323_; 
v_v_2321_ = lean_ctor_get(v_p_2317_, 1);
lean_inc(v_v_2321_);
v_p_2322_ = lean_ctor_get(v_p_2317_, 2);
lean_inc_ref(v_p_2322_);
lean_dec_ref_known(v_p_2317_, 3);
lean_inc(v_y_2316_);
v___x_2323_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_v_2321_, v_y_2316_, v_a_2318_, v_a_2319_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_dec_ref_known(v___x_2323_, 1);
v_p_2317_ = v_p_2322_;
goto _start;
}
else
{
lean_dec_ref(v_p_2322_);
lean_dec(v_y_2316_);
return v___x_2323_;
}
}
else
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_dec_ref(v_p_2317_);
lean_dec(v_y_2316_);
v___x_2325_ = lean_box(0);
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
return v___x_2326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg___boxed(lean_object* v_y_2327_, lean_object* v_p_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2327_, v_p_2328_, v_a_2329_, v_a_2330_);
lean_dec_ref(v_a_2330_);
lean_dec(v_a_2329_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(lean_object* v_y_2333_, lean_object* v_p_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_y_2333_, v_p_2334_, v_a_2335_, v_a_2343_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___boxed(lean_object* v_y_2347_, lean_object* v_p_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go(v_y_2347_, v_p_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec(v_a_2356_);
lean_dec_ref(v_a_2355_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec(v_a_2350_);
lean_dec(v_a_2349_);
return v_res_2360_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = ((lean_object*)(l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__0));
v___x_2363_ = l_Lean_stringToMessageData(v___x_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg(lean_object* v_p_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
if (lean_obj_tag(v_p_2364_) == 1)
{
lean_object* v_v_2371_; lean_object* v_p_2372_; lean_object* v___x_2373_; 
v_v_2371_ = lean_ctor_get(v_p_2364_, 1);
lean_inc(v_v_2371_);
v_p_2372_ = lean_ctor_get(v_p_2364_, 2);
lean_inc_ref(v_p_2372_);
lean_dec_ref_known(v_p_2364_, 3);
v___x_2373_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_updateOccs_go___redArg(v_v_2371_, v_p_2372_, v_a_2365_, v_a_2368_);
return v___x_2373_;
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
lean_dec_ref(v_p_2364_);
v___x_2374_ = lean_obj_once(&l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1, &l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1_once, _init_l_Int_Internal_Linear_Poly_updateOccs___redArg___closed__1);
v___x_2375_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2374_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
return v___x_2375_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg___boxed(lean_object* v_p_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs(lean_object* v_p_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_2384_, v_a_2385_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_updateOccs___boxed(lean_object* v_p_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Int_Internal_Linear_Poly_updateOccs(v_p_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
lean_dec(v_a_2399_);
lean_dec(v_a_2398_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go_spec__0(lean_object* v_a_2410_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Rat_ofInt(v_a_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(lean_object* v_a_2412_, lean_object* v_v_2413_, lean_object* v_a_2414_){
_start:
{
if (lean_obj_tag(v_a_2414_) == 0)
{
lean_object* v_k_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2424_; 
v_k_2415_ = lean_ctor_get(v_a_2414_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_a_2414_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2417_ = v_a_2414_;
v_isShared_2418_ = v_isSharedCheck_2424_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_k_2415_);
lean_dec(v_a_2414_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2424_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2419_ = l_Rat_ofInt(v_k_2415_);
v___x_2420_ = l_Rat_add(v_v_2413_, v___x_2419_);
if (v_isShared_2418_ == 0)
{
lean_ctor_set_tag(v___x_2417_, 1);
lean_ctor_set(v___x_2417_, 0, v___x_2420_);
v___x_2422_ = v___x_2417_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
else
{
lean_object* v_k_2425_; lean_object* v_v_2426_; lean_object* v_p_2427_; lean_object* v_size_2428_; uint8_t v___x_2429_; 
v_k_2425_ = lean_ctor_get(v_a_2414_, 0);
lean_inc(v_k_2425_);
v_v_2426_ = lean_ctor_get(v_a_2414_, 1);
lean_inc(v_v_2426_);
v_p_2427_ = lean_ctor_get(v_a_2414_, 2);
lean_inc_ref(v_p_2427_);
lean_dec_ref_known(v_a_2414_, 3);
v_size_2428_ = lean_ctor_get(v_a_2412_, 2);
v___x_2429_ = lean_nat_dec_lt(v_v_2426_, v_size_2428_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; 
lean_dec_ref(v_p_2427_);
lean_dec(v_v_2426_);
lean_dec(v_k_2425_);
lean_dec_ref(v_v_2413_);
v___x_2430_ = lean_box(0);
return v___x_2430_;
}
else
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2431_ = l_Rat_ofInt(v_k_2425_);
v___x_2432_ = l_instInhabitedRat;
v___x_2433_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2432_, v_a_2412_, v_v_2426_);
lean_dec(v_v_2426_);
v___x_2434_ = l_Rat_mul(v___x_2431_, v___x_2433_);
lean_dec_ref(v___x_2431_);
v___x_2435_ = l_Rat_add(v_v_2413_, v___x_2434_);
v_v_2413_ = v___x_2435_;
v_a_2414_ = v_p_2427_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go___boxed(lean_object* v_a_2437_, lean_object* v_v_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_a_2437_, v_v_2438_, v_a_2439_);
lean_dec_ref(v_a_2437_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(lean_object* v_a_2441_){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = lean_nat_to_int(v_a_2441_);
v___x_2443_ = l_Rat_ofInt(v___x_2442_);
return v___x_2443_;
}
}
static lean_object* _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_unsigned_to_nat(0u);
v___x_2445_ = l_Nat_cast___at___00Int_Internal_Linear_Poly_eval_x3f_spec__0(v___x_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg(lean_object* v_p_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2447_, v_a_2448_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2461_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2461_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2461_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v_assignment_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2459_; 
v_assignment_2455_ = lean_ctor_get(v_a_2451_, 13);
lean_inc_ref(v_assignment_2455_);
lean_dec(v_a_2451_);
v___x_2456_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2457_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Internal_Linear_Poly_eval_x3f_go(v_assignment_2455_, v___x_2456_, v_p_2446_);
lean_dec_ref(v_assignment_2455_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2457_);
v___x_2459_ = v___x_2453_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec_ref(v_p_2446_);
v_a_2462_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2450_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2450_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___redArg___boxed(lean_object* v_p_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2470_, v_a_2471_, v_a_2472_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f(lean_object* v_p_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2475_, v_a_2476_, v_a_2484_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_eval_x3f___boxed(lean_object* v_p_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Int_Internal_Linear_Poly_eval_x3f(v_p_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
lean_dec(v_a_2494_);
lean_dec_ref(v_a_2493_);
lean_dec(v_a_2492_);
lean_dec_ref(v_a_2491_);
lean_dec(v_a_2490_);
lean_dec(v_a_2489_);
return v_res_2500_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(lean_object* v_c_2501_){
_start:
{
lean_object* v_p_2502_; uint8_t v___x_2503_; 
v_p_2502_ = lean_ctor_get(v_c_2501_, 0);
v___x_2503_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat___boxed(lean_object* v_c_2504_){
_start:
{
uint8_t v_res_2505_; lean_object* v_r_2506_; 
v_res_2505_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(v_c_2504_);
lean_dec_ref(v_c_2504_);
v_r_2506_ = lean_box(v_res_2505_);
return v_r_2506_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(lean_object* v_c_2507_){
_start:
{
lean_object* v_d_2508_; lean_object* v_p_2509_; uint8_t v___x_2510_; 
v_d_2508_ = lean_ctor_get(v_c_2507_, 0);
lean_inc(v_d_2508_);
v_p_2509_ = lean_ctor_get(v_c_2507_, 1);
lean_inc_ref(v_p_2509_);
lean_dec_ref(v_c_2507_);
v___x_2510_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_2508_, v_p_2509_);
lean_dec_ref(v_p_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat___boxed(lean_object* v_c_2511_){
_start:
{
uint8_t v_res_2512_; lean_object* v_r_2513_; 
v_res_2512_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(v_c_2511_);
v_r_2513_ = lean_box(v_res_2512_);
return v_r_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object* v_c_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_){
_start:
{
lean_object* v_d_2518_; lean_object* v_p_2519_; lean_object* v___x_2520_; 
v_d_2518_ = lean_ctor_get(v_c_2514_, 0);
lean_inc(v_d_2518_);
v_p_2519_ = lean_ctor_get(v_c_2514_, 1);
lean_inc_ref(v_p_2519_);
lean_dec_ref(v_c_2514_);
v___x_2520_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2519_, v_a_2515_, v_a_2516_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2547_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2523_ = v___x_2520_;
v_isShared_2524_ = v_isSharedCheck_2547_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2520_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2547_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
if (lean_obj_tag(v_a_2521_) == 1)
{
lean_object* v_val_2525_; lean_object* v_num_2526_; lean_object* v_den_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; uint8_t v___x_2530_; 
v_val_2525_ = lean_ctor_get(v_a_2521_, 0);
lean_inc(v_val_2525_);
lean_dec_ref_known(v_a_2521_, 1);
v_num_2526_ = lean_ctor_get(v_val_2525_, 0);
lean_inc(v_num_2526_);
v_den_2527_ = lean_ctor_get(v_val_2525_, 1);
lean_inc(v_den_2527_);
lean_dec(v_val_2525_);
v___x_2528_ = lean_unsigned_to_nat(1u);
v___x_2529_ = lean_nat_dec_eq(v_den_2527_, v___x_2528_);
lean_dec(v_den_2527_);
v___x_2530_ = lean_bool_not(v___x_2529_);
if (v___x_2530_ == 0)
{
uint8_t v___x_2531_; uint8_t v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2531_ = l_Int_decidableDvd(v_d_2518_, v_num_2526_);
lean_dec(v_num_2526_);
lean_dec(v_d_2518_);
v___x_2532_ = l_Lean_Bool_toLBool(v___x_2531_);
v___x_2533_ = lean_box(v___x_2532_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 0, v___x_2533_);
v___x_2535_ = v___x_2523_;
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
uint8_t v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2540_; 
lean_dec(v_num_2526_);
lean_dec(v_d_2518_);
v___x_2537_ = 0;
v___x_2538_ = lean_box(v___x_2537_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 0, v___x_2538_);
v___x_2540_ = v___x_2523_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
else
{
uint8_t v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
lean_dec(v_a_2521_);
lean_dec(v_d_2518_);
v___x_2542_ = 2;
v___x_2543_ = lean_box(v___x_2542_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 0, v___x_2543_);
v___x_2545_ = v___x_2523_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2543_);
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
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
lean_dec(v_d_2518_);
v_a_2548_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2520_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2520_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg___boxed(lean_object* v_c_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2556_, v_a_2557_, v_a_2558_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(lean_object* v_c_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2561_, v_a_2562_, v_a_2570_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___boxed(lean_object* v_c_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(v_c_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
lean_dec(v_a_2582_);
lean_dec_ref(v_a_2581_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
lean_dec(v_a_2578_);
lean_dec_ref(v_a_2577_);
lean_dec(v_a_2576_);
lean_dec(v_a_2575_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg(lean_object* v_p_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2587_, v_a_2588_, v_a_2589_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2609_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2609_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2609_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
if (lean_obj_tag(v_a_2592_) == 1)
{
lean_object* v_val_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; uint8_t v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
v_val_2596_ = lean_ctor_get(v_a_2592_, 0);
lean_inc(v_val_2596_);
lean_dec_ref_known(v_a_2592_, 1);
v___x_2597_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2598_ = l_Rat_instDecidableLe(v_val_2596_, v___x_2597_);
v___x_2599_ = l_Lean_Bool_toLBool(v___x_2598_);
v___x_2600_ = lean_box(v___x_2599_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2600_);
v___x_2602_ = v___x_2594_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
else
{
uint8_t v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2607_; 
lean_dec(v_a_2592_);
v___x_2604_ = 2;
v___x_2605_ = lean_box(v___x_2604_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2605_);
v___x_2607_ = v___x_2594_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
v_a_2610_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2591_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2591_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
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
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___redArg___boxed(lean_object* v_p_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2618_, v_a_2619_, v_a_2620_);
lean_dec_ref(v_a_2620_);
lean_dec(v_a_2619_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe(lean_object* v_p_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2623_, v_a_2624_, v_a_2632_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_satisfiedLe___boxed(lean_object* v_p_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Int_Internal_Linear_Poly_satisfiedLe(v_p_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
lean_dec(v_a_2638_);
lean_dec(v_a_2637_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(lean_object* v_c_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_){
_start:
{
lean_object* v_p_2653_; lean_object* v___x_2654_; 
v_p_2653_ = lean_ctor_get(v_c_2649_, 0);
lean_inc_ref(v_p_2653_);
lean_dec_ref(v_c_2649_);
v___x_2654_ = l_Int_Internal_Linear_Poly_satisfiedLe___redArg(v_p_2653_, v_a_2650_, v_a_2651_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg___boxed(lean_object* v_c_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2655_, v_a_2656_, v_a_2657_);
lean_dec_ref(v_a_2657_);
lean_dec(v_a_2656_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(lean_object* v_c_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2660_, v_a_2661_, v_a_2669_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___boxed(lean_object* v_c_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(v_c_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
lean_dec(v_a_2675_);
lean_dec(v_a_2674_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(lean_object* v_c_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v_p_2690_; lean_object* v___x_2691_; 
v_p_2690_ = lean_ctor_get(v_c_2686_, 0);
lean_inc_ref(v_p_2690_);
lean_dec_ref(v_c_2686_);
v___x_2691_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2690_, v_a_2687_, v_a_2688_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2710_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2694_ = v___x_2691_;
v_isShared_2695_ = v_isSharedCheck_2710_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2691_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2710_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
if (lean_obj_tag(v_a_2692_) == 1)
{
lean_object* v_val_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; uint8_t v___x_2699_; uint8_t v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2703_; 
v_val_2696_ = lean_ctor_get(v_a_2692_, 0);
lean_inc(v_val_2696_);
lean_dec_ref_known(v_a_2692_, 1);
v___x_2697_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2698_ = l_instDecidableEqRat_decEq(v_val_2696_, v___x_2697_);
lean_dec(v_val_2696_);
v___x_2699_ = lean_bool_not(v___x_2698_);
v___x_2700_ = l_Lean_Bool_toLBool(v___x_2699_);
v___x_2701_ = lean_box(v___x_2700_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v___x_2701_);
v___x_2703_ = v___x_2694_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
else
{
uint8_t v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2708_; 
lean_dec(v_a_2692_);
v___x_2705_ = 2;
v___x_2706_ = lean_box(v___x_2705_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v___x_2706_);
v___x_2708_ = v___x_2694_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2706_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
v_a_2711_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2691_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2691_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg___boxed(lean_object* v_c_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_2719_, v_a_2720_, v_a_2721_);
lean_dec_ref(v_a_2721_);
lean_dec(v_a_2720_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(lean_object* v_c_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_2724_, v_a_2725_, v_a_2733_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___boxed(lean_object* v_c_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(v_c_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
lean_dec(v_a_2747_);
lean_dec_ref(v_a_2746_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
lean_dec(v_a_2741_);
lean_dec_ref(v_a_2740_);
lean_dec(v_a_2739_);
lean_dec(v_a_2738_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(lean_object* v_c_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_){
_start:
{
lean_object* v_p_2754_; lean_object* v___x_2755_; 
v_p_2754_ = lean_ctor_get(v_c_2750_, 0);
lean_inc_ref(v_p_2754_);
lean_dec_ref(v_c_2750_);
v___x_2755_ = l_Int_Internal_Linear_Poly_eval_x3f___redArg(v_p_2754_, v_a_2751_, v_a_2752_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2773_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2758_ = v___x_2755_;
v_isShared_2759_ = v_isSharedCheck_2773_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2773_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
if (lean_obj_tag(v_a_2756_) == 1)
{
lean_object* v_val_2760_; lean_object* v___x_2761_; uint8_t v___x_2762_; uint8_t v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2766_; 
v_val_2760_ = lean_ctor_get(v_a_2756_, 0);
lean_inc(v_val_2760_);
lean_dec_ref_known(v_a_2756_, 1);
v___x_2761_ = lean_obj_once(&l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Internal_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2762_ = l_instDecidableEqRat_decEq(v_val_2760_, v___x_2761_);
lean_dec(v_val_2760_);
v___x_2763_ = l_Lean_Bool_toLBool(v___x_2762_);
v___x_2764_ = lean_box(v___x_2763_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2764_);
v___x_2766_ = v___x_2758_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2764_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
else
{
uint8_t v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2771_; 
lean_dec(v_a_2756_);
v___x_2768_ = 2;
v___x_2769_ = lean_box(v___x_2768_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2769_);
v___x_2771_ = v___x_2758_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
v_a_2774_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2755_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2755_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg___boxed(lean_object* v_c_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_2782_, v_a_2783_, v_a_2784_);
lean_dec_ref(v_a_2784_);
lean_dec(v_a_2783_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(lean_object* v_c_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_2787_, v_a_2788_, v_a_2796_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___boxed(lean_object* v_c_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(v_c_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_);
lean_dec(v_a_2810_);
lean_dec_ref(v_a_2809_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_2807_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
lean_dec(v_a_2801_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg(lean_object* v_p_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
if (lean_obj_tag(v_p_2813_) == 0)
{
lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2824_; 
v_isSharedCheck_2824_ = !lean_is_exclusive(v_p_2813_);
if (v_isSharedCheck_2824_ == 0)
{
lean_object* v_unused_2825_; 
v_unused_2825_ = lean_ctor_get(v_p_2813_, 0);
lean_dec(v_unused_2825_);
v___x_2818_ = v_p_2813_;
v_isShared_2819_ = v_isSharedCheck_2824_;
goto v_resetjp_2817_;
}
else
{
lean_dec(v_p_2813_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2824_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2820_; lean_object* v___x_2822_; 
v___x_2820_ = lean_box(0);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v___x_2820_);
v___x_2822_ = v___x_2818_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
else
{
lean_object* v_k_2826_; lean_object* v_v_2827_; lean_object* v_p_2828_; lean_object* v___x_2829_; 
v_k_2826_ = lean_ctor_get(v_p_2813_, 0);
lean_inc(v_k_2826_);
v_v_2827_ = lean_ctor_get(v_p_2813_, 1);
lean_inc(v_v_2827_);
v_p_2828_ = lean_ctor_get(v_p_2813_, 2);
lean_inc_ref(v_p_2828_);
lean_dec_ref_known(v_p_2813_, 3);
v___x_2829_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2814_, v_a_2815_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2856_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2832_ = v___x_2829_;
v_isShared_2833_ = v_isSharedCheck_2856_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2829_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2856_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___y_2835_; lean_object* v_elimEqs_2850_; lean_object* v_size_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v_elimEqs_2850_ = lean_ctor_get(v_a_2830_, 10);
lean_inc_ref(v_elimEqs_2850_);
lean_dec(v_a_2830_);
v_size_2851_ = lean_ctor_get(v_elimEqs_2850_, 2);
v___x_2852_ = lean_box(0);
v___x_2853_ = lean_nat_dec_lt(v_v_2827_, v_size_2851_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; 
lean_dec_ref(v_elimEqs_2850_);
v___x_2854_ = l_outOfBounds___redArg(v___x_2852_);
v___y_2835_ = v___x_2854_;
goto v___jp_2834_;
}
else
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2852_, v_elimEqs_2850_, v_v_2827_);
lean_dec_ref(v_elimEqs_2850_);
v___y_2835_ = v___x_2855_;
goto v___jp_2834_;
}
v___jp_2834_:
{
if (lean_obj_tag(v___y_2835_) == 1)
{
lean_object* v_val_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2848_; 
lean_dec_ref(v_p_2828_);
v_val_2836_ = lean_ctor_get(v___y_2835_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___y_2835_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2838_ = v___y_2835_;
v_isShared_2839_ = v_isSharedCheck_2848_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_val_2836_);
lean_dec(v___y_2835_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2848_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2843_; 
v___x_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2840_, 0, v_v_2827_);
lean_ctor_set(v___x_2840_, 1, v_val_2836_);
v___x_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2841_, 0, v_k_2826_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 0, v___x_2841_);
v___x_2843_ = v___x_2838_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
lean_object* v___x_2845_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 0, v___x_2843_);
v___x_2845_ = v___x_2832_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
else
{
lean_dec(v___y_2835_);
lean_del_object(v___x_2832_);
lean_dec(v_v_2827_);
lean_dec(v_k_2826_);
v_p_2813_ = v_p_2828_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec_ref(v_p_2828_);
lean_dec(v_v_2827_);
lean_dec(v_k_2826_);
v_a_2857_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2829_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2829_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg___boxed(lean_object* v_p_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_2865_, v_a_2866_, v_a_2867_);
lean_dec_ref(v_a_2867_);
lean_dec(v_a_2866_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst(lean_object* v_p_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_2870_, v_a_2871_, v_a_2879_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___boxed(lean_object* v_p_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Int_Internal_Linear_Poly_findVarToSubst(v_p_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
lean_dec(v_a_2893_);
lean_dec_ref(v_a_2892_);
lean_dec(v_a_2891_);
lean_dec_ref(v_a_2890_);
lean_dec(v_a_2889_);
lean_dec_ref(v_a_2888_);
lean_dec(v_a_2887_);
lean_dec_ref(v_a_2886_);
lean_dec(v_a_2885_);
lean_dec(v_a_2884_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(lean_object* v_pred_2896_){
_start:
{
lean_object* v_c_u2081_2897_; lean_object* v_c_u2082_2898_; uint8_t v_left_2899_; lean_object* v_c_u2083_x3f_2900_; lean_object* v_p_2901_; lean_object* v_p_2902_; lean_object* v_a_2903_; lean_object* v_b_2904_; 
v_c_u2081_2897_ = lean_ctor_get(v_pred_2896_, 0);
v_c_u2082_2898_ = lean_ctor_get(v_pred_2896_, 1);
v_left_2899_ = lean_ctor_get_uint8(v_pred_2896_, sizeof(void*)*3);
v_c_u2083_x3f_2900_ = lean_ctor_get(v_pred_2896_, 2);
v_p_2901_ = lean_ctor_get(v_c_u2081_2897_, 0);
v_p_2902_ = lean_ctor_get(v_c_u2082_2898_, 0);
v_a_2903_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_2901_);
v_b_2904_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_2902_);
if (lean_obj_tag(v_c_u2083_x3f_2900_) == 0)
{
if (v_left_2899_ == 0)
{
lean_object* v___x_2905_; 
lean_dec(v_a_2903_);
v___x_2905_ = lean_nat_abs(v_b_2904_);
lean_dec(v_b_2904_);
return v___x_2905_;
}
else
{
lean_object* v___x_2906_; 
lean_dec(v_b_2904_);
v___x_2906_ = lean_nat_abs(v_a_2903_);
lean_dec(v_a_2903_);
return v___x_2906_;
}
}
else
{
lean_object* v_val_2907_; lean_object* v_d_2908_; lean_object* v_p_2909_; lean_object* v_c_2910_; 
v_val_2907_ = lean_ctor_get(v_c_u2083_x3f_2900_, 0);
v_d_2908_ = lean_ctor_get(v_val_2907_, 0);
v_p_2909_ = lean_ctor_get(v_val_2907_, 1);
v_c_2910_ = l_Int_Internal_Linear_Poly_leadCoeff(v_p_2909_);
if (v_left_2899_ == 0)
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
lean_dec(v_a_2903_);
v___x_2911_ = lean_int_mul(v_b_2904_, v_d_2908_);
v___x_2912_ = l_Int_gcd(v___x_2911_, v_c_2910_);
lean_dec(v_c_2910_);
v___x_2913_ = lean_nat_to_int(v___x_2912_);
v___x_2914_ = lean_int_ediv(v___x_2911_, v___x_2913_);
lean_dec(v___x_2913_);
lean_dec(v___x_2911_);
v___x_2915_ = l_Int_lcm(v_b_2904_, v___x_2914_);
lean_dec(v___x_2914_);
lean_dec(v_b_2904_);
return v___x_2915_;
}
else
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
lean_dec(v_b_2904_);
v___x_2916_ = lean_int_mul(v_a_2903_, v_d_2908_);
v___x_2917_ = l_Int_gcd(v___x_2916_, v_c_2910_);
lean_dec(v_c_2910_);
v___x_2918_ = lean_nat_to_int(v___x_2917_);
v___x_2919_ = lean_int_ediv(v___x_2916_, v___x_2918_);
lean_dec(v___x_2918_);
lean_dec(v___x_2916_);
v___x_2920_ = l_Int_lcm(v_a_2903_, v___x_2919_);
lean_dec(v___x_2919_);
lean_dec(v_a_2903_);
return v___x_2920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases___boxed(lean_object* v_pred_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(v_pred_2921_);
lean_dec_ref(v_pred_2921_);
return v_res_2922_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2924_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0));
v___x_2925_ = l_Lean_stringToMessageData(v___x_2924_);
return v___x_2925_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4(void){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3));
v___x_2930_ = l_Lean_MessageData_ofFormat(v___x_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(lean_object* v_pred_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_){
_start:
{
lean_object* v_c_u2081_2935_; lean_object* v_c_u2082_2936_; lean_object* v_c_u2083_x3f_2937_; lean_object* v___x_2938_; 
v_c_u2081_2935_ = lean_ctor_get(v_pred_2931_, 0);
lean_inc_ref(v_c_u2081_2935_);
v_c_u2082_2936_ = lean_ctor_get(v_pred_2931_, 1);
lean_inc_ref(v_c_u2082_2936_);
v_c_u2083_x3f_2937_ = lean_ctor_get(v_pred_2931_, 2);
lean_inc(v_c_u2083_x3f_2937_);
lean_dec_ref(v_pred_2931_);
v___x_2938_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_2935_, v_a_2932_, v_a_2933_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___x_2938_, 1);
v___x_2940_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_2936_, v_a_2932_, v_a_2933_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2959_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2943_ = v___x_2940_;
v_isShared_2944_ = v_isSharedCheck_2959_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2959_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v_____do__lift_2946_; 
if (lean_obj_tag(v_c_u2083_x3f_2937_) == 1)
{
lean_object* v_val_2955_; lean_object* v___x_2956_; 
v_val_2955_ = lean_ctor_get(v_c_u2083_x3f_2937_, 0);
lean_inc(v_val_2955_);
lean_dec_ref_known(v_c_u2083_x3f_2937_, 1);
v___x_2956_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_val_2955_, v_a_2932_, v_a_2933_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2956_, 1);
v_____do__lift_2946_ = v_a_2957_;
goto v___jp_2945_;
}
else
{
lean_del_object(v___x_2943_);
lean_dec(v_a_2941_);
lean_dec(v_a_2939_);
return v___x_2956_;
}
}
else
{
lean_object* v___x_2958_; 
lean_dec(v_c_u2083_x3f_2937_);
v___x_2958_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4);
v_____do__lift_2946_ = v___x_2958_;
goto v___jp_2945_;
}
v___jp_2945_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2953_; 
v___x_2947_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_2948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2948_, 0, v_a_2939_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
v___x_2949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
lean_ctor_set(v___x_2949_, 1, v_a_2941_);
v___x_2950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
lean_ctor_set(v___x_2950_, 1, v___x_2947_);
v___x_2951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v_____do__lift_2946_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2951_);
v___x_2953_ = v___x_2943_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2951_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
else
{
lean_dec(v_a_2939_);
lean_dec(v_c_u2083_x3f_2937_);
return v___x_2940_;
}
}
else
{
lean_dec(v_c_u2083_x3f_2937_);
lean_dec_ref(v_c_u2082_2936_);
return v___x_2938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___boxed(lean_object* v_pred_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_2960_, v_a_2961_, v_a_2962_);
lean_dec_ref(v_a_2962_);
lean_dec(v_a_2961_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(lean_object* v_pred_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_2965_, v_a_2966_, v_a_2974_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___boxed(lean_object* v_pred_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(v_pred_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec_ref(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec(v_a_2980_);
lean_dec(v_a_2979_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(lean_object* v_h_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_){
_start:
{
switch(lean_obj_tag(v_h_2991_))
{
case 0:
{
lean_object* v_c_2995_; lean_object* v___x_2996_; 
v_c_2995_ = lean_ctor_get(v_h_2991_, 0);
lean_inc_ref(v_c_2995_);
lean_dec_ref_known(v_h_2991_, 1);
v___x_2996_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_2995_, v_a_2992_, v_a_2993_);
return v___x_2996_;
}
case 1:
{
lean_object* v_c_2997_; lean_object* v___x_2998_; 
v_c_2997_ = lean_ctor_get(v_h_2991_, 0);
lean_inc_ref(v_c_2997_);
lean_dec_ref_known(v_h_2991_, 1);
v___x_2998_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_2997_, v_a_2992_, v_a_2993_);
return v___x_2998_;
}
case 2:
{
lean_object* v_c_2999_; lean_object* v___x_3000_; 
v_c_2999_ = lean_ctor_get(v_h_2991_, 0);
lean_inc_ref(v_c_2999_);
lean_dec_ref_known(v_h_2991_, 1);
v___x_3000_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_2999_, v_a_2992_, v_a_2993_);
return v___x_3000_;
}
case 3:
{
lean_object* v_c_3001_; lean_object* v___x_3002_; 
v_c_3001_ = lean_ctor_get(v_h_2991_, 0);
lean_inc_ref(v_c_3001_);
lean_dec_ref_known(v_h_2991_, 1);
v___x_3002_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_3001_, v_a_2992_, v_a_2993_);
return v___x_3002_;
}
default: 
{
lean_object* v_c_u2081_3003_; lean_object* v_c_u2082_3004_; lean_object* v_c_u2083_3005_; lean_object* v___x_3006_; 
v_c_u2081_3003_ = lean_ctor_get(v_h_2991_, 0);
lean_inc_ref(v_c_u2081_3003_);
v_c_u2082_3004_ = lean_ctor_get(v_h_2991_, 1);
lean_inc_ref(v_c_u2082_3004_);
v_c_u2083_3005_ = lean_ctor_get(v_h_2991_, 2);
lean_inc_ref(v_c_u2083_3005_);
lean_dec_ref_known(v_h_2991_, 3);
v___x_3006_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3003_, v_a_2992_, v_a_2993_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v___x_3008_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3004_, v_a_2992_, v_a_2993_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3010_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v___x_3010_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2083_3005_, v_a_2992_, v_a_2993_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3023_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3013_ = v___x_3010_;
v_isShared_3014_ = v_isSharedCheck_3023_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_3010_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3023_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3021_; 
v___x_3015_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3016_, 0, v_a_3007_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
v___x_3017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
lean_ctor_set(v___x_3017_, 1, v_a_3009_);
v___x_3018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
lean_ctor_set(v___x_3018_, 1, v___x_3015_);
v___x_3019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
lean_ctor_set(v___x_3019_, 1, v_a_3011_);
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 0, v___x_3019_);
v___x_3021_ = v___x_3013_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3019_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
else
{
lean_dec(v_a_3009_);
lean_dec(v_a_3007_);
return v___x_3010_;
}
}
else
{
lean_dec(v_a_3007_);
lean_dec_ref(v_c_u2083_3005_);
return v___x_3008_;
}
}
else
{
lean_dec_ref(v_c_u2083_3005_);
lean_dec_ref(v_c_u2082_3004_);
return v___x_3006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg___boxed(lean_object* v_h_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3024_, v_a_3025_, v_a_3026_);
lean_dec_ref(v_a_3026_);
lean_dec(v_a_3025_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(lean_object* v_h_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v___x_3041_; 
v___x_3041_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3029_, v_a_3030_, v_a_3038_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___boxed(lean_object* v_h_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(v_h_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
lean_dec(v_a_3044_);
lean_dec(v_a_3043_);
return v_res_3054_;
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
