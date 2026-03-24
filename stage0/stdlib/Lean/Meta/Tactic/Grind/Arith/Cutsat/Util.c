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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_112_);
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
lean_dec_ref(v_conflict_x3f_120_);
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
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_316_; size_t v___x_317_; size_t v___x_318_; 
v___x_316_ = ((size_t)5ULL);
v___x_317_ = ((size_t)1ULL);
v___x_318_ = lean_usize_shift_left(v___x_317_, v___x_316_);
return v___x_318_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_319_; size_t v___x_320_; size_t v___x_321_; 
v___x_319_ = ((size_t)1ULL);
v___x_320_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__0);
v___x_321_ = lean_usize_sub(v___x_320_, v___x_319_);
return v___x_321_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(lean_object* v_x_322_, size_t v_x_323_, lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_322_) == 0)
{
lean_object* v_es_325_; lean_object* v___x_326_; size_t v___x_327_; size_t v___x_328_; size_t v___x_329_; lean_object* v_j_330_; lean_object* v___x_331_; 
v_es_325_ = lean_ctor_get(v_x_322_, 0);
lean_inc_ref(v_es_325_);
lean_dec_ref(v_x_322_);
v___x_326_ = lean_box(2);
v___x_327_ = ((size_t)5ULL);
v___x_328_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__1);
v___x_329_ = lean_usize_land(v_x_323_, v___x_328_);
v_j_330_ = lean_usize_to_nat(v___x_329_);
v___x_331_ = lean_array_get(v___x_326_, v_es_325_, v_j_330_);
lean_dec(v_j_330_);
lean_dec_ref(v_es_325_);
switch(lean_obj_tag(v___x_331_))
{
case 0:
{
lean_object* v_key_332_; uint8_t v___x_333_; 
v_key_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_key_332_);
lean_dec_ref(v___x_331_);
v___x_333_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_324_, v_key_332_);
lean_dec(v_key_332_);
return v___x_333_;
}
case 1:
{
lean_object* v_node_334_; size_t v___x_335_; 
v_node_334_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_node_334_);
lean_dec_ref(v___x_331_);
v___x_335_ = lean_usize_shift_right(v_x_323_, v___x_327_);
v_x_322_ = v_node_334_;
v_x_323_ = v___x_335_;
goto _start;
}
default: 
{
uint8_t v___x_337_; 
v___x_337_ = 0;
return v___x_337_;
}
}
}
else
{
lean_object* v_ks_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v_ks_338_ = lean_ctor_get(v_x_322_, 0);
lean_inc_ref(v_ks_338_);
lean_dec_ref(v_x_322_);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_ks_338_, v___x_339_, v_x_324_);
lean_dec_ref(v_ks_338_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___boxed(lean_object* v_x_341_, lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
size_t v_x_853__boxed_344_; uint8_t v_res_345_; lean_object* v_r_346_; 
v_x_853__boxed_344_ = lean_unbox_usize(v_x_342_);
lean_dec(v_x_342_);
v_res_345_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_341_, v_x_853__boxed_344_, v_x_343_);
lean_dec_ref(v_x_343_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
uint64_t v___x_349_; size_t v___x_350_; uint8_t v___x_351_; 
v___x_349_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_348_);
v___x_350_ = lean_uint64_to_usize(v___x_349_);
v___x_351_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_347_, v___x_350_, v_x_348_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg___boxed(lean_object* v_x_352_, lean_object* v_x_353_){
_start:
{
uint8_t v_res_354_; lean_object* v_r_355_; 
v_res_354_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_352_, v_x_353_);
lean_dec_ref(v_x_353_);
v_r_355_ = lean_box(v_res_354_);
return v_r_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(lean_object* v_e_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_357_, v_a_358_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_371_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_371_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v_varMap_365_; uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v_varMap_365_ = lean_ctor_get(v_a_361_, 1);
lean_inc_ref(v_varMap_365_);
lean_dec(v_a_361_);
v___x_366_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_varMap_365_, v_e_356_);
v___x_367_ = lean_box(v___x_366_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_367_);
v___x_369_ = v___x_363_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
v_a_372_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_360_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_360_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg___boxed(lean_object* v_e_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_380_, v_a_381_, v_a_382_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_e_380_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar(lean_object* v_e_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_385_, v_a_386_, v_a_394_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_hasVar___boxed(lean_object* v_e_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar(v_e_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
lean_dec(v_a_399_);
lean_dec_ref(v_e_398_);
return v_res_410_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(lean_object* v_00_u03b2_411_, lean_object* v_x_412_, lean_object* v_x_413_){
_start:
{
uint8_t v___x_414_; 
v___x_414_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_412_, v_x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___boxed(lean_object* v_00_u03b2_415_, lean_object* v_x_416_, lean_object* v_x_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(v_00_u03b2_415_, v_x_416_, v_x_417_);
lean_dec_ref(v_x_417_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(lean_object* v_00_u03b2_420_, lean_object* v_x_421_, size_t v_x_422_, lean_object* v_x_423_){
_start:
{
uint8_t v___x_424_; 
v___x_424_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_421_, v_x_422_, v_x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_425_, lean_object* v_x_426_, lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
size_t v_x_966__boxed_429_; uint8_t v_res_430_; lean_object* v_r_431_; 
v_x_966__boxed_429_ = lean_unbox_usize(v_x_427_);
lean_dec(v_x_427_);
v_res_430_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(v_00_u03b2_425_, v_x_426_, v_x_966__boxed_429_, v_x_428_);
lean_dec_ref(v_x_428_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_432_, lean_object* v_keys_433_, lean_object* v_vals_434_, lean_object* v_heq_435_, lean_object* v_i_436_, lean_object* v_k_437_){
_start:
{
uint8_t v___x_438_; 
v___x_438_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_433_, v_i_436_, v_k_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_439_, lean_object* v_keys_440_, lean_object* v_vals_441_, lean_object* v_heq_442_, lean_object* v_i_443_, lean_object* v_k_444_){
_start:
{
uint8_t v_res_445_; lean_object* v_r_446_; 
v_res_445_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(v_00_u03b2_439_, v_keys_440_, v_vals_441_, v_heq_442_, v_i_443_, v_k_444_);
lean_dec_ref(v_k_444_);
lean_dec_ref(v_vals_441_);
lean_dec_ref(v_keys_440_);
v_r_446_ = lean_box(v_res_445_);
return v_r_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(lean_object* v_e_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_447_, v_a_448_, v_a_449_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg___boxed(lean_object* v_e_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(v_e_452_, v_a_453_, v_a_454_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_e_452_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(lean_object* v_e_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_457_, v_a_458_, v_a_466_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___boxed(lean_object* v_e_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(v_e_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_e_470_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(lean_object* v_x_483_, lean_object* v_a_484_, lean_object* v_a_485_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_484_, v_a_485_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_510_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_510_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_510_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_510_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___y_493_; lean_object* v_elimEqs_504_; lean_object* v_size_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v_elimEqs_504_ = lean_ctor_get(v_a_488_, 10);
lean_inc_ref(v_elimEqs_504_);
lean_dec(v_a_488_);
v_size_505_ = lean_ctor_get(v_elimEqs_504_, 2);
v___x_506_ = lean_box(0);
v___x_507_ = lean_nat_dec_lt(v_x_483_, v_size_505_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_dec_ref(v_elimEqs_504_);
v___x_508_ = l_outOfBounds___redArg(v___x_506_);
v___y_493_ = v___x_508_;
goto v___jp_492_;
}
else
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_PersistentArray_get_x21___redArg(v___x_506_, v_elimEqs_504_, v_x_483_);
v___y_493_ = v___x_509_;
goto v___jp_492_;
}
v___jp_492_:
{
if (lean_obj_tag(v___y_493_) == 0)
{
uint8_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_494_ = 0;
v___x_495_ = lean_box(v___x_494_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_495_);
v___x_497_ = v___x_490_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
else
{
uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
lean_dec_ref(v___y_493_);
v___x_499_ = 1;
v___x_500_ = lean_box(v___x_499_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_500_);
v___x_502_ = v___x_490_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_a_511_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_487_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_487_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg___boxed(lean_object* v_x_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_519_, v_a_520_, v_a_521_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec(v_x_519_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated(lean_object* v_x_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_524_, v_a_525_, v_a_533_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_eliminated___boxed(lean_object* v_x_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated(v_x_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec(v_a_538_);
lean_dec(v_x_537_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_assert___boxed(lean_object* v_c_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_00___x40___internal___hyg_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = lean_grind_cutsat_assert_eq(v_c_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(lean_object* v_x_575_, lean_object* v_s_576_){
_start:
{
lean_object* v_vars_577_; lean_object* v_varMap_578_; lean_object* v_vars_x27_579_; lean_object* v_varMap_x27_580_; lean_object* v_natToIntMap_581_; lean_object* v_natDef_582_; lean_object* v_dvds_583_; lean_object* v_lowers_584_; lean_object* v_uppers_585_; lean_object* v_diseqs_586_; lean_object* v_elimEqs_587_; lean_object* v_elimStack_588_; lean_object* v_occurs_589_; lean_object* v_assignment_590_; lean_object* v_nextCnstrId_591_; uint8_t v_caseSplits_592_; lean_object* v_conflict_x3f_593_; lean_object* v_diseqSplits_594_; lean_object* v_divMod_595_; lean_object* v_toIntIds_596_; lean_object* v_toIntInfos_597_; lean_object* v_toIntTermMap_598_; lean_object* v_toIntVarMap_599_; uint8_t v_usedCommRing_600_; lean_object* v_nonlinearOccs_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_609_; 
v_vars_577_ = lean_ctor_get(v_s_576_, 0);
v_varMap_578_ = lean_ctor_get(v_s_576_, 1);
v_vars_x27_579_ = lean_ctor_get(v_s_576_, 2);
v_varMap_x27_580_ = lean_ctor_get(v_s_576_, 3);
v_natToIntMap_581_ = lean_ctor_get(v_s_576_, 4);
v_natDef_582_ = lean_ctor_get(v_s_576_, 5);
v_dvds_583_ = lean_ctor_get(v_s_576_, 6);
v_lowers_584_ = lean_ctor_get(v_s_576_, 7);
v_uppers_585_ = lean_ctor_get(v_s_576_, 8);
v_diseqs_586_ = lean_ctor_get(v_s_576_, 9);
v_elimEqs_587_ = lean_ctor_get(v_s_576_, 10);
v_elimStack_588_ = lean_ctor_get(v_s_576_, 11);
v_occurs_589_ = lean_ctor_get(v_s_576_, 12);
v_assignment_590_ = lean_ctor_get(v_s_576_, 13);
v_nextCnstrId_591_ = lean_ctor_get(v_s_576_, 14);
v_caseSplits_592_ = lean_ctor_get_uint8(v_s_576_, sizeof(void*)*23);
v_conflict_x3f_593_ = lean_ctor_get(v_s_576_, 15);
v_diseqSplits_594_ = lean_ctor_get(v_s_576_, 16);
v_divMod_595_ = lean_ctor_get(v_s_576_, 17);
v_toIntIds_596_ = lean_ctor_get(v_s_576_, 18);
v_toIntInfos_597_ = lean_ctor_get(v_s_576_, 19);
v_toIntTermMap_598_ = lean_ctor_get(v_s_576_, 20);
v_toIntVarMap_599_ = lean_ctor_get(v_s_576_, 21);
v_usedCommRing_600_ = lean_ctor_get_uint8(v_s_576_, sizeof(void*)*23 + 1);
v_nonlinearOccs_601_ = lean_ctor_get(v_s_576_, 22);
v_isSharedCheck_609_ = !lean_is_exclusive(v_s_576_);
if (v_isSharedCheck_609_ == 0)
{
v___x_603_ = v_s_576_;
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_nonlinearOccs_601_);
lean_inc(v_toIntVarMap_599_);
lean_inc(v_toIntTermMap_598_);
lean_inc(v_toIntInfos_597_);
lean_inc(v_toIntIds_596_);
lean_inc(v_divMod_595_);
lean_inc(v_diseqSplits_594_);
lean_inc(v_conflict_x3f_593_);
lean_inc(v_nextCnstrId_591_);
lean_inc(v_assignment_590_);
lean_inc(v_occurs_589_);
lean_inc(v_elimStack_588_);
lean_inc(v_elimEqs_587_);
lean_inc(v_diseqs_586_);
lean_inc(v_uppers_585_);
lean_inc(v_lowers_584_);
lean_inc(v_dvds_583_);
lean_inc(v_natDef_582_);
lean_inc(v_natToIntMap_581_);
lean_inc(v_varMap_x27_580_);
lean_inc(v_vars_x27_579_);
lean_inc(v_varMap_578_);
lean_inc(v_vars_577_);
lean_dec(v_s_576_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_590_, v_x_575_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 13, v___x_605_);
v___x_607_ = v___x_603_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_vars_577_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_varMap_578_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_vars_x27_579_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v_varMap_x27_580_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v_natToIntMap_581_);
lean_ctor_set(v_reuseFailAlloc_608_, 5, v_natDef_582_);
lean_ctor_set(v_reuseFailAlloc_608_, 6, v_dvds_583_);
lean_ctor_set(v_reuseFailAlloc_608_, 7, v_lowers_584_);
lean_ctor_set(v_reuseFailAlloc_608_, 8, v_uppers_585_);
lean_ctor_set(v_reuseFailAlloc_608_, 9, v_diseqs_586_);
lean_ctor_set(v_reuseFailAlloc_608_, 10, v_elimEqs_587_);
lean_ctor_set(v_reuseFailAlloc_608_, 11, v_elimStack_588_);
lean_ctor_set(v_reuseFailAlloc_608_, 12, v_occurs_589_);
lean_ctor_set(v_reuseFailAlloc_608_, 13, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_608_, 14, v_nextCnstrId_591_);
lean_ctor_set(v_reuseFailAlloc_608_, 15, v_conflict_x3f_593_);
lean_ctor_set(v_reuseFailAlloc_608_, 16, v_diseqSplits_594_);
lean_ctor_set(v_reuseFailAlloc_608_, 17, v_divMod_595_);
lean_ctor_set(v_reuseFailAlloc_608_, 18, v_toIntIds_596_);
lean_ctor_set(v_reuseFailAlloc_608_, 19, v_toIntInfos_597_);
lean_ctor_set(v_reuseFailAlloc_608_, 20, v_toIntTermMap_598_);
lean_ctor_set(v_reuseFailAlloc_608_, 21, v_toIntVarMap_599_);
lean_ctor_set(v_reuseFailAlloc_608_, 22, v_nonlinearOccs_601_);
lean_ctor_set_uint8(v_reuseFailAlloc_608_, sizeof(void*)*23, v_caseSplits_592_);
lean_ctor_set_uint8(v_reuseFailAlloc_608_, sizeof(void*)*23 + 1, v_usedCommRing_600_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_x_610_, lean_object* v_s_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(v_x_610_, v_s_611_);
lean_dec(v_x_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object* v_x_613_, lean_object* v_a_614_){
_start:
{
lean_object* v___f_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___f_616_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_616_, 0, v_x_613_);
v___x_617_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_618_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_617_, v___f_616_, v_a_614_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___boxed(lean_object* v_x_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_619_, v_a_620_);
lean_dec(v_a_620_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(lean_object* v_x_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_623_, v_a_624_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___boxed(lean_object* v_x_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(v_x_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec(v_a_637_);
return v_res_648_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__0));
v___x_651_ = l_Lean_stringToMessageData(v___x_650_);
return v___x_651_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = lean_nat_to_int(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3));
v___x_656_ = l_Lean_stringToMessageData(v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(lean_object* v_r_657_, lean_object* v_p_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
if (lean_obj_tag(v_p_658_) == 0)
{
lean_object* v_k_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_680_; 
v_k_662_ = lean_ctor_get(v_p_658_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v_p_658_);
if (v_isSharedCheck_680_ == 0)
{
v___x_664_ = v_p_658_;
v_isShared_665_ = v_isSharedCheck_680_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_k_662_);
lean_dec(v_p_658_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_680_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_667_ = lean_int_dec_eq(v_k_662_, v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_668_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1);
v___x_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_669_, 0, v_r_657_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = l_Int_repr(v_k_662_);
lean_dec(v_k_662_);
if (v_isShared_665_ == 0)
{
lean_ctor_set_tag(v___x_664_, 3);
lean_ctor_set(v___x_664_, 0, v___x_670_);
v___x_672_ = v___x_664_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_676_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = l_Lean_MessageData_ofFormat(v___x_672_);
v___x_674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_669_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
else
{
lean_object* v___x_678_; 
lean_dec(v_k_662_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v_r_657_);
v___x_678_ = v___x_664_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_r_657_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
else
{
lean_object* v_k_681_; lean_object* v_v_682_; lean_object* v_p_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v_k_681_ = lean_ctor_get(v_p_658_, 0);
lean_inc(v_k_681_);
v_v_682_ = lean_ctor_get(v_p_658_, 1);
lean_inc(v_v_682_);
v_p_683_ = lean_ctor_get(v_p_658_, 2);
lean_inc_ref(v_p_683_);
lean_dec_ref(v_p_658_);
v___x_684_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2);
v___x_685_ = lean_int_dec_eq(v_k_681_, v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_682_, v_a_659_, v_a_660_);
lean_dec(v_v_682_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref(v___x_686_);
v___x_688_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1);
v___x_689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_689_, 0, v_r_657_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = l_Int_repr(v_k_681_);
lean_dec(v_k_681_);
v___x_691_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
v___x_692_ = l_Lean_MessageData_ofFormat(v___x_691_);
v___x_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_689_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4);
v___x_695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_693_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_687_);
v___x_697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v_r_657_ = v___x_697_;
v_p_658_ = v_p_683_;
goto _start;
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec_ref(v_p_683_);
lean_dec(v_k_681_);
lean_dec_ref(v_r_657_);
v_a_699_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_686_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_686_);
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
else
{
lean_object* v___x_707_; 
lean_dec(v_k_681_);
v___x_707_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_682_, v_a_659_, v_a_660_);
lean_dec(v_v_682_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref(v___x_707_);
v___x_709_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1);
v___x_710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_710_, 0, v_r_657_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_708_);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v_r_657_ = v___x_712_;
v_p_658_ = v_p_683_;
goto _start;
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v_p_683_);
lean_dec_ref(v_r_657_);
v_a_714_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_707_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_707_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___boxed(lean_object* v_r_722_, lean_object* v_p_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(v_r_722_, v_p_723_, v_a_724_, v_a_725_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go(lean_object* v_r_728_, lean_object* v_p_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(v_r_728_, v_p_729_, v_a_730_, v_a_738_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___boxed(lean_object* v_r_742_, lean_object* v_p_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go(v_r_742_, v_p_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec(v_a_744_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_pp___redArg(lean_object* v_p_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
if (lean_obj_tag(v_p_756_) == 0)
{
lean_object* v_k_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_770_; 
v_k_760_ = lean_ctor_get(v_p_756_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v_p_756_);
if (v_isSharedCheck_770_ == 0)
{
v___x_762_ = v_p_756_;
v_isShared_763_ = v_isSharedCheck_770_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_k_760_);
lean_dec(v_p_756_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_770_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_764_ = l_Int_repr(v_k_760_);
lean_dec(v_k_760_);
if (v_isShared_763_ == 0)
{
lean_ctor_set_tag(v___x_762_, 3);
lean_ctor_set(v___x_762_, 0, v___x_764_);
v___x_766_ = v___x_762_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_764_);
v___x_766_ = v_reuseFailAlloc_769_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = l_Lean_MessageData_ofFormat(v___x_766_);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
}
}
else
{
lean_object* v_k_771_; lean_object* v_v_772_; lean_object* v_p_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_k_771_ = lean_ctor_get(v_p_756_, 0);
lean_inc(v_k_771_);
v_v_772_ = lean_ctor_get(v_p_756_, 1);
lean_inc(v_v_772_);
v_p_773_ = lean_ctor_get(v_p_756_, 2);
lean_inc_ref(v_p_773_);
lean_dec_ref(v_p_756_);
v___x_774_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2);
v___x_775_ = lean_int_dec_eq(v_k_771_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_772_, v_a_757_, v_a_758_);
lean_dec(v_v_772_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref(v___x_776_);
v___x_778_ = l_Int_repr(v_k_771_);
lean_dec(v_k_771_);
v___x_779_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
v___x_780_ = l_Lean_MessageData_ofFormat(v___x_779_);
v___x_781_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4);
v___x_782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_777_);
v___x_784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(v___x_784_, v_p_773_, v_a_757_, v_a_758_);
return v___x_785_;
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v_p_773_);
lean_dec(v_k_771_);
v_a_786_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_776_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_776_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_object* v___x_794_; 
lean_dec(v_k_771_);
v___x_794_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_772_, v_a_757_, v_a_758_);
lean_dec(v_v_772_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref(v___x_794_);
v___x_796_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_795_);
v___x_797_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(v___x_796_, v_p_773_, v_a_757_, v_a_758_);
return v___x_797_;
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec_ref(v_p_773_);
v_a_798_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_794_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_794_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
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
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_pp___redArg___boxed(lean_object* v_p_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Int_Linear_Poly_pp___redArg(v_p_806_, v_a_807_, v_a_808_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_pp(lean_object* v_p_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Int_Linear_Poly_pp___redArg(v_p_811_, v_a_812_, v_a_820_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_pp___boxed(lean_object* v_p_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Int_Linear_Poly_pp(v_p_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
lean_dec(v_a_825_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0(lean_object* v_a_837_, lean_object* v___x_838_, lean_object* v_x_839_){
_start:
{
lean_object* v_size_840_; uint8_t v___x_841_; 
v_size_840_ = lean_ctor_get(v_a_837_, 2);
v___x_841_ = lean_nat_dec_lt(v_x_839_, v_size_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; 
lean_dec_ref(v_a_837_);
v___x_842_ = l_outOfBounds___redArg(v___x_838_);
return v___x_842_;
}
else
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_PersistentArray_get_x21___redArg(v___x_838_, v_a_837_, v_x_839_);
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed(lean_object* v_a_844_, lean_object* v___x_845_, lean_object* v_x_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0(v_a_844_, v___x_845_, v_x_846_);
lean_dec(v_x_846_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___redArg(lean_object* v_p_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_849_, v_a_850_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; lean_object* v___f_855_; lean_object* v___x_856_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref(v___x_852_);
v___x_854_ = l_Lean_instInhabitedExpr;
v___f_855_ = lean_alloc_closure((void*)(l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_855_, 0, v_a_853_);
lean_closure_set(v___f_855_, 1, v___x_854_);
v___x_856_ = l_Int_Linear_Poly_denoteExpr___redArg(v___f_855_, v_p_848_);
return v___x_856_;
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec_ref(v_p_848_);
v_a_857_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_852_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_852_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___redArg___boxed(lean_object* v_p_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_865_, v_a_866_, v_a_867_);
lean_dec_ref(v_a_867_);
lean_dec(v_a_866_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27(lean_object* v_p_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_870_, v_a_871_, v_a_879_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___boxed(lean_object* v_p_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Int_Linear_Poly_denoteExpr_x27(v_p_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec(v_a_884_);
return v_res_895_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object* v_c_896_){
_start:
{
lean_object* v_p_897_; 
v_p_897_ = lean_ctor_get(v_c_896_, 1);
if (lean_obj_tag(v_p_897_) == 0)
{
lean_object* v_d_898_; lean_object* v_k_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v_d_898_ = lean_ctor_get(v_c_896_, 0);
v_k_899_ = lean_ctor_get(v_p_897_, 0);
v___x_900_ = lean_int_emod(v_k_899_, v_d_898_);
v___x_901_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_902_ = lean_int_dec_eq(v___x_900_, v___x_901_);
lean_dec(v___x_900_);
return v___x_902_;
}
else
{
lean_object* v_d_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v_d_903_ = lean_ctor_get(v_c_896_, 0);
v___x_904_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2);
v___x_905_ = lean_int_dec_eq(v_d_903_, v___x_904_);
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial___boxed(lean_object* v_c_906_){
_start:
{
uint8_t v_res_907_; lean_object* v_r_908_; 
v_res_907_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_c_906_);
lean_dec_ref(v_c_906_);
v_r_908_ = lean_box(v_res_907_);
return v_r_908_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0));
v___x_911_ = l_Lean_stringToMessageData(v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object* v_c_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_d_916_; lean_object* v_p_917_; lean_object* v___x_918_; 
v_d_916_ = lean_ctor_get(v_c_912_, 0);
lean_inc(v_d_916_);
v_p_917_ = lean_ctor_get(v_c_912_, 1);
lean_inc_ref(v_p_917_);
lean_dec_ref(v_c_912_);
v___x_918_ = l_Int_Linear_Poly_pp___redArg(v_p_917_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_932_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_932_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_932_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_932_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_923_ = l_Int_repr(v_d_916_);
lean_dec(v_d_916_);
v___x_924_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
v___x_925_ = l_Lean_MessageData_ofFormat(v___x_924_);
v___x_926_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1);
v___x_927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v_a_919_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_928_);
v___x_930_ = v___x_921_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
else
{
lean_dec(v_d_916_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___boxed(lean_object* v_c_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_933_, v_a_934_, v_a_935_);
lean_dec_ref(v_a_935_);
lean_dec(v_a_934_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(lean_object* v_c_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_938_, v_a_939_, v_a_947_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___boxed(lean_object* v_c_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(v_c_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec(v_a_952_);
return v_res_963_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = lean_unsigned_to_nat(0u);
v___x_970_ = l_Lean_Level_ofNat(v___x_969_);
return v___x_970_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_971_ = lean_box(0);
v___x_972_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3);
v___x_973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v___x_971_);
return v___x_973_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4);
v___x_975_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2));
v___x_976_ = l_Lean_Expr_const___override(v___x_975_, v___x_974_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = lean_box(0);
v___x_981_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7));
v___x_982_ = l_Lean_Expr_const___override(v___x_981_, v___x_980_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = lean_box(0);
v___x_988_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10));
v___x_989_ = l_Lean_Expr_const___override(v___x_988_, v___x_987_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(lean_object* v_c_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_d_994_; lean_object* v_p_995_; lean_object* v___x_996_; 
v_d_994_ = lean_ctor_get(v_c_990_, 0);
lean_inc(v_d_994_);
v_p_995_ = lean_ctor_get(v_c_990_, 1);
lean_inc_ref(v_p_995_);
lean_dec_ref(v_c_990_);
v___x_996_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_995_, v_a_991_, v_a_992_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1018_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1018_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1018_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___y_1002_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1007_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1008_ = lean_int_dec_le(v___x_1007_, v_d_994_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1009_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5);
v___x_1010_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8);
v___x_1011_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11);
v___x_1012_ = lean_int_neg(v_d_994_);
lean_dec(v_d_994_);
v___x_1013_ = l_Int_toNat(v___x_1012_);
lean_dec(v___x_1012_);
v___x_1014_ = l_Lean_instToExprInt_mkNat(v___x_1013_);
v___x_1015_ = l_Lean_mkApp3(v___x_1009_, v___x_1010_, v___x_1011_, v___x_1014_);
v___y_1002_ = v___x_1015_;
goto v___jp_1001_;
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = l_Int_toNat(v_d_994_);
lean_dec(v_d_994_);
v___x_1017_ = l_Lean_instToExprInt_mkNat(v___x_1016_);
v___y_1002_ = v___x_1017_;
goto v___jp_1001_;
}
v___jp_1001_:
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = l_Lean_mkIntDvd(v___y_1002_, v_a_997_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1003_);
v___x_1005_ = v___x_999_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
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
lean_dec(v_d_994_);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1019_, v_a_1020_, v_a_1021_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(lean_object* v_c_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1024_, v_a_1025_, v_a_1033_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___boxed(lean_object* v_c_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(v_c_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec(v_a_1038_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(lean_object* v_msgData_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1056_; lean_object* v_env_1057_; lean_object* v___x_1058_; lean_object* v_mctx_1059_; lean_object* v_lctx_1060_; lean_object* v_options_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1056_ = lean_st_ref_get(v___y_1054_);
v_env_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc_ref(v_env_1057_);
lean_dec(v___x_1056_);
v___x_1058_ = lean_st_ref_get(v___y_1052_);
v_mctx_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc_ref(v_mctx_1059_);
lean_dec(v___x_1058_);
v_lctx_1060_ = lean_ctor_get(v___y_1051_, 2);
v_options_1061_ = lean_ctor_get(v___y_1053_, 2);
lean_inc_ref(v_options_1061_);
lean_inc_ref(v_lctx_1060_);
v___x_1062_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1062_, 0, v_env_1057_);
lean_ctor_set(v___x_1062_, 1, v_mctx_1059_);
lean_ctor_set(v___x_1062_, 2, v_lctx_1060_);
lean_ctor_set(v___x_1062_, 3, v_options_1061_);
v___x_1063_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v_msgData_1050_);
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object* v_msgData_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msgData_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(lean_object* v_msg_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_ref_1078_; lean_object* v___x_1079_; lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1088_; 
v_ref_1078_ = lean_ctor_get(v___y_1075_, 5);
v___x_1079_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msg_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1088_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1088_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
lean_inc(v_ref_1078_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_ref_1078_);
lean_ctor_set(v___x_1084_, 1, v_a_1080_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 1);
lean_ctor_set(v___x_1082_, 0, v___x_1084_);
v___x_1086_ = v___x_1082_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg___boxed(lean_object* v_msg_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
return v_res_1095_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0));
v___x_1098_ = l_Lean_stringToMessageData(v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2));
v___x_1101_ = l_Lean_stringToMessageData(v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object* v_c_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1102_, v_a_1103_, v_a_1111_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref(v___x_1114_);
v___x_1116_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1117_ = l_Lean_indentD(v_a_1115_);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1120_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
return v___x_1121_;
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
v_a_1122_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1114_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1114_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec(v_a_1131_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(lean_object* v_00_u03b1_1143_, lean_object* v_c_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1157_, lean_object* v_c_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(v_00_u03b1_1157_, v_c_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_a_1160_);
lean_dec(v_a_1159_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(lean_object* v_00_u03b1_1171_, lean_object* v_msg_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1172_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___boxed(lean_object* v_00_u03b1_1185_, lean_object* v_msg_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(v_00_u03b1_1185_, v_msg_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec(v___y_1187_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial_spec__0(lean_object* v_a_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_nat_to_int(v_a_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(lean_object* v_c_1201_){
_start:
{
lean_object* v_p_1202_; 
v_p_1202_ = lean_ctor_get(v_c_1201_, 0);
if (lean_obj_tag(v_p_1202_) == 0)
{
lean_object* v_k_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v_k_1203_ = lean_ctor_get(v_p_1202_, 0);
v___x_1204_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1205_ = lean_int_dec_eq(v_k_1203_, v___x_1204_);
if (v___x_1205_ == 0)
{
uint8_t v___x_1206_; 
v___x_1206_ = 1;
return v___x_1206_;
}
else
{
uint8_t v___x_1207_; 
v___x_1207_ = 0;
return v___x_1207_;
}
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1208_ = l_Int_Linear_Poly_getConst(v_p_1202_);
v___x_1209_ = l_Int_Linear_Poly_gcdCoeffs_x27(v_p_1202_);
v___x_1210_ = lean_nat_to_int(v___x_1209_);
v___x_1211_ = lean_int_emod(v___x_1208_, v___x_1210_);
lean_dec(v___x_1210_);
lean_dec(v___x_1208_);
v___x_1212_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1213_ = lean_int_dec_eq(v___x_1211_, v___x_1212_);
lean_dec(v___x_1211_);
if (v___x_1213_ == 0)
{
uint8_t v___x_1214_; 
v___x_1214_ = 1;
return v___x_1214_;
}
else
{
uint8_t v___x_1215_; 
v___x_1215_ = 0;
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial___boxed(lean_object* v_c_1216_){
_start:
{
uint8_t v_res_1217_; lean_object* v_r_1218_; 
v_res_1217_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(v_c_1216_);
lean_dec_ref(v_c_1216_);
v_r_1218_ = lean_box(v_res_1217_);
return v_r_1218_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0));
v___x_1221_ = l_Lean_stringToMessageData(v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(lean_object* v_c_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_p_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1243_; 
v_p_1226_ = lean_ctor_get(v_c_1222_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_c_1222_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; 
v_unused_1244_ = lean_ctor_get(v_c_1222_, 1);
lean_dec(v_unused_1244_);
v___x_1228_ = v_c_1222_;
v_isShared_1229_ = v_isSharedCheck_1243_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_p_1226_);
lean_dec(v_c_1222_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1243_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Int_Linear_Poly_pp___redArg(v_p_1226_, v_a_1223_, v_a_1224_);
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
v___x_1235_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1);
if (v_isShared_1229_ == 0)
{
lean_ctor_set_tag(v___x_1228_, 7);
lean_ctor_set(v___x_1228_, 1, v___x_1235_);
lean_ctor_set(v___x_1228_, 0, v_a_1231_);
v___x_1237_ = v___x_1228_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1231_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___x_1235_);
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
lean_del_object(v___x_1228_);
return v___x_1230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___boxed(lean_object* v_c_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1245_, v_a_1246_, v_a_1247_);
lean_dec_ref(v_a_1247_);
lean_dec(v_a_1246_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(lean_object* v_c_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1250_, v_a_1251_, v_a_1259_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___boxed(lean_object* v_c_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(v_c_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec(v_a_1264_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(lean_object* v_c_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1276_, v_a_1277_, v_a_1280_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref(v___x_1283_);
v___x_1285_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1286_ = l_Lean_indentD(v_a_1284_);
v___x_1287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1287_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_);
return v___x_1288_;
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
v_a_1289_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1283_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1283_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(lean_object* v_00_u03b1_1305_, lean_object* v_c_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1306_, v_a_1307_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1319_, lean_object* v_c_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(v_00_u03b1_1319_, v_c_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec(v_a_1321_);
return v_res_1332_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1334_ = l_Lean_mkIntLit(v___x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(lean_object* v_c_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v_p_1339_; lean_object* v___x_1340_; 
v_p_1339_ = lean_ctor_get(v_c_1335_, 0);
lean_inc_ref(v_p_1339_);
lean_dec_ref(v_c_1335_);
v___x_1340_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_1339_, v_a_1336_, v_a_1337_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1351_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1351_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1351_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1345_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1346_ = l_Lean_mkIntEq(v_a_1341_, v___x_1345_);
v___x_1347_ = l_Lean_mkNot(v___x_1346_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1347_);
v___x_1349_ = v___x_1343_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
else
{
return v___x_1340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1352_, v_a_1353_, v_a_1354_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(lean_object* v_c_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1357_, v_a_1358_, v_a_1366_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___boxed(lean_object* v_c_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(v_c_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec(v_a_1371_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert___boxed(lean_object* v_c_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_00___x40___internal___hyg_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = lean_grind_cutsat_assert_le(v_c_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(lean_object* v_c_1408_){
_start:
{
lean_object* v_p_1409_; 
v_p_1409_ = lean_ctor_get(v_c_1408_, 0);
if (lean_obj_tag(v_p_1409_) == 0)
{
lean_object* v_k_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v_k_1410_ = lean_ctor_get(v_p_1409_, 0);
v___x_1411_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1412_ = lean_int_dec_le(v_k_1410_, v___x_1411_);
return v___x_1412_;
}
else
{
uint8_t v___x_1413_; 
v___x_1413_ = 0;
return v___x_1413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial___boxed(lean_object* v_c_1414_){
_start:
{
uint8_t v_res_1415_; lean_object* v_r_1416_; 
v_res_1415_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_c_1414_);
lean_dec_ref(v_c_1414_);
v_r_1416_ = lean_box(v_res_1415_);
return v_r_1416_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0));
v___x_1419_ = l_Lean_stringToMessageData(v___x_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(lean_object* v_c_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v_p_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1441_; 
v_p_1424_ = lean_ctor_get(v_c_1420_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_c_1420_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; 
v_unused_1442_ = lean_ctor_get(v_c_1420_, 1);
lean_dec(v_unused_1442_);
v___x_1426_ = v_c_1420_;
v_isShared_1427_ = v_isSharedCheck_1441_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_p_1424_);
lean_dec(v_c_1420_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1441_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Int_Linear_Poly_pp___redArg(v_p_1424_, v_a_1421_, v_a_1422_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1440_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1440_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1440_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1433_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1);
if (v_isShared_1427_ == 0)
{
lean_ctor_set_tag(v___x_1426_, 7);
lean_ctor_set(v___x_1426_, 1, v___x_1433_);
lean_ctor_set(v___x_1426_, 0, v_a_1429_);
v___x_1435_ = v___x_1426_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1429_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1437_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1435_);
v___x_1437_ = v___x_1431_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
else
{
lean_del_object(v___x_1426_);
return v___x_1428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___boxed(lean_object* v_c_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1443_, v_a_1444_, v_a_1445_);
lean_dec_ref(v_a_1445_);
lean_dec(v_a_1444_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(lean_object* v_c_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1448_, v_a_1449_, v_a_1457_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___boxed(lean_object* v_c_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(v_c_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
lean_dec(v_a_1463_);
lean_dec(v_a_1462_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(lean_object* v_c_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_p_1478_; lean_object* v___x_1479_; 
v_p_1478_ = lean_ctor_get(v_c_1474_, 0);
lean_inc_ref(v_p_1478_);
lean_dec_ref(v_c_1474_);
v___x_1479_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_1478_, v_a_1475_, v_a_1476_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1489_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1489_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1489_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1484_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1485_ = l_Lean_mkIntLE(v_a_1480_, v___x_1484_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1485_);
v___x_1487_ = v___x_1482_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
else
{
return v___x_1479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1490_, v_a_1491_, v_a_1492_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(lean_object* v_c_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1495_, v_a_1496_, v_a_1504_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___boxed(lean_object* v_c_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(v_c_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
lean_dec(v_a_1514_);
lean_dec_ref(v_a_1513_);
lean_dec(v_a_1512_);
lean_dec_ref(v_a_1511_);
lean_dec(v_a_1510_);
lean_dec(v_a_1509_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(lean_object* v_c_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1521_, v_a_1522_, v_a_1525_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref(v___x_1528_);
v___x_1530_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1531_ = l_Lean_indentD(v_a_1529_);
v___x_1532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1532_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
return v___x_1533_;
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
v_a_1534_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1528_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1528_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
lean_dec(v_a_1547_);
lean_dec_ref(v_a_1546_);
lean_dec(v_a_1545_);
lean_dec_ref(v_a_1544_);
lean_dec(v_a_1543_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(lean_object* v_00_u03b1_1550_, lean_object* v_c_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1551_, v_a_1552_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1564_, lean_object* v_c_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(v_00_u03b1_1564_, v_c_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
lean_dec(v_a_1573_);
lean_dec_ref(v_a_1572_);
lean_dec(v_a_1571_);
lean_dec_ref(v_a_1570_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec(v_a_1567_);
lean_dec(v_a_1566_);
return v_res_1577_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(lean_object* v_c_1578_){
_start:
{
lean_object* v_p_1579_; 
v_p_1579_ = lean_ctor_get(v_c_1578_, 0);
if (lean_obj_tag(v_p_1579_) == 0)
{
lean_object* v_k_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v_k_1580_ = lean_ctor_get(v_p_1579_, 0);
v___x_1581_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1582_ = lean_int_dec_eq(v_k_1580_, v___x_1581_);
return v___x_1582_;
}
else
{
uint8_t v___x_1583_; 
v___x_1583_ = 0;
return v___x_1583_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial___boxed(lean_object* v_c_1584_){
_start:
{
uint8_t v_res_1585_; lean_object* v_r_1586_; 
v_res_1585_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(v_c_1584_);
lean_dec_ref(v_c_1584_);
v_r_1586_ = lean_box(v_res_1585_);
return v_r_1586_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0));
v___x_1589_ = l_Lean_stringToMessageData(v___x_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object* v_c_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_p_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1611_; 
v_p_1594_ = lean_ctor_get(v_c_1590_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_c_1590_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; 
v_unused_1612_ = lean_ctor_get(v_c_1590_, 1);
lean_dec(v_unused_1612_);
v___x_1596_ = v_c_1590_;
v_isShared_1597_ = v_isSharedCheck_1611_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_p_1594_);
lean_dec(v_c_1590_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1611_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Int_Linear_Poly_pp___redArg(v_p_1594_, v_a_1591_, v_a_1592_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1610_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1601_ = v___x_1598_;
v_isShared_1602_ = v_isSharedCheck_1610_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1610_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1603_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1);
if (v_isShared_1597_ == 0)
{
lean_ctor_set_tag(v___x_1596_, 7);
lean_ctor_set(v___x_1596_, 1, v___x_1603_);
lean_ctor_set(v___x_1596_, 0, v_a_1599_);
v___x_1605_ = v___x_1596_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1599_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1607_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1605_);
v___x_1607_ = v___x_1601_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
else
{
lean_del_object(v___x_1596_);
return v___x_1598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___boxed(lean_object* v_c_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1613_, v_a_1614_, v_a_1615_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(lean_object* v_c_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1618_, v_a_1619_, v_a_1627_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___boxed(lean_object* v_c_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(v_c_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
lean_dec(v_a_1641_);
lean_dec_ref(v_a_1640_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
lean_dec(v_a_1633_);
lean_dec(v_a_1632_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(lean_object* v_c_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_p_1648_; lean_object* v___x_1649_; 
v_p_1648_ = lean_ctor_get(v_c_1644_, 0);
lean_inc_ref(v_p_1648_);
lean_dec_ref(v_c_1644_);
v___x_1649_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_1648_, v_a_1645_, v_a_1646_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1659_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1659_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1659_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1654_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1655_ = l_Lean_mkIntEq(v_a_1650_, v___x_1654_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v___x_1655_);
v___x_1657_ = v___x_1652_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
else
{
return v___x_1649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1660_, v_a_1661_, v_a_1662_);
lean_dec_ref(v_a_1662_);
lean_dec(v_a_1661_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(lean_object* v_c_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1665_, v_a_1666_, v_a_1674_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___boxed(lean_object* v_c_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(v_c_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec(v_a_1679_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(lean_object* v_c_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1691_, v_a_1692_, v_a_1695_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref(v___x_1698_);
v___x_1700_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1701_ = l_Lean_indentD(v_a_1699_);
v___x_1702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1700_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
v___x_1703_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1702_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
return v___x_1703_;
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
v_a_1704_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1698_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1698_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(lean_object* v_00_u03b1_1720_, lean_object* v_c_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_1721_, v_a_1722_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1734_, lean_object* v_c_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(v_00_u03b1_1734_, v_c_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec(v_a_1743_);
lean_dec_ref(v_a_1742_);
lean_dec(v_a_1741_);
lean_dec_ref(v_a_1740_);
lean_dec(v_a_1739_);
lean_dec_ref(v_a_1738_);
lean_dec(v_a_1737_);
lean_dec(v_a_1736_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(lean_object* v_x_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1749_, v_a_1750_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1769_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1769_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1769_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v_occurs_1757_; lean_object* v_size_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v_occurs_1757_ = lean_ctor_get(v_a_1753_, 12);
lean_inc_ref(v_occurs_1757_);
lean_dec(v_a_1753_);
v_size_1758_ = lean_ctor_get(v_occurs_1757_, 2);
v___x_1759_ = lean_box(1);
v___x_1760_ = lean_nat_dec_lt(v_x_1748_, v_size_1758_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1763_; 
lean_dec_ref(v_occurs_1757_);
v___x_1761_ = l_outOfBounds___redArg(v___x_1759_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1761_);
v___x_1763_ = v___x_1755_;
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
else
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1765_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1759_, v_occurs_1757_, v_x_1748_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1765_);
v___x_1767_ = v___x_1755_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
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
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
v_a_1770_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1752_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1752_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg___boxed(lean_object* v_x_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_1778_, v_a_1779_, v_a_1780_);
lean_dec_ref(v_a_1780_);
lean_dec(v_a_1779_);
lean_dec(v_x_1778_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(lean_object* v_x_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_1783_, v_a_1784_, v_a_1792_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___boxed(lean_object* v_x_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(v_x_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
lean_dec(v_a_1806_);
lean_dec_ref(v_a_1805_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
lean_dec(v_a_1802_);
lean_dec_ref(v_a_1801_);
lean_dec(v_a_1800_);
lean_dec_ref(v_a_1799_);
lean_dec(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec(v_x_1796_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(lean_object* v_k_1809_, lean_object* v_v_1810_, lean_object* v_t_1811_){
_start:
{
if (lean_obj_tag(v_t_1811_) == 0)
{
lean_object* v_size_1812_; lean_object* v_k_1813_; lean_object* v_v_1814_; lean_object* v_l_1815_; lean_object* v_r_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_2097_; 
v_size_1812_ = lean_ctor_get(v_t_1811_, 0);
v_k_1813_ = lean_ctor_get(v_t_1811_, 1);
v_v_1814_ = lean_ctor_get(v_t_1811_, 2);
v_l_1815_ = lean_ctor_get(v_t_1811_, 3);
v_r_1816_ = lean_ctor_get(v_t_1811_, 4);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_t_1811_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_1818_ = v_t_1811_;
v_isShared_1819_ = v_isSharedCheck_2097_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_r_1816_);
lean_inc(v_l_1815_);
lean_inc(v_v_1814_);
lean_inc(v_k_1813_);
lean_inc(v_size_1812_);
lean_dec(v_t_1811_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_2097_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
uint8_t v___x_1820_; 
v___x_1820_ = lean_nat_dec_lt(v_k_1809_, v_k_1813_);
if (v___x_1820_ == 0)
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_nat_dec_eq(v_k_1809_, v_k_1813_);
if (v___x_1821_ == 0)
{
lean_object* v_impl_1822_; lean_object* v___x_1823_; 
lean_dec(v_size_1812_);
v_impl_1822_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_1809_, v_v_1810_, v_r_1816_);
v___x_1823_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1815_) == 0)
{
lean_object* v_size_1824_; lean_object* v_size_1825_; lean_object* v_k_1826_; lean_object* v_v_1827_; lean_object* v_l_1828_; lean_object* v_r_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v_size_1824_ = lean_ctor_get(v_l_1815_, 0);
v_size_1825_ = lean_ctor_get(v_impl_1822_, 0);
lean_inc(v_size_1825_);
v_k_1826_ = lean_ctor_get(v_impl_1822_, 1);
lean_inc(v_k_1826_);
v_v_1827_ = lean_ctor_get(v_impl_1822_, 2);
lean_inc(v_v_1827_);
v_l_1828_ = lean_ctor_get(v_impl_1822_, 3);
lean_inc(v_l_1828_);
v_r_1829_ = lean_ctor_get(v_impl_1822_, 4);
lean_inc(v_r_1829_);
v___x_1830_ = lean_unsigned_to_nat(3u);
v___x_1831_ = lean_nat_mul(v___x_1830_, v_size_1824_);
v___x_1832_ = lean_nat_dec_lt(v___x_1831_, v_size_1825_);
lean_dec(v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1836_; 
lean_dec(v_r_1829_);
lean_dec(v_l_1828_);
lean_dec(v_v_1827_);
lean_dec(v_k_1826_);
v___x_1833_ = lean_nat_add(v___x_1823_, v_size_1824_);
v___x_1834_ = lean_nat_add(v___x_1833_, v_size_1825_);
lean_dec(v_size_1825_);
lean_dec(v___x_1833_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 4, v_impl_1822_);
lean_ctor_set(v___x_1818_, 0, v___x_1834_);
v___x_1836_ = v___x_1818_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_k_1813_);
lean_ctor_set(v_reuseFailAlloc_1837_, 2, v_v_1814_);
lean_ctor_set(v_reuseFailAlloc_1837_, 3, v_l_1815_);
lean_ctor_set(v_reuseFailAlloc_1837_, 4, v_impl_1822_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
else
{
lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1901_; 
v_isSharedCheck_1901_ = !lean_is_exclusive(v_impl_1822_);
if (v_isSharedCheck_1901_ == 0)
{
lean_object* v_unused_1902_; lean_object* v_unused_1903_; lean_object* v_unused_1904_; lean_object* v_unused_1905_; lean_object* v_unused_1906_; 
v_unused_1902_ = lean_ctor_get(v_impl_1822_, 4);
lean_dec(v_unused_1902_);
v_unused_1903_ = lean_ctor_get(v_impl_1822_, 3);
lean_dec(v_unused_1903_);
v_unused_1904_ = lean_ctor_get(v_impl_1822_, 2);
lean_dec(v_unused_1904_);
v_unused_1905_ = lean_ctor_get(v_impl_1822_, 1);
lean_dec(v_unused_1905_);
v_unused_1906_ = lean_ctor_get(v_impl_1822_, 0);
lean_dec(v_unused_1906_);
v___x_1839_ = v_impl_1822_;
v_isShared_1840_ = v_isSharedCheck_1901_;
goto v_resetjp_1838_;
}
else
{
lean_dec(v_impl_1822_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1901_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v_size_1841_; lean_object* v_k_1842_; lean_object* v_v_1843_; lean_object* v_l_1844_; lean_object* v_r_1845_; lean_object* v_size_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v_size_1841_ = lean_ctor_get(v_l_1828_, 0);
v_k_1842_ = lean_ctor_get(v_l_1828_, 1);
v_v_1843_ = lean_ctor_get(v_l_1828_, 2);
v_l_1844_ = lean_ctor_get(v_l_1828_, 3);
v_r_1845_ = lean_ctor_get(v_l_1828_, 4);
v_size_1846_ = lean_ctor_get(v_r_1829_, 0);
v___x_1847_ = lean_unsigned_to_nat(2u);
v___x_1848_ = lean_nat_mul(v___x_1847_, v_size_1846_);
v___x_1849_ = lean_nat_dec_lt(v_size_1841_, v___x_1848_);
lean_dec(v___x_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1877_; 
lean_inc(v_r_1845_);
lean_inc(v_l_1844_);
lean_inc(v_v_1843_);
lean_inc(v_k_1842_);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_l_1828_);
if (v_isSharedCheck_1877_ == 0)
{
lean_object* v_unused_1878_; lean_object* v_unused_1879_; lean_object* v_unused_1880_; lean_object* v_unused_1881_; lean_object* v_unused_1882_; 
v_unused_1878_ = lean_ctor_get(v_l_1828_, 4);
lean_dec(v_unused_1878_);
v_unused_1879_ = lean_ctor_get(v_l_1828_, 3);
lean_dec(v_unused_1879_);
v_unused_1880_ = lean_ctor_get(v_l_1828_, 2);
lean_dec(v_unused_1880_);
v_unused_1881_ = lean_ctor_get(v_l_1828_, 1);
lean_dec(v_unused_1881_);
v_unused_1882_ = lean_ctor_get(v_l_1828_, 0);
lean_dec(v_unused_1882_);
v___x_1851_ = v_l_1828_;
v_isShared_1852_ = v_isSharedCheck_1877_;
goto v_resetjp_1850_;
}
else
{
lean_dec(v_l_1828_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1877_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1867_; 
v___x_1853_ = lean_nat_add(v___x_1823_, v_size_1824_);
v___x_1854_ = lean_nat_add(v___x_1853_, v_size_1825_);
lean_dec(v_size_1825_);
if (lean_obj_tag(v_l_1844_) == 0)
{
lean_object* v_size_1875_; 
v_size_1875_ = lean_ctor_get(v_l_1844_, 0);
lean_inc(v_size_1875_);
v___y_1867_ = v_size_1875_;
goto v___jp_1866_;
}
else
{
lean_object* v___x_1876_; 
v___x_1876_ = lean_unsigned_to_nat(0u);
v___y_1867_ = v___x_1876_;
goto v___jp_1866_;
}
v___jp_1855_:
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1859_ = lean_nat_add(v___y_1856_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec(v___y_1856_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 4, v_r_1829_);
lean_ctor_set(v___x_1851_, 3, v_r_1845_);
lean_ctor_set(v___x_1851_, 2, v_v_1827_);
lean_ctor_set(v___x_1851_, 1, v_k_1826_);
lean_ctor_set(v___x_1851_, 0, v___x_1859_);
v___x_1861_ = v___x_1851_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1859_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_k_1826_);
lean_ctor_set(v_reuseFailAlloc_1865_, 2, v_v_1827_);
lean_ctor_set(v_reuseFailAlloc_1865_, 3, v_r_1845_);
lean_ctor_set(v_reuseFailAlloc_1865_, 4, v_r_1829_);
v___x_1861_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1863_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 4, v___x_1861_);
lean_ctor_set(v___x_1839_, 3, v___y_1857_);
lean_ctor_set(v___x_1839_, 2, v_v_1843_);
lean_ctor_set(v___x_1839_, 1, v_k_1842_);
lean_ctor_set(v___x_1839_, 0, v___x_1854_);
v___x_1863_ = v___x_1839_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_k_1842_);
lean_ctor_set(v_reuseFailAlloc_1864_, 2, v_v_1843_);
lean_ctor_set(v_reuseFailAlloc_1864_, 3, v___y_1857_);
lean_ctor_set(v_reuseFailAlloc_1864_, 4, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
v___jp_1866_:
{
lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1868_ = lean_nat_add(v___x_1853_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec(v___x_1853_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 4, v_l_1844_);
lean_ctor_set(v___x_1818_, 0, v___x_1868_);
v___x_1870_ = v___x_1818_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_k_1813_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v_v_1814_);
lean_ctor_set(v_reuseFailAlloc_1874_, 3, v_l_1815_);
lean_ctor_set(v_reuseFailAlloc_1874_, 4, v_l_1844_);
v___x_1870_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_nat_add(v___x_1823_, v_size_1846_);
if (lean_obj_tag(v_r_1845_) == 0)
{
lean_object* v_size_1872_; 
v_size_1872_ = lean_ctor_get(v_r_1845_, 0);
lean_inc(v_size_1872_);
v___y_1856_ = v___x_1871_;
v___y_1857_ = v___x_1870_;
v___y_1858_ = v_size_1872_;
goto v___jp_1855_;
}
else
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_unsigned_to_nat(0u);
v___y_1856_ = v___x_1871_;
v___y_1857_ = v___x_1870_;
v___y_1858_ = v___x_1873_;
goto v___jp_1855_;
}
}
}
}
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1887_; 
lean_del_object(v___x_1818_);
v___x_1883_ = lean_nat_add(v___x_1823_, v_size_1824_);
v___x_1884_ = lean_nat_add(v___x_1883_, v_size_1825_);
lean_dec(v_size_1825_);
v___x_1885_ = lean_nat_add(v___x_1883_, v_size_1841_);
lean_dec(v___x_1883_);
lean_inc_ref(v_l_1815_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 4, v_l_1828_);
lean_ctor_set(v___x_1839_, 3, v_l_1815_);
lean_ctor_set(v___x_1839_, 2, v_v_1814_);
lean_ctor_set(v___x_1839_, 1, v_k_1813_);
lean_ctor_set(v___x_1839_, 0, v___x_1885_);
v___x_1887_ = v___x_1839_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_k_1813_);
lean_ctor_set(v_reuseFailAlloc_1900_, 2, v_v_1814_);
lean_ctor_set(v_reuseFailAlloc_1900_, 3, v_l_1815_);
lean_ctor_set(v_reuseFailAlloc_1900_, 4, v_l_1828_);
v___x_1887_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
v_isSharedCheck_1894_ = !lean_is_exclusive(v_l_1815_);
if (v_isSharedCheck_1894_ == 0)
{
lean_object* v_unused_1895_; lean_object* v_unused_1896_; lean_object* v_unused_1897_; lean_object* v_unused_1898_; lean_object* v_unused_1899_; 
v_unused_1895_ = lean_ctor_get(v_l_1815_, 4);
lean_dec(v_unused_1895_);
v_unused_1896_ = lean_ctor_get(v_l_1815_, 3);
lean_dec(v_unused_1896_);
v_unused_1897_ = lean_ctor_get(v_l_1815_, 2);
lean_dec(v_unused_1897_);
v_unused_1898_ = lean_ctor_get(v_l_1815_, 1);
lean_dec(v_unused_1898_);
v_unused_1899_ = lean_ctor_get(v_l_1815_, 0);
lean_dec(v_unused_1899_);
v___x_1889_ = v_l_1815_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_dec(v_l_1815_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 4, v_r_1829_);
lean_ctor_set(v___x_1889_, 3, v___x_1887_);
lean_ctor_set(v___x_1889_, 2, v_v_1827_);
lean_ctor_set(v___x_1889_, 1, v_k_1826_);
lean_ctor_set(v___x_1889_, 0, v___x_1884_);
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_k_1826_);
lean_ctor_set(v_reuseFailAlloc_1893_, 2, v_v_1827_);
lean_ctor_set(v_reuseFailAlloc_1893_, 3, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1893_, 4, v_r_1829_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1907_; 
v_l_1907_ = lean_ctor_get(v_impl_1822_, 3);
lean_inc(v_l_1907_);
if (lean_obj_tag(v_l_1907_) == 0)
{
lean_object* v_r_1908_; lean_object* v_k_1909_; lean_object* v_v_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1933_; 
v_r_1908_ = lean_ctor_get(v_impl_1822_, 4);
v_k_1909_ = lean_ctor_get(v_impl_1822_, 1);
v_v_1910_ = lean_ctor_get(v_impl_1822_, 2);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_impl_1822_);
if (v_isSharedCheck_1933_ == 0)
{
lean_object* v_unused_1934_; lean_object* v_unused_1935_; 
v_unused_1934_ = lean_ctor_get(v_impl_1822_, 3);
lean_dec(v_unused_1934_);
v_unused_1935_ = lean_ctor_get(v_impl_1822_, 0);
lean_dec(v_unused_1935_);
v___x_1912_ = v_impl_1822_;
v_isShared_1913_ = v_isSharedCheck_1933_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_r_1908_);
lean_inc(v_v_1910_);
lean_inc(v_k_1909_);
lean_dec(v_impl_1822_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1933_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v_k_1914_; lean_object* v_v_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1929_; 
v_k_1914_ = lean_ctor_get(v_l_1907_, 1);
v_v_1915_ = lean_ctor_get(v_l_1907_, 2);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_l_1907_);
if (v_isSharedCheck_1929_ == 0)
{
lean_object* v_unused_1930_; lean_object* v_unused_1931_; lean_object* v_unused_1932_; 
v_unused_1930_ = lean_ctor_get(v_l_1907_, 4);
lean_dec(v_unused_1930_);
v_unused_1931_ = lean_ctor_get(v_l_1907_, 3);
lean_dec(v_unused_1931_);
v_unused_1932_ = lean_ctor_get(v_l_1907_, 0);
lean_dec(v_unused_1932_);
v___x_1917_ = v_l_1907_;
v_isShared_1918_ = v_isSharedCheck_1929_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_v_1915_);
lean_inc(v_k_1914_);
lean_dec(v_l_1907_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1929_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1919_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1908_, 2);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 4, v_r_1908_);
lean_ctor_set(v___x_1917_, 3, v_r_1908_);
lean_ctor_set(v___x_1917_, 2, v_v_1814_);
lean_ctor_set(v___x_1917_, 1, v_k_1813_);
lean_ctor_set(v___x_1917_, 0, v___x_1823_);
v___x_1921_ = v___x_1917_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_k_1813_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v_v_1814_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v_r_1908_);
lean_ctor_set(v_reuseFailAlloc_1928_, 4, v_r_1908_);
v___x_1921_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1923_; 
lean_inc(v_r_1908_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 3, v_r_1908_);
lean_ctor_set(v___x_1912_, 0, v___x_1823_);
v___x_1923_ = v___x_1912_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_k_1909_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v_v_1910_);
lean_ctor_set(v_reuseFailAlloc_1927_, 3, v_r_1908_);
lean_ctor_set(v_reuseFailAlloc_1927_, 4, v_r_1908_);
v___x_1923_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1925_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 4, v___x_1923_);
lean_ctor_set(v___x_1818_, 3, v___x_1921_);
lean_ctor_set(v___x_1818_, 2, v_v_1915_);
lean_ctor_set(v___x_1818_, 1, v_k_1914_);
lean_ctor_set(v___x_1818_, 0, v___x_1919_);
v___x_1925_ = v___x_1818_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1919_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v_k_1914_);
lean_ctor_set(v_reuseFailAlloc_1926_, 2, v_v_1915_);
lean_ctor_set(v_reuseFailAlloc_1926_, 3, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1926_, 4, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
}
else
{
lean_object* v_r_1936_; 
v_r_1936_ = lean_ctor_get(v_impl_1822_, 4);
lean_inc(v_r_1936_);
if (lean_obj_tag(v_r_1936_) == 0)
{
lean_object* v_k_1937_; lean_object* v_v_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1949_; 
v_k_1937_ = lean_ctor_get(v_impl_1822_, 1);
v_v_1938_ = lean_ctor_get(v_impl_1822_, 2);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_impl_1822_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; lean_object* v_unused_1951_; lean_object* v_unused_1952_; 
v_unused_1950_ = lean_ctor_get(v_impl_1822_, 4);
lean_dec(v_unused_1950_);
v_unused_1951_ = lean_ctor_get(v_impl_1822_, 3);
lean_dec(v_unused_1951_);
v_unused_1952_ = lean_ctor_get(v_impl_1822_, 0);
lean_dec(v_unused_1952_);
v___x_1940_ = v_impl_1822_;
v_isShared_1941_ = v_isSharedCheck_1949_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_v_1938_);
lean_inc(v_k_1937_);
lean_dec(v_impl_1822_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1949_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1942_ = lean_unsigned_to_nat(3u);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 4, v_l_1907_);
lean_ctor_set(v___x_1940_, 2, v_v_1814_);
lean_ctor_set(v___x_1940_, 1, v_k_1813_);
lean_ctor_set(v___x_1940_, 0, v___x_1823_);
v___x_1944_ = v___x_1940_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_k_1813_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v_v_1814_);
lean_ctor_set(v_reuseFailAlloc_1948_, 3, v_l_1907_);
lean_ctor_set(v_reuseFailAlloc_1948_, 4, v_l_1907_);
v___x_1944_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1946_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 4, v_r_1936_);
lean_ctor_set(v___x_1818_, 3, v___x_1944_);
lean_ctor_set(v___x_1818_, 2, v_v_1938_);
lean_ctor_set(v___x_1818_, 1, v_k_1937_);
lean_ctor_set(v___x_1818_, 0, v___x_1942_);
v___x_1946_ = v___x_1818_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1942_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_k_1937_);
lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_v_1938_);
lean_ctor_set(v_reuseFailAlloc_1947_, 3, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_1947_, 4, v_r_1936_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1953_ = lean_unsigned_to_nat(2u);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 4, v_impl_1822_);
lean_ctor_set(v___x_1818_, 3, v_r_1936_);
lean_ctor_set(v___x_1818_, 0, v___x_1953_);
v___x_1955_ = v___x_1818_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_k_1813_);
lean_ctor_set(v_reuseFailAlloc_1956_, 2, v_v_1814_);
lean_ctor_set(v_reuseFailAlloc_1956_, 3, v_r_1936_);
lean_ctor_set(v_reuseFailAlloc_1956_, 4, v_impl_1822_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
else
{
lean_object* v___x_1958_; 
lean_dec(v_v_1814_);
lean_dec(v_k_1813_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 2, v_v_1810_);
lean_ctor_set(v___x_1818_, 1, v_k_1809_);
v___x_1958_ = v___x_1818_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_size_1812_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_k_1809_);
lean_ctor_set(v_reuseFailAlloc_1959_, 2, v_v_1810_);
lean_ctor_set(v_reuseFailAlloc_1959_, 3, v_l_1815_);
lean_ctor_set(v_reuseFailAlloc_1959_, 4, v_r_1816_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
else
{
lean_object* v_impl_1960_; lean_object* v___x_1961_; 
lean_dec(v_size_1812_);
v_impl_1960_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_1809_, v_v_1810_, v_l_1815_);
v___x_1961_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1816_) == 0)
{
lean_object* v_size_1962_; lean_object* v_size_1963_; lean_object* v_k_1964_; lean_object* v_v_1965_; lean_object* v_l_1966_; lean_object* v_r_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
v_size_1962_ = lean_ctor_get(v_r_1816_, 0);
v_size_1963_ = lean_ctor_get(v_impl_1960_, 0);
lean_inc(v_size_1963_);
v_k_1964_ = lean_ctor_get(v_impl_1960_, 1);
lean_inc(v_k_1964_);
v_v_1965_ = lean_ctor_get(v_impl_1960_, 2);
lean_inc(v_v_1965_);
v_l_1966_ = lean_ctor_get(v_impl_1960_, 3);
lean_inc(v_l_1966_);
v_r_1967_ = lean_ctor_get(v_impl_1960_, 4);
lean_inc(v_r_1967_);
v___x_1968_ = lean_unsigned_to_nat(3u);
v___x_1969_ = lean_nat_mul(v___x_1968_, v_size_1962_);
v___x_1970_ = lean_nat_dec_lt(v___x_1969_, v_size_1963_);
lean_dec(v___x_1969_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1974_; 
lean_dec(v_r_1967_);
lean_dec(v_l_1966_);
lean_dec(v_v_1965_);
lean_dec(v_k_1964_);
v___x_1971_ = lean_nat_add(v___x_1961_, v_size_1963_);
lean_dec(v_size_1963_);
v___x_1972_ = lean_nat_add(v___x_1971_, v_size_1962_);
lean_dec(v___x_1971_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 3, v_impl_1960_);
lean_ctor_set(v___x_1818_, 0, v___x_1972_);
v___x_1974_ = v___x_1818_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_k_1813_);
lean_ctor_set(v_reuseFailAlloc_1975_, 2, v_v_1814_);
lean_ctor_set(v_reuseFailAlloc_1975_, 3, v_impl_1960_);
lean_ctor_set(v_reuseFailAlloc_1975_, 4, v_r_1816_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
else
{
lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2041_; 
v_isSharedCheck_2041_ = !lean_is_exclusive(v_impl_1960_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; lean_object* v_unused_2043_; lean_object* v_unused_2044_; lean_object* v_unused_2045_; lean_object* v_unused_2046_; 
v_unused_2042_ = lean_ctor_get(v_impl_1960_, 4);
lean_dec(v_unused_2042_);
v_unused_2043_ = lean_ctor_get(v_impl_1960_, 3);
lean_dec(v_unused_2043_);
v_unused_2044_ = lean_ctor_get(v_impl_1960_, 2);
lean_dec(v_unused_2044_);
v_unused_2045_ = lean_ctor_get(v_impl_1960_, 1);
lean_dec(v_unused_2045_);
v_unused_2046_ = lean_ctor_get(v_impl_1960_, 0);
lean_dec(v_unused_2046_);
v___x_1977_ = v_impl_1960_;
v_isShared_1978_ = v_isSharedCheck_2041_;
goto v_resetjp_1976_;
}
else
{
lean_dec(v_impl_1960_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2041_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v_size_1979_; lean_object* v_size_1980_; lean_object* v_k_1981_; lean_object* v_v_1982_; lean_object* v_l_1983_; lean_object* v_r_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v_size_1979_ = lean_ctor_get(v_l_1966_, 0);
v_size_1980_ = lean_ctor_get(v_r_1967_, 0);
v_k_1981_ = lean_ctor_get(v_r_1967_, 1);
v_v_1982_ = lean_ctor_get(v_r_1967_, 2);
v_l_1983_ = lean_ctor_get(v_r_1967_, 3);
v_r_1984_ = lean_ctor_get(v_r_1967_, 4);
v___x_1985_ = lean_unsigned_to_nat(2u);
v___x_1986_ = lean_nat_mul(v___x_1985_, v_size_1979_);
v___x_1987_ = lean_nat_dec_lt(v_size_1980_, v___x_1986_);
lean_dec(v___x_1986_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2016_; 
lean_inc(v_r_1984_);
lean_inc(v_l_1983_);
lean_inc(v_v_1982_);
lean_inc(v_k_1981_);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_r_1967_);
if (v_isSharedCheck_2016_ == 0)
{
lean_object* v_unused_2017_; lean_object* v_unused_2018_; lean_object* v_unused_2019_; lean_object* v_unused_2020_; lean_object* v_unused_2021_; 
v_unused_2017_ = lean_ctor_get(v_r_1967_, 4);
lean_dec(v_unused_2017_);
v_unused_2018_ = lean_ctor_get(v_r_1967_, 3);
lean_dec(v_unused_2018_);
v_unused_2019_ = lean_ctor_get(v_r_1967_, 2);
lean_dec(v_unused_2019_);
v_unused_2020_ = lean_ctor_get(v_r_1967_, 1);
lean_dec(v_unused_2020_);
v_unused_2021_ = lean_ctor_get(v_r_1967_, 0);
lean_dec(v_unused_2021_);
v___x_1989_ = v_r_1967_;
v_isShared_1990_ = v_isSharedCheck_2016_;
goto v_resetjp_1988_;
}
else
{
lean_dec(v_r_1967_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2016_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___x_2004_; lean_object* v___y_2006_; 
v___x_1991_ = lean_nat_add(v___x_1961_, v_size_1963_);
lean_dec(v_size_1963_);
v___x_1992_ = lean_nat_add(v___x_1991_, v_size_1962_);
lean_dec(v___x_1991_);
v___x_2004_ = lean_nat_add(v___x_1961_, v_size_1979_);
if (lean_obj_tag(v_l_1983_) == 0)
{
lean_object* v_size_2014_; 
v_size_2014_ = lean_ctor_get(v_l_1983_, 0);
lean_inc(v_size_2014_);
v___y_2006_ = v_size_2014_;
goto v___jp_2005_;
}
else
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_unsigned_to_nat(0u);
v___y_2006_ = v___x_2015_;
goto v___jp_2005_;
}
v___jp_1993_:
{
lean_object* v___x_1997_; lean_object* v___x_1999_; 
v___x_1997_ = lean_nat_add(v___y_1994_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec(v___y_1994_);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 4, v_r_1816_);
lean_ctor_set(v___x_1989_, 3, v_r_1984_);
lean_ctor_set(v___x_1989_, 2, v_v_1814_);
lean_ctor_set(v___x_1989_, 1, v_k_1813_);
lean_ctor_set(v___x_1989_, 0, v___x_1997_);
v___x_1999_ = v___x_1989_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_k_1813_);
lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_v_1814_);
lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_r_1984_);
lean_ctor_set(v_reuseFailAlloc_2003_, 4, v_r_1816_);
v___x_1999_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2001_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 4, v___x_1999_);
lean_ctor_set(v___x_1977_, 3, v___y_1995_);
lean_ctor_set(v___x_1977_, 2, v_v_1982_);
lean_ctor_set(v___x_1977_, 1, v_k_1981_);
lean_ctor_set(v___x_1977_, 0, v___x_1992_);
v___x_2001_ = v___x_1977_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_k_1981_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v_v_1982_);
lean_ctor_set(v_reuseFailAlloc_2002_, 3, v___y_1995_);
lean_ctor_set(v_reuseFailAlloc_2002_, 4, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
v___jp_2005_:
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2007_ = lean_nat_add(v___x_2004_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec(v___x_2004_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 4, v_l_1983_);
lean_ctor_set(v___x_1818_, 3, v_l_1966_);
lean_ctor_set(v___x_1818_, 2, v_v_1965_);
lean_ctor_set(v___x_1818_, 1, v_k_1964_);
lean_ctor_set(v___x_1818_, 0, v___x_2007_);
v___x_2009_ = v___x_1818_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_k_1964_);
lean_ctor_set(v_reuseFailAlloc_2013_, 2, v_v_1965_);
lean_ctor_set(v_reuseFailAlloc_2013_, 3, v_l_1966_);
lean_ctor_set(v_reuseFailAlloc_2013_, 4, v_l_1983_);
v___x_2009_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_nat_add(v___x_1961_, v_size_1962_);
if (lean_obj_tag(v_r_1984_) == 0)
{
lean_object* v_size_2011_; 
v_size_2011_ = lean_ctor_get(v_r_1984_, 0);
lean_inc(v_size_2011_);
v___y_1994_ = v___x_2010_;
v___y_1995_ = v___x_2009_;
v___y_1996_ = v_size_2011_;
goto v___jp_1993_;
}
else
{
lean_object* v___x_2012_; 
v___x_2012_ = lean_unsigned_to_nat(0u);
v___y_1994_ = v___x_2010_;
v___y_1995_ = v___x_2009_;
v___y_1996_ = v___x_2012_;
goto v___jp_1993_;
}
}
}
}
}
else
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
lean_del_object(v___x_1818_);
v___x_2022_ = lean_nat_add(v___x_1961_, v_size_1963_);
lean_dec(v_size_1963_);
v___x_2023_ = lean_nat_add(v___x_2022_, v_size_1962_);
lean_dec(v___x_2022_);
v___x_2024_ = lean_nat_add(v___x_1961_, v_size_1962_);
v___x_2025_ = lean_nat_add(v___x_2024_, v_size_1980_);
lean_dec(v___x_2024_);
lean_inc_ref(v_r_1816_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 4, v_r_1816_);
lean_ctor_set(v___x_1977_, 3, v_r_1967_);
lean_ctor_set(v___x_1977_, 2, v_v_1814_);
lean_ctor_set(v___x_1977_, 1, v_k_1813_);
lean_ctor_set(v___x_1977_, 0, v___x_2025_);
v___x_2027_ = v___x_1977_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v_k_1813_);
lean_ctor_set(v_reuseFailAlloc_2040_, 2, v_v_1814_);
lean_ctor_set(v_reuseFailAlloc_2040_, 3, v_r_1967_);
lean_ctor_set(v_reuseFailAlloc_2040_, 4, v_r_1816_);
v___x_2027_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
v_isSharedCheck_2034_ = !lean_is_exclusive(v_r_1816_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; lean_object* v_unused_2036_; lean_object* v_unused_2037_; lean_object* v_unused_2038_; lean_object* v_unused_2039_; 
v_unused_2035_ = lean_ctor_get(v_r_1816_, 4);
lean_dec(v_unused_2035_);
v_unused_2036_ = lean_ctor_get(v_r_1816_, 3);
lean_dec(v_unused_2036_);
v_unused_2037_ = lean_ctor_get(v_r_1816_, 2);
lean_dec(v_unused_2037_);
v_unused_2038_ = lean_ctor_get(v_r_1816_, 1);
lean_dec(v_unused_2038_);
v_unused_2039_ = lean_ctor_get(v_r_1816_, 0);
lean_dec(v_unused_2039_);
v___x_2029_ = v_r_1816_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_dec(v_r_1816_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v___x_2027_);
lean_ctor_set(v___x_2029_, 3, v_l_1966_);
lean_ctor_set(v___x_2029_, 2, v_v_1965_);
lean_ctor_set(v___x_2029_, 1, v_k_1964_);
lean_ctor_set(v___x_2029_, 0, v___x_2023_);
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_k_1964_);
lean_ctor_set(v_reuseFailAlloc_2033_, 2, v_v_1965_);
lean_ctor_set(v_reuseFailAlloc_2033_, 3, v_l_1966_);
lean_ctor_set(v_reuseFailAlloc_2033_, 4, v___x_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2047_; 
v_l_2047_ = lean_ctor_get(v_impl_1960_, 3);
lean_inc(v_l_2047_);
if (lean_obj_tag(v_l_2047_) == 0)
{
lean_object* v_r_2048_; lean_object* v_k_2049_; lean_object* v_v_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2061_; 
v_r_2048_ = lean_ctor_get(v_impl_1960_, 4);
v_k_2049_ = lean_ctor_get(v_impl_1960_, 1);
v_v_2050_ = lean_ctor_get(v_impl_1960_, 2);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_impl_1960_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; lean_object* v_unused_2063_; 
v_unused_2062_ = lean_ctor_get(v_impl_1960_, 3);
lean_dec(v_unused_2062_);
v_unused_2063_ = lean_ctor_get(v_impl_1960_, 0);
lean_dec(v_unused_2063_);
v___x_2052_ = v_impl_1960_;
v_isShared_2053_ = v_isSharedCheck_2061_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_r_2048_);
lean_inc(v_v_2050_);
lean_inc(v_k_2049_);
lean_dec(v_impl_1960_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2061_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2054_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2048_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 3, v_r_2048_);
lean_ctor_set(v___x_2052_, 2, v_v_1814_);
lean_ctor_set(v___x_2052_, 1, v_k_1813_);
lean_ctor_set(v___x_2052_, 0, v___x_1961_);
v___x_2056_ = v___x_2052_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_k_1813_);
lean_ctor_set(v_reuseFailAlloc_2060_, 2, v_v_1814_);
lean_ctor_set(v_reuseFailAlloc_2060_, 3, v_r_2048_);
lean_ctor_set(v_reuseFailAlloc_2060_, 4, v_r_2048_);
v___x_2056_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
lean_object* v___x_2058_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 4, v___x_2056_);
lean_ctor_set(v___x_1818_, 3, v_l_2047_);
lean_ctor_set(v___x_1818_, 2, v_v_2050_);
lean_ctor_set(v___x_1818_, 1, v_k_2049_);
lean_ctor_set(v___x_1818_, 0, v___x_2054_);
v___x_2058_ = v___x_1818_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_k_2049_);
lean_ctor_set(v_reuseFailAlloc_2059_, 2, v_v_2050_);
lean_ctor_set(v_reuseFailAlloc_2059_, 3, v_l_2047_);
lean_ctor_set(v_reuseFailAlloc_2059_, 4, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_object* v_r_2064_; 
v_r_2064_ = lean_ctor_get(v_impl_1960_, 4);
lean_inc(v_r_2064_);
if (lean_obj_tag(v_r_2064_) == 0)
{
lean_object* v_k_2065_; lean_object* v_v_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2089_; 
v_k_2065_ = lean_ctor_get(v_impl_1960_, 1);
v_v_2066_ = lean_ctor_get(v_impl_1960_, 2);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_impl_1960_);
if (v_isSharedCheck_2089_ == 0)
{
lean_object* v_unused_2090_; lean_object* v_unused_2091_; lean_object* v_unused_2092_; 
v_unused_2090_ = lean_ctor_get(v_impl_1960_, 4);
lean_dec(v_unused_2090_);
v_unused_2091_ = lean_ctor_get(v_impl_1960_, 3);
lean_dec(v_unused_2091_);
v_unused_2092_ = lean_ctor_get(v_impl_1960_, 0);
lean_dec(v_unused_2092_);
v___x_2068_ = v_impl_1960_;
v_isShared_2069_ = v_isSharedCheck_2089_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_v_2066_);
lean_inc(v_k_2065_);
lean_dec(v_impl_1960_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2089_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v_k_2070_; lean_object* v_v_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2085_; 
v_k_2070_ = lean_ctor_get(v_r_2064_, 1);
v_v_2071_ = lean_ctor_get(v_r_2064_, 2);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_r_2064_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; lean_object* v_unused_2087_; lean_object* v_unused_2088_; 
v_unused_2086_ = lean_ctor_get(v_r_2064_, 4);
lean_dec(v_unused_2086_);
v_unused_2087_ = lean_ctor_get(v_r_2064_, 3);
lean_dec(v_unused_2087_);
v_unused_2088_ = lean_ctor_get(v_r_2064_, 0);
lean_dec(v_unused_2088_);
v___x_2073_ = v_r_2064_;
v_isShared_2074_ = v_isSharedCheck_2085_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_v_2071_);
lean_inc(v_k_2070_);
lean_dec(v_r_2064_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2085_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2075_ = lean_unsigned_to_nat(3u);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 4, v_l_2047_);
lean_ctor_set(v___x_2073_, 3, v_l_2047_);
lean_ctor_set(v___x_2073_, 2, v_v_2066_);
lean_ctor_set(v___x_2073_, 1, v_k_2065_);
lean_ctor_set(v___x_2073_, 0, v___x_1961_);
v___x_2077_ = v___x_2073_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_k_2065_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_v_2066_);
lean_ctor_set(v_reuseFailAlloc_2084_, 3, v_l_2047_);
lean_ctor_set(v_reuseFailAlloc_2084_, 4, v_l_2047_);
v___x_2077_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_object* v___x_2079_; 
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 4, v_l_2047_);
lean_ctor_set(v___x_2068_, 2, v_v_1814_);
lean_ctor_set(v___x_2068_, 1, v_k_1813_);
lean_ctor_set(v___x_2068_, 0, v___x_1961_);
v___x_2079_ = v___x_2068_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_k_1813_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v_v_1814_);
lean_ctor_set(v_reuseFailAlloc_2083_, 3, v_l_2047_);
lean_ctor_set(v_reuseFailAlloc_2083_, 4, v_l_2047_);
v___x_2079_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2081_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 4, v___x_2079_);
lean_ctor_set(v___x_1818_, 3, v___x_2077_);
lean_ctor_set(v___x_1818_, 2, v_v_2071_);
lean_ctor_set(v___x_1818_, 1, v_k_2070_);
lean_ctor_set(v___x_1818_, 0, v___x_2075_);
v___x_2081_ = v___x_1818_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_k_2070_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v_v_2071_);
lean_ctor_set(v_reuseFailAlloc_2082_, 3, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2082_, 4, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
}
else
{
lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2093_ = lean_unsigned_to_nat(2u);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 4, v_r_2064_);
lean_ctor_set(v___x_1818_, 3, v_impl_1960_);
lean_ctor_set(v___x_1818_, 0, v___x_2093_);
v___x_2095_ = v___x_1818_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_k_1813_);
lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_v_1814_);
lean_ctor_set(v_reuseFailAlloc_2096_, 3, v_impl_1960_);
lean_ctor_set(v_reuseFailAlloc_2096_, 4, v_r_2064_);
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
}
}
}
else
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_unsigned_to_nat(1u);
v___x_2099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v_k_1809_);
lean_ctor_set(v___x_2099_, 2, v_v_1810_);
lean_ctor_set(v___x_2099_, 3, v_t_1811_);
lean_ctor_set(v___x_2099_, 4, v_t_1811_);
return v___x_2099_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(lean_object* v_k_2100_, lean_object* v_t_2101_){
_start:
{
if (lean_obj_tag(v_t_2101_) == 0)
{
lean_object* v_k_2102_; lean_object* v_l_2103_; lean_object* v_r_2104_; uint8_t v___x_2105_; 
v_k_2102_ = lean_ctor_get(v_t_2101_, 1);
v_l_2103_ = lean_ctor_get(v_t_2101_, 3);
v_r_2104_ = lean_ctor_get(v_t_2101_, 4);
v___x_2105_ = lean_nat_dec_lt(v_k_2100_, v_k_2102_);
if (v___x_2105_ == 0)
{
uint8_t v___x_2106_; 
v___x_2106_ = lean_nat_dec_eq(v_k_2100_, v_k_2102_);
if (v___x_2106_ == 0)
{
v_t_2101_ = v_r_2104_;
goto _start;
}
else
{
return v___x_2106_;
}
}
else
{
v_t_2101_ = v_l_2103_;
goto _start;
}
}
else
{
uint8_t v___x_2109_; 
v___x_2109_ = 0;
return v___x_2109_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg___boxed(lean_object* v_k_2110_, lean_object* v_t_2111_){
_start:
{
uint8_t v_res_2112_; lean_object* v_r_2113_; 
v_res_2112_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2110_, v_t_2111_);
lean_dec(v_t_2111_);
lean_dec(v_k_2110_);
v_r_2113_ = lean_box(v_res_2112_);
return v_r_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___redArg(lean_object* v_y_2114_, lean_object* v_x_2115_, size_t v_x_2116_, size_t v_x_2117_){
_start:
{
if (lean_obj_tag(v_x_2115_) == 0)
{
lean_object* v_cs_2118_; size_t v_j_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v_cs_2118_ = lean_ctor_get(v_x_2115_, 0);
v_j_2119_ = lean_usize_shift_right(v_x_2116_, v_x_2117_);
v___x_2120_ = lean_usize_to_nat(v_j_2119_);
v___x_2121_ = lean_array_get_size(v_cs_2118_);
v___x_2122_ = lean_nat_dec_lt(v___x_2120_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_dec(v___x_2120_);
lean_dec(v_y_2114_);
return v_x_2115_;
}
else
{
lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2140_; 
lean_inc_ref(v_cs_2118_);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_x_2115_);
if (v_isSharedCheck_2140_ == 0)
{
lean_object* v_unused_2141_; 
v_unused_2141_ = lean_ctor_get(v_x_2115_, 0);
lean_dec(v_unused_2141_);
v___x_2124_ = v_x_2115_;
v_isShared_2125_ = v_isSharedCheck_2140_;
goto v_resetjp_2123_;
}
else
{
lean_dec(v_x_2115_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2140_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
size_t v___x_2126_; size_t v___x_2127_; size_t v___x_2128_; size_t v_i_2129_; size_t v___x_2130_; size_t v_shift_2131_; lean_object* v_v_2132_; lean_object* v___x_2133_; lean_object* v_xs_x27_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2126_ = ((size_t)1ULL);
v___x_2127_ = lean_usize_shift_left(v___x_2126_, v_x_2117_);
v___x_2128_ = lean_usize_sub(v___x_2127_, v___x_2126_);
v_i_2129_ = lean_usize_land(v_x_2116_, v___x_2128_);
v___x_2130_ = ((size_t)5ULL);
v_shift_2131_ = lean_usize_sub(v_x_2117_, v___x_2130_);
v_v_2132_ = lean_array_fget(v_cs_2118_, v___x_2120_);
v___x_2133_ = lean_box(0);
v_xs_x27_2134_ = lean_array_fset(v_cs_2118_, v___x_2120_, v___x_2133_);
v___x_2135_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___redArg(v_y_2114_, v_v_2132_, v_i_2129_, v_shift_2131_);
v___x_2136_ = lean_array_fset(v_xs_x27_2134_, v___x_2120_, v___x_2135_);
lean_dec(v___x_2120_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2136_);
v___x_2138_ = v___x_2124_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
else
{
lean_object* v_vs_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v_vs_2142_ = lean_ctor_get(v_x_2115_, 0);
v___x_2143_ = lean_usize_to_nat(v_x_2116_);
v___x_2144_ = lean_array_get_size(v_vs_2142_);
v___x_2145_ = lean_nat_dec_lt(v___x_2143_, v___x_2144_);
if (v___x_2145_ == 0)
{
lean_dec(v___x_2143_);
lean_dec(v_y_2114_);
return v_x_2115_;
}
else
{
lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2160_; 
lean_inc_ref(v_vs_2142_);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_x_2115_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; 
v_unused_2161_ = lean_ctor_get(v_x_2115_, 0);
lean_dec(v_unused_2161_);
v___x_2147_ = v_x_2115_;
v_isShared_2148_ = v_isSharedCheck_2160_;
goto v_resetjp_2146_;
}
else
{
lean_dec(v_x_2115_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2160_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v_v_2149_; lean_object* v___x_2150_; lean_object* v_xs_x27_2151_; lean_object* v___y_2153_; uint8_t v___x_2158_; 
v_v_2149_ = lean_array_fget(v_vs_2142_, v___x_2143_);
v___x_2150_ = lean_box(0);
v_xs_x27_2151_ = lean_array_fset(v_vs_2142_, v___x_2143_, v___x_2150_);
v___x_2158_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2114_, v_v_2149_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2114_, v___x_2150_, v_v_2149_);
v___y_2153_ = v___x_2159_;
goto v___jp_2152_;
}
else
{
lean_dec(v_y_2114_);
v___y_2153_ = v_v_2149_;
goto v___jp_2152_;
}
v___jp_2152_:
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2154_ = lean_array_fset(v_xs_x27_2151_, v___x_2143_, v___y_2153_);
lean_dec(v___x_2143_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v___x_2154_);
v___x_2156_ = v___x_2147_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___redArg___boxed(lean_object* v_y_2162_, lean_object* v_x_2163_, lean_object* v_x_2164_, lean_object* v_x_2165_){
_start:
{
size_t v_x_4526__boxed_2166_; size_t v_x_4527__boxed_2167_; lean_object* v_res_2168_; 
v_x_4526__boxed_2166_ = lean_unbox_usize(v_x_2164_);
lean_dec(v_x_2164_);
v_x_4527__boxed_2167_ = lean_unbox_usize(v_x_2165_);
lean_dec(v_x_2165_);
v_res_2168_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___redArg(v_y_2162_, v_x_2163_, v_x_4526__boxed_2166_, v_x_4527__boxed_2167_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(lean_object* v_y_2169_, lean_object* v_inst_2170_, lean_object* v_t_2171_, lean_object* v_i_2172_){
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
v___x_2183_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___redArg(v_y_2169_, v_root_2173_, v___x_2182_, v_shift_2176_);
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
lean_dec(v_y_2169_);
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
v___x_2202_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2169_, v_v_2193_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2169_, v___x_2194_, v_v_2193_);
v___y_2197_ = v___x_2203_;
goto v___jp_2196_;
}
else
{
lean_dec(v_y_2169_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2___boxed(lean_object* v_y_2205_, lean_object* v_inst_2206_, lean_object* v_t_2207_, lean_object* v_i_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2205_, v_inst_2206_, v_t_2207_, v_i_2208_);
lean_dec(v_i_2208_);
lean_dec(v_inst_2206_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(lean_object* v_y_2210_, lean_object* v_x_2211_, lean_object* v_s_2212_){
_start:
{
lean_object* v_vars_2213_; lean_object* v_varMap_2214_; lean_object* v_vars_x27_2215_; lean_object* v_varMap_x27_2216_; lean_object* v_natToIntMap_2217_; lean_object* v_natDef_2218_; lean_object* v_dvds_2219_; lean_object* v_lowers_2220_; lean_object* v_uppers_2221_; lean_object* v_diseqs_2222_; lean_object* v_elimEqs_2223_; lean_object* v_elimStack_2224_; lean_object* v_occurs_2225_; lean_object* v_assignment_2226_; lean_object* v_nextCnstrId_2227_; uint8_t v_caseSplits_2228_; lean_object* v_conflict_x3f_2229_; lean_object* v_diseqSplits_2230_; lean_object* v_divMod_2231_; lean_object* v_toIntIds_2232_; lean_object* v_toIntInfos_2233_; lean_object* v_toIntTermMap_2234_; lean_object* v_toIntVarMap_2235_; uint8_t v_usedCommRing_2236_; lean_object* v_nonlinearOccs_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2246_; 
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
v_caseSplits_2228_ = lean_ctor_get_uint8(v_s_2212_, sizeof(void*)*23);
v_conflict_x3f_2229_ = lean_ctor_get(v_s_2212_, 15);
v_diseqSplits_2230_ = lean_ctor_get(v_s_2212_, 16);
v_divMod_2231_ = lean_ctor_get(v_s_2212_, 17);
v_toIntIds_2232_ = lean_ctor_get(v_s_2212_, 18);
v_toIntInfos_2233_ = lean_ctor_get(v_s_2212_, 19);
v_toIntTermMap_2234_ = lean_ctor_get(v_s_2212_, 20);
v_toIntVarMap_2235_ = lean_ctor_get(v_s_2212_, 21);
v_usedCommRing_2236_ = lean_ctor_get_uint8(v_s_2212_, sizeof(void*)*23 + 1);
v_nonlinearOccs_2237_ = lean_ctor_get(v_s_2212_, 22);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_s_2212_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2239_ = v_s_2212_;
v_isShared_2240_ = v_isSharedCheck_2246_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_nonlinearOccs_2237_);
lean_inc(v_toIntVarMap_2235_);
lean_inc(v_toIntTermMap_2234_);
lean_inc(v_toIntInfos_2233_);
lean_inc(v_toIntIds_2232_);
lean_inc(v_divMod_2231_);
lean_inc(v_diseqSplits_2230_);
lean_inc(v_conflict_x3f_2229_);
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
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2246_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2244_; 
v___x_2241_ = lean_box(1);
v___x_2242_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2210_, v___x_2241_, v_occurs_2225_, v_x_2211_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 12, v___x_2242_);
v___x_2244_ = v___x_2239_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 23, 2);
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
lean_ctor_set(v_reuseFailAlloc_2245_, 15, v_conflict_x3f_2229_);
lean_ctor_set(v_reuseFailAlloc_2245_, 16, v_diseqSplits_2230_);
lean_ctor_set(v_reuseFailAlloc_2245_, 17, v_divMod_2231_);
lean_ctor_set(v_reuseFailAlloc_2245_, 18, v_toIntIds_2232_);
lean_ctor_set(v_reuseFailAlloc_2245_, 19, v_toIntInfos_2233_);
lean_ctor_set(v_reuseFailAlloc_2245_, 20, v_toIntTermMap_2234_);
lean_ctor_set(v_reuseFailAlloc_2245_, 21, v_toIntVarMap_2235_);
lean_ctor_set(v_reuseFailAlloc_2245_, 22, v_nonlinearOccs_2237_);
lean_ctor_set_uint8(v_reuseFailAlloc_2245_, sizeof(void*)*23, v_caseSplits_2228_);
lean_ctor_set_uint8(v_reuseFailAlloc_2245_, sizeof(void*)*23 + 1, v_usedCommRing_2236_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(lean_object* v_y_2327_, lean_object* v_inst_2328_, lean_object* v_x_2329_, size_t v_x_2330_, size_t v_x_2331_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___redArg(v_y_2327_, v_x_2329_, v_x_2330_, v_x_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2333_, lean_object* v_inst_2334_, lean_object* v_x_2335_, lean_object* v_x_2336_, lean_object* v_x_2337_){
_start:
{
size_t v_x_4737__boxed_2338_; size_t v_x_4738__boxed_2339_; lean_object* v_res_2340_; 
v_x_4737__boxed_2338_ = lean_unbox_usize(v_x_2336_);
lean_dec(v_x_2336_);
v_x_4738__boxed_2339_ = lean_unbox_usize(v_x_2337_);
lean_dec(v_x_2337_);
v_res_2340_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2333_, v_inst_2334_, v_x_2335_, v_x_4737__boxed_2338_, v_x_4738__boxed_2339_);
lean_dec(v_inst_2334_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(lean_object* v_y_2341_, lean_object* v_p_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
if (lean_obj_tag(v_p_2342_) == 1)
{
lean_object* v_v_2346_; lean_object* v_p_2347_; lean_object* v___x_2348_; 
v_v_2346_ = lean_ctor_get(v_p_2342_, 1);
lean_inc(v_v_2346_);
v_p_2347_ = lean_ctor_get(v_p_2342_, 2);
lean_inc_ref(v_p_2347_);
lean_dec_ref(v_p_2342_);
lean_inc(v_y_2341_);
v___x_2348_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_v_2346_, v_y_2341_, v_a_2343_, v_a_2344_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_dec_ref(v___x_2348_);
v_p_2342_ = v_p_2347_;
goto _start;
}
else
{
lean_dec_ref(v_p_2347_);
lean_dec(v_y_2341_);
return v___x_2348_;
}
}
else
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
lean_dec_ref(v_p_2342_);
lean_dec(v_y_2341_);
v___x_2350_ = lean_box(0);
v___x_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
return v___x_2351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg___boxed(lean_object* v_y_2352_, lean_object* v_p_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(v_y_2352_, v_p_2353_, v_a_2354_, v_a_2355_);
lean_dec_ref(v_a_2355_);
lean_dec(v_a_2354_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go(lean_object* v_y_2358_, lean_object* v_p_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(v_y_2358_, v_p_2359_, v_a_2360_, v_a_2368_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___boxed(lean_object* v_y_2372_, lean_object* v_p_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go(v_y_2372_, v_p_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
lean_dec(v_a_2375_);
lean_dec(v_a_2374_);
return v_res_2385_;
}
}
static lean_object* _init_l_Int_Linear_Poly_updateOccs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = ((lean_object*)(l_Int_Linear_Poly_updateOccs___redArg___closed__0));
v___x_2388_ = l_Lean_stringToMessageData(v___x_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_updateOccs___redArg(lean_object* v_p_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
if (lean_obj_tag(v_p_2389_) == 1)
{
lean_object* v_v_2396_; lean_object* v_p_2397_; lean_object* v___x_2398_; 
v_v_2396_ = lean_ctor_get(v_p_2389_, 1);
lean_inc(v_v_2396_);
v_p_2397_ = lean_ctor_get(v_p_2389_, 2);
lean_inc_ref(v_p_2397_);
lean_dec_ref(v_p_2389_);
v___x_2398_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(v_v_2396_, v_p_2397_, v_a_2390_, v_a_2393_);
return v___x_2398_;
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
lean_dec_ref(v_p_2389_);
v___x_2399_ = lean_obj_once(&l_Int_Linear_Poly_updateOccs___redArg___closed__1, &l_Int_Linear_Poly_updateOccs___redArg___closed__1_once, _init_l_Int_Linear_Poly_updateOccs___redArg___closed__1);
v___x_2400_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2399_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
return v___x_2400_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_updateOccs___redArg___boxed(lean_object* v_p_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Int_Linear_Poly_updateOccs___redArg(v_p_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_updateOccs(lean_object* v_p_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Int_Linear_Poly_updateOccs___redArg(v_p_2409_, v_a_2410_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_updateOccs___boxed(lean_object* v_p_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Int_Linear_Poly_updateOccs(v_p_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
lean_dec(v_a_2428_);
lean_dec_ref(v_a_2427_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
lean_dec(v_a_2424_);
lean_dec(v_a_2423_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go_spec__0(lean_object* v_a_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Rat_ofInt(v_a_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go(lean_object* v_a_2437_, lean_object* v_v_2438_, lean_object* v_a_2439_){
_start:
{
if (lean_obj_tag(v_a_2439_) == 0)
{
lean_object* v_k_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2449_; 
lean_dec_ref(v_a_2437_);
v_k_2440_ = lean_ctor_get(v_a_2439_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_a_2439_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2442_ = v_a_2439_;
v_isShared_2443_ = v_isSharedCheck_2449_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_k_2440_);
lean_dec(v_a_2439_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2449_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2447_; 
v___x_2444_ = l_Rat_ofInt(v_k_2440_);
v___x_2445_ = l_Rat_add(v_v_2438_, v___x_2444_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set_tag(v___x_2442_, 1);
lean_ctor_set(v___x_2442_, 0, v___x_2445_);
v___x_2447_ = v___x_2442_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
else
{
lean_object* v_k_2450_; lean_object* v_v_2451_; lean_object* v_p_2452_; lean_object* v_size_2453_; uint8_t v___x_2454_; 
v_k_2450_ = lean_ctor_get(v_a_2439_, 0);
lean_inc(v_k_2450_);
v_v_2451_ = lean_ctor_get(v_a_2439_, 1);
lean_inc(v_v_2451_);
v_p_2452_ = lean_ctor_get(v_a_2439_, 2);
lean_inc_ref(v_p_2452_);
lean_dec_ref(v_a_2439_);
v_size_2453_ = lean_ctor_get(v_a_2437_, 2);
v___x_2454_ = lean_nat_dec_lt(v_v_2451_, v_size_2453_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; 
lean_dec_ref(v_p_2452_);
lean_dec(v_v_2451_);
lean_dec(v_k_2450_);
lean_dec_ref(v_v_2438_);
lean_dec_ref(v_a_2437_);
v___x_2455_ = lean_box(0);
return v___x_2455_;
}
else
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2456_ = l_Rat_ofInt(v_k_2450_);
v___x_2457_ = l_instInhabitedRat;
lean_inc_ref(v_a_2437_);
v___x_2458_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2457_, v_a_2437_, v_v_2451_);
lean_dec(v_v_2451_);
v___x_2459_ = l_Rat_mul(v___x_2456_, v___x_2458_);
lean_dec_ref(v___x_2456_);
v___x_2460_ = l_Rat_add(v_v_2438_, v___x_2459_);
v_v_2438_ = v___x_2460_;
v_a_2439_ = v_p_2452_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_Linear_Poly_eval_x3f_spec__0(lean_object* v_a_2462_){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = lean_nat_to_int(v_a_2462_);
v___x_2464_ = l_Rat_ofInt(v___x_2463_);
return v___x_2464_;
}
}
static lean_object* _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = lean_unsigned_to_nat(0u);
v___x_2466_ = l_Nat_cast___at___00Int_Linear_Poly_eval_x3f_spec__0(v___x_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_eval_x3f___redArg(lean_object* v_p_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2468_, v_a_2469_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2482_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2474_ = v___x_2471_;
v_isShared_2475_ = v_isSharedCheck_2482_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2482_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v_assignment_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2480_; 
v_assignment_2476_ = lean_ctor_get(v_a_2472_, 13);
lean_inc_ref(v_assignment_2476_);
lean_dec(v_a_2472_);
v___x_2477_ = lean_obj_once(&l_Int_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2478_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go(v_assignment_2476_, v___x_2477_, v_p_2467_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v___x_2478_);
v___x_2480_ = v___x_2474_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2478_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec_ref(v_p_2467_);
v_a_2483_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2471_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2471_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_eval_x3f___redArg___boxed(lean_object* v_p_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2491_, v_a_2492_, v_a_2493_);
lean_dec_ref(v_a_2493_);
lean_dec(v_a_2492_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_eval_x3f(lean_object* v_p_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2496_, v_a_2497_, v_a_2505_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_eval_x3f___boxed(lean_object* v_p_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Int_Linear_Poly_eval_x3f(v_p_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
lean_dec(v_a_2511_);
lean_dec(v_a_2510_);
return v_res_2521_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(lean_object* v_c_2522_){
_start:
{
lean_object* v_p_2523_; uint8_t v___x_2524_; 
v_p_2523_ = lean_ctor_get(v_c_2522_, 0);
v___x_2524_ = l_Int_Linear_Poly_isUnsatLe(v_p_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat___boxed(lean_object* v_c_2525_){
_start:
{
uint8_t v_res_2526_; lean_object* v_r_2527_; 
v_res_2526_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(v_c_2525_);
lean_dec_ref(v_c_2525_);
v_r_2527_ = lean_box(v_res_2526_);
return v_r_2527_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(lean_object* v_c_2528_){
_start:
{
lean_object* v_d_2529_; lean_object* v_p_2530_; uint8_t v___x_2531_; 
v_d_2529_ = lean_ctor_get(v_c_2528_, 0);
lean_inc(v_d_2529_);
v_p_2530_ = lean_ctor_get(v_c_2528_, 1);
lean_inc_ref(v_p_2530_);
lean_dec_ref(v_c_2528_);
v___x_2531_ = l_Int_Linear_Poly_isUnsatDvd(v_d_2529_, v_p_2530_);
lean_dec_ref(v_p_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat___boxed(lean_object* v_c_2532_){
_start:
{
uint8_t v_res_2533_; lean_object* v_r_2534_; 
v_res_2533_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(v_c_2532_);
v_r_2534_ = lean_box(v_res_2533_);
return v_r_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object* v_c_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v_d_2539_; lean_object* v_p_2540_; lean_object* v___x_2541_; 
v_d_2539_ = lean_ctor_get(v_c_2535_, 0);
lean_inc(v_d_2539_);
v_p_2540_ = lean_ctor_get(v_c_2535_, 1);
lean_inc_ref(v_p_2540_);
lean_dec_ref(v_c_2535_);
v___x_2541_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2540_, v_a_2536_, v_a_2537_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2567_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2544_ = v___x_2541_;
v_isShared_2545_ = v_isSharedCheck_2567_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2567_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
if (lean_obj_tag(v_a_2542_) == 1)
{
lean_object* v_val_2546_; lean_object* v_num_2547_; lean_object* v_den_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; 
v_val_2546_ = lean_ctor_get(v_a_2542_, 0);
lean_inc(v_val_2546_);
lean_dec_ref(v_a_2542_);
v_num_2547_ = lean_ctor_get(v_val_2546_, 0);
lean_inc(v_num_2547_);
v_den_2548_ = lean_ctor_get(v_val_2546_, 1);
lean_inc(v_den_2548_);
lean_dec(v_val_2546_);
v___x_2549_ = lean_unsigned_to_nat(1u);
v___x_2550_ = lean_nat_dec_eq(v_den_2548_, v___x_2549_);
lean_dec(v_den_2548_);
if (v___x_2550_ == 0)
{
uint8_t v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2554_; 
lean_dec(v_num_2547_);
lean_dec(v_d_2539_);
v___x_2551_ = 0;
v___x_2552_ = lean_box(v___x_2551_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v___x_2552_);
v___x_2554_ = v___x_2544_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2552_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
else
{
uint8_t v___x_2556_; uint8_t v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2560_; 
v___x_2556_ = l_Int_decidableDvd(v_d_2539_, v_num_2547_);
lean_dec(v_num_2547_);
lean_dec(v_d_2539_);
v___x_2557_ = l_Bool_toLBool(v___x_2556_);
v___x_2558_ = lean_box(v___x_2557_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v___x_2558_);
v___x_2560_ = v___x_2544_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
else
{
uint8_t v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2565_; 
lean_dec(v_a_2542_);
lean_dec(v_d_2539_);
v___x_2562_ = 2;
v___x_2563_ = lean_box(v___x_2562_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v___x_2563_);
v___x_2565_ = v___x_2544_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2563_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec(v_d_2539_);
v_a_2568_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2541_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2541_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg___boxed(lean_object* v_c_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2576_, v_a_2577_, v_a_2578_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(lean_object* v_c_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2581_, v_a_2582_, v_a_2590_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___boxed(lean_object* v_c_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(v_c_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_);
lean_dec(v_a_2604_);
lean_dec_ref(v_a_2603_);
lean_dec(v_a_2602_);
lean_dec_ref(v_a_2601_);
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_a_2596_);
lean_dec(v_a_2595_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_satisfiedLe___redArg(lean_object* v_p_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2607_, v_a_2608_, v_a_2609_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2629_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2629_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2629_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
if (lean_obj_tag(v_a_2612_) == 1)
{
lean_object* v_val_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; uint8_t v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2622_; 
v_val_2616_ = lean_ctor_get(v_a_2612_, 0);
lean_inc(v_val_2616_);
lean_dec_ref(v_a_2612_);
v___x_2617_ = lean_obj_once(&l_Int_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2618_ = l_Rat_instDecidableLe(v_val_2616_, v___x_2617_);
v___x_2619_ = l_Bool_toLBool(v___x_2618_);
v___x_2620_ = lean_box(v___x_2619_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v___x_2620_);
v___x_2622_ = v___x_2614_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
else
{
uint8_t v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2627_; 
lean_dec(v_a_2612_);
v___x_2624_ = 2;
v___x_2625_ = lean_box(v___x_2624_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v___x_2625_);
v___x_2627_ = v___x_2614_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
v_a_2630_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2611_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2611_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_satisfiedLe___redArg___boxed(lean_object* v_p_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Int_Linear_Poly_satisfiedLe___redArg(v_p_2638_, v_a_2639_, v_a_2640_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_satisfiedLe(lean_object* v_p_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Int_Linear_Poly_satisfiedLe___redArg(v_p_2643_, v_a_2644_, v_a_2652_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_satisfiedLe___boxed(lean_object* v_p_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Int_Linear_Poly_satisfiedLe(v_p_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec(v_a_2657_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(lean_object* v_c_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v_p_2673_; lean_object* v___x_2674_; 
v_p_2673_ = lean_ctor_get(v_c_2669_, 0);
lean_inc_ref(v_p_2673_);
lean_dec_ref(v_c_2669_);
v___x_2674_ = l_Int_Linear_Poly_satisfiedLe___redArg(v_p_2673_, v_a_2670_, v_a_2671_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg___boxed(lean_object* v_c_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2675_, v_a_2676_, v_a_2677_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(lean_object* v_c_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2680_, v_a_2681_, v_a_2689_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___boxed(lean_object* v_c_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(v_c_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
lean_dec(v_a_2703_);
lean_dec_ref(v_a_2702_);
lean_dec(v_a_2701_);
lean_dec_ref(v_a_2700_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_a_2695_);
lean_dec(v_a_2694_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(lean_object* v_c_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v_p_2710_; lean_object* v___x_2711_; 
v_p_2710_ = lean_ctor_get(v_c_2706_, 0);
lean_inc_ref(v_p_2710_);
lean_dec_ref(v_c_2706_);
v___x_2711_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2710_, v_a_2707_, v_a_2708_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2731_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2714_ = v___x_2711_;
v_isShared_2715_ = v_isSharedCheck_2731_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2711_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2731_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
uint8_t v___y_2717_; 
if (lean_obj_tag(v_a_2712_) == 1)
{
lean_object* v_val_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v_val_2723_ = lean_ctor_get(v_a_2712_, 0);
lean_inc(v_val_2723_);
lean_dec_ref(v_a_2712_);
v___x_2724_ = lean_obj_once(&l_Int_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2725_ = l_instDecidableEqRat_decEq(v_val_2723_, v___x_2724_);
lean_dec(v_val_2723_);
if (v___x_2725_ == 0)
{
uint8_t v___x_2726_; 
v___x_2726_ = 1;
v___y_2717_ = v___x_2726_;
goto v___jp_2716_;
}
else
{
uint8_t v___x_2727_; 
v___x_2727_ = 0;
v___y_2717_ = v___x_2727_;
goto v___jp_2716_;
}
}
else
{
uint8_t v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_del_object(v___x_2714_);
lean_dec(v_a_2712_);
v___x_2728_ = 2;
v___x_2729_ = lean_box(v___x_2728_);
v___x_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2729_);
return v___x_2730_;
}
v___jp_2716_:
{
uint8_t v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2721_; 
v___x_2718_ = l_Bool_toLBool(v___y_2717_);
v___x_2719_ = lean_box(v___x_2718_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v___x_2719_);
v___x_2721_ = v___x_2714_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
v_a_2732_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2711_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2711_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg___boxed(lean_object* v_c_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_2740_, v_a_2741_, v_a_2742_);
lean_dec_ref(v_a_2742_);
lean_dec(v_a_2741_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(lean_object* v_c_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_2745_, v_a_2746_, v_a_2754_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___boxed(lean_object* v_c_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(v_c_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
lean_dec(v_a_2760_);
lean_dec(v_a_2759_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(lean_object* v_c_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_){
_start:
{
lean_object* v_p_2775_; lean_object* v___x_2776_; 
v_p_2775_ = lean_ctor_get(v_c_2771_, 0);
lean_inc_ref(v_p_2775_);
lean_dec_ref(v_c_2771_);
v___x_2776_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2775_, v_a_2772_, v_a_2773_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2794_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2794_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2794_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
if (lean_obj_tag(v_a_2777_) == 1)
{
lean_object* v_val_2781_; lean_object* v___x_2782_; uint8_t v___x_2783_; uint8_t v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v_val_2781_ = lean_ctor_get(v_a_2777_, 0);
lean_inc(v_val_2781_);
lean_dec_ref(v_a_2777_);
v___x_2782_ = lean_obj_once(&l_Int_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2783_ = l_instDecidableEqRat_decEq(v_val_2781_, v___x_2782_);
lean_dec(v_val_2781_);
v___x_2784_ = l_Bool_toLBool(v___x_2783_);
v___x_2785_ = lean_box(v___x_2784_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v___x_2785_);
v___x_2787_ = v___x_2779_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
else
{
uint8_t v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2792_; 
lean_dec(v_a_2777_);
v___x_2789_ = 2;
v___x_2790_ = lean_box(v___x_2789_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v___x_2790_);
v___x_2792_ = v___x_2779_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2790_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
v_a_2795_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2776_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2776_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg___boxed(lean_object* v_c_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_2803_, v_a_2804_, v_a_2805_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(lean_object* v_c_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_2808_, v_a_2809_, v_a_2817_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___boxed(lean_object* v_c_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(v_c_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
lean_dec_ref(v_a_2828_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
lean_dec(v_a_2825_);
lean_dec_ref(v_a_2824_);
lean_dec(v_a_2823_);
lean_dec(v_a_2822_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_findVarToSubst___redArg(lean_object* v_p_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
if (lean_obj_tag(v_p_2834_) == 0)
{
lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2845_; 
v_isSharedCheck_2845_ = !lean_is_exclusive(v_p_2834_);
if (v_isSharedCheck_2845_ == 0)
{
lean_object* v_unused_2846_; 
v_unused_2846_ = lean_ctor_get(v_p_2834_, 0);
lean_dec(v_unused_2846_);
v___x_2839_ = v_p_2834_;
v_isShared_2840_ = v_isSharedCheck_2845_;
goto v_resetjp_2838_;
}
else
{
lean_dec(v_p_2834_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2845_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2841_; lean_object* v___x_2843_; 
v___x_2841_ = lean_box(0);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v___x_2841_);
v___x_2843_ = v___x_2839_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
else
{
lean_object* v_k_2847_; lean_object* v_v_2848_; lean_object* v_p_2849_; lean_object* v___x_2850_; 
v_k_2847_ = lean_ctor_get(v_p_2834_, 0);
lean_inc(v_k_2847_);
v_v_2848_ = lean_ctor_get(v_p_2834_, 1);
lean_inc(v_v_2848_);
v_p_2849_ = lean_ctor_get(v_p_2834_, 2);
lean_inc_ref(v_p_2849_);
lean_dec_ref(v_p_2834_);
v___x_2850_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2835_, v_a_2836_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2877_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2853_ = v___x_2850_;
v_isShared_2854_ = v_isSharedCheck_2877_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2850_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2877_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___y_2856_; lean_object* v_elimEqs_2871_; lean_object* v_size_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; 
v_elimEqs_2871_ = lean_ctor_get(v_a_2851_, 10);
lean_inc_ref(v_elimEqs_2871_);
lean_dec(v_a_2851_);
v_size_2872_ = lean_ctor_get(v_elimEqs_2871_, 2);
v___x_2873_ = lean_box(0);
v___x_2874_ = lean_nat_dec_lt(v_v_2848_, v_size_2872_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; 
lean_dec_ref(v_elimEqs_2871_);
v___x_2875_ = l_outOfBounds___redArg(v___x_2873_);
v___y_2856_ = v___x_2875_;
goto v___jp_2855_;
}
else
{
lean_object* v___x_2876_; 
v___x_2876_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2873_, v_elimEqs_2871_, v_v_2848_);
v___y_2856_ = v___x_2876_;
goto v___jp_2855_;
}
v___jp_2855_:
{
if (lean_obj_tag(v___y_2856_) == 1)
{
lean_object* v_val_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2869_; 
lean_dec_ref(v_p_2849_);
v_val_2857_ = lean_ctor_get(v___y_2856_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___y_2856_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2859_ = v___y_2856_;
v_isShared_2860_ = v_isSharedCheck_2869_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_val_2857_);
lean_dec(v___y_2856_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2869_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2864_; 
v___x_2861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2861_, 0, v_v_2848_);
lean_ctor_set(v___x_2861_, 1, v_val_2857_);
v___x_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2862_, 0, v_k_2847_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2862_);
v___x_2864_ = v___x_2859_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2866_; 
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v___x_2864_);
v___x_2866_ = v___x_2853_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
else
{
lean_dec(v___y_2856_);
lean_del_object(v___x_2853_);
lean_dec(v_v_2848_);
lean_dec(v_k_2847_);
v_p_2834_ = v_p_2849_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
lean_dec_ref(v_p_2849_);
lean_dec(v_v_2848_);
lean_dec(v_k_2847_);
v_a_2878_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2850_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2850_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
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
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_findVarToSubst___redArg___boxed(lean_object* v_p_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_2886_, v_a_2887_, v_a_2888_);
lean_dec_ref(v_a_2888_);
lean_dec(v_a_2887_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_findVarToSubst(lean_object* v_p_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v___x_2903_; 
v___x_2903_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_2891_, v_a_2892_, v_a_2900_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_findVarToSubst___boxed(lean_object* v_p_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Int_Linear_Poly_findVarToSubst(v_p_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
lean_dec(v_a_2908_);
lean_dec_ref(v_a_2907_);
lean_dec(v_a_2906_);
lean_dec(v_a_2905_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(lean_object* v_pred_2917_){
_start:
{
lean_object* v_c_u2081_2918_; lean_object* v_c_u2082_2919_; uint8_t v_left_2920_; lean_object* v_c_u2083_x3f_2921_; lean_object* v_p_2922_; lean_object* v_p_2923_; lean_object* v_a_2924_; lean_object* v_b_2925_; 
v_c_u2081_2918_ = lean_ctor_get(v_pred_2917_, 0);
v_c_u2082_2919_ = lean_ctor_get(v_pred_2917_, 1);
v_left_2920_ = lean_ctor_get_uint8(v_pred_2917_, sizeof(void*)*3);
v_c_u2083_x3f_2921_ = lean_ctor_get(v_pred_2917_, 2);
v_p_2922_ = lean_ctor_get(v_c_u2081_2918_, 0);
v_p_2923_ = lean_ctor_get(v_c_u2082_2919_, 0);
v_a_2924_ = l_Int_Linear_Poly_leadCoeff(v_p_2922_);
v_b_2925_ = l_Int_Linear_Poly_leadCoeff(v_p_2923_);
if (lean_obj_tag(v_c_u2083_x3f_2921_) == 0)
{
if (v_left_2920_ == 0)
{
lean_object* v___x_2926_; 
lean_dec(v_a_2924_);
v___x_2926_ = lean_nat_abs(v_b_2925_);
lean_dec(v_b_2925_);
return v___x_2926_;
}
else
{
lean_object* v___x_2927_; 
lean_dec(v_b_2925_);
v___x_2927_ = lean_nat_abs(v_a_2924_);
lean_dec(v_a_2924_);
return v___x_2927_;
}
}
else
{
lean_object* v_val_2928_; lean_object* v_d_2929_; lean_object* v_p_2930_; lean_object* v_c_2931_; 
v_val_2928_ = lean_ctor_get(v_c_u2083_x3f_2921_, 0);
v_d_2929_ = lean_ctor_get(v_val_2928_, 0);
v_p_2930_ = lean_ctor_get(v_val_2928_, 1);
v_c_2931_ = l_Int_Linear_Poly_leadCoeff(v_p_2930_);
if (v_left_2920_ == 0)
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
lean_dec(v_a_2924_);
v___x_2932_ = lean_int_mul(v_b_2925_, v_d_2929_);
v___x_2933_ = l_Int_gcd(v___x_2932_, v_c_2931_);
lean_dec(v_c_2931_);
v___x_2934_ = lean_nat_to_int(v___x_2933_);
v___x_2935_ = lean_int_ediv(v___x_2932_, v___x_2934_);
lean_dec(v___x_2934_);
lean_dec(v___x_2932_);
v___x_2936_ = l_Int_lcm(v_b_2925_, v___x_2935_);
lean_dec(v___x_2935_);
lean_dec(v_b_2925_);
return v___x_2936_;
}
else
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
lean_dec(v_b_2925_);
v___x_2937_ = lean_int_mul(v_a_2924_, v_d_2929_);
v___x_2938_ = l_Int_gcd(v___x_2937_, v_c_2931_);
lean_dec(v_c_2931_);
v___x_2939_ = lean_nat_to_int(v___x_2938_);
v___x_2940_ = lean_int_ediv(v___x_2937_, v___x_2939_);
lean_dec(v___x_2939_);
lean_dec(v___x_2937_);
v___x_2941_ = l_Int_lcm(v_a_2924_, v___x_2940_);
lean_dec(v___x_2940_);
lean_dec(v_a_2924_);
return v___x_2941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases___boxed(lean_object* v_pred_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(v_pred_2942_);
lean_dec_ref(v_pred_2942_);
return v_res_2943_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0));
v___x_2946_ = l_Lean_stringToMessageData(v___x_2945_);
return v___x_2946_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4(void){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3));
v___x_2951_ = l_Lean_MessageData_ofFormat(v___x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(lean_object* v_pred_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
lean_object* v_c_u2081_2956_; lean_object* v_c_u2082_2957_; lean_object* v_c_u2083_x3f_2958_; lean_object* v___x_2959_; 
v_c_u2081_2956_ = lean_ctor_get(v_pred_2952_, 0);
lean_inc_ref(v_c_u2081_2956_);
v_c_u2082_2957_ = lean_ctor_get(v_pred_2952_, 1);
lean_inc_ref(v_c_u2082_2957_);
v_c_u2083_x3f_2958_ = lean_ctor_get(v_pred_2952_, 2);
lean_inc(v_c_u2083_x3f_2958_);
lean_dec_ref(v_pred_2952_);
v___x_2959_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_2956_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2961_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref(v___x_2959_);
v___x_2961_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_2957_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2980_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2964_ = v___x_2961_;
v_isShared_2965_ = v_isSharedCheck_2980_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2961_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2980_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v_a_2967_; 
if (lean_obj_tag(v_c_u2083_x3f_2958_) == 1)
{
lean_object* v_val_2976_; lean_object* v___x_2977_; 
v_val_2976_ = lean_ctor_get(v_c_u2083_x3f_2958_, 0);
lean_inc(v_val_2976_);
lean_dec_ref(v_c_u2083_x3f_2958_);
v___x_2977_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_val_2976_, v_a_2953_, v_a_2954_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref(v___x_2977_);
v_a_2967_ = v_a_2978_;
goto v___jp_2966_;
}
else
{
lean_del_object(v___x_2964_);
lean_dec(v_a_2962_);
lean_dec(v_a_2960_);
return v___x_2977_;
}
}
else
{
lean_object* v___x_2979_; 
lean_dec(v_c_u2083_x3f_2958_);
v___x_2979_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4);
v_a_2967_ = v___x_2979_;
goto v___jp_2966_;
}
v___jp_2966_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
v___x_2968_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_2969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2969_, 0, v_a_2960_);
lean_ctor_set(v___x_2969_, 1, v___x_2968_);
v___x_2970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
lean_ctor_set(v___x_2970_, 1, v_a_2962_);
v___x_2971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2970_);
lean_ctor_set(v___x_2971_, 1, v___x_2968_);
v___x_2972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
lean_ctor_set(v___x_2972_, 1, v_a_2967_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 0, v___x_2972_);
v___x_2974_ = v___x_2964_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
else
{
lean_dec(v_a_2960_);
lean_dec(v_c_u2083_x3f_2958_);
return v___x_2961_;
}
}
else
{
lean_dec(v_c_u2083_x3f_2958_);
lean_dec_ref(v_c_u2082_2957_);
return v___x_2959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___boxed(lean_object* v_pred_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_2981_, v_a_2982_, v_a_2983_);
lean_dec_ref(v_a_2983_);
lean_dec(v_a_2982_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(lean_object* v_pred_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_2986_, v_a_2987_, v_a_2995_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___boxed(lean_object* v_pred_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(v_pred_2999_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_);
lean_dec(v_a_3009_);
lean_dec_ref(v_a_3008_);
lean_dec(v_a_3007_);
lean_dec_ref(v_a_3006_);
lean_dec(v_a_3005_);
lean_dec_ref(v_a_3004_);
lean_dec(v_a_3003_);
lean_dec_ref(v_a_3002_);
lean_dec(v_a_3001_);
lean_dec(v_a_3000_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(lean_object* v_h_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_){
_start:
{
switch(lean_obj_tag(v_h_3012_))
{
case 0:
{
lean_object* v_c_3016_; lean_object* v___x_3017_; 
v_c_3016_ = lean_ctor_get(v_h_3012_, 0);
lean_inc_ref(v_c_3016_);
lean_dec_ref(v_h_3012_);
v___x_3017_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_3016_, v_a_3013_, v_a_3014_);
return v___x_3017_;
}
case 1:
{
lean_object* v_c_3018_; lean_object* v___x_3019_; 
v_c_3018_ = lean_ctor_get(v_h_3012_, 0);
lean_inc_ref(v_c_3018_);
lean_dec_ref(v_h_3012_);
v___x_3019_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3018_, v_a_3013_, v_a_3014_);
return v___x_3019_;
}
case 2:
{
lean_object* v_c_3020_; lean_object* v___x_3021_; 
v_c_3020_ = lean_ctor_get(v_h_3012_, 0);
lean_inc_ref(v_c_3020_);
lean_dec_ref(v_h_3012_);
v___x_3021_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_3020_, v_a_3013_, v_a_3014_);
return v___x_3021_;
}
case 3:
{
lean_object* v_c_3022_; lean_object* v___x_3023_; 
v_c_3022_ = lean_ctor_get(v_h_3012_, 0);
lean_inc_ref(v_c_3022_);
lean_dec_ref(v_h_3012_);
v___x_3023_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_3022_, v_a_3013_, v_a_3014_);
return v___x_3023_;
}
default: 
{
lean_object* v_c_u2081_3024_; lean_object* v_c_u2082_3025_; lean_object* v_c_u2083_3026_; lean_object* v___x_3027_; 
v_c_u2081_3024_ = lean_ctor_get(v_h_3012_, 0);
lean_inc_ref(v_c_u2081_3024_);
v_c_u2082_3025_ = lean_ctor_get(v_h_3012_, 1);
lean_inc_ref(v_c_u2082_3025_);
v_c_u2083_3026_ = lean_ctor_get(v_h_3012_, 2);
lean_inc_ref(v_c_u2083_3026_);
lean_dec_ref(v_h_3012_);
v___x_3027_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3024_, v_a_3013_, v_a_3014_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3029_; 
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3028_);
lean_dec_ref(v___x_3027_);
v___x_3029_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3025_, v_a_3013_, v_a_3014_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3031_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref(v___x_3029_);
v___x_3031_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2083_3026_, v_a_3013_, v_a_3014_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3044_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3034_ = v___x_3031_;
v_isShared_3035_ = v_isSharedCheck_3044_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3031_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3044_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3042_; 
v___x_3036_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3037_, 0, v_a_3028_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
lean_ctor_set(v___x_3038_, 1, v_a_3030_);
v___x_3039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
lean_ctor_set(v___x_3039_, 1, v___x_3036_);
v___x_3040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v_a_3032_);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 0, v___x_3040_);
v___x_3042_ = v___x_3034_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v___x_3040_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
else
{
lean_dec(v_a_3030_);
lean_dec(v_a_3028_);
return v___x_3031_;
}
}
else
{
lean_dec(v_a_3028_);
lean_dec_ref(v_c_u2083_3026_);
return v___x_3029_;
}
}
else
{
lean_dec_ref(v_c_u2083_3026_);
lean_dec_ref(v_c_u2082_3025_);
return v___x_3027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg___boxed(lean_object* v_h_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3045_, v_a_3046_, v_a_3047_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(lean_object* v_h_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3050_, v_a_3051_, v_a_3059_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___boxed(lean_object* v_h_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(v_h_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
lean_dec(v_a_3073_);
lean_dec_ref(v_a_3072_);
lean_dec(v_a_3071_);
lean_dec_ref(v_a_3070_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec(v_a_3064_);
return v_res_3075_;
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
