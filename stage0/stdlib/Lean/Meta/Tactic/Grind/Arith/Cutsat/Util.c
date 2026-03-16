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
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
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
uint8_t l_Int_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatLe(lean_object*);
uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object*);
lean_object* l_Int_Linear_Poly_leadCoeff(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__5;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVar___boxed(lean_object* v_e_178_, lean_object* v_a_00___x40___internal___hyg_179_, lean_object* v_a_00___x40___internal___hyg_180_, lean_object* v_a_00___x40___internal___hyg_181_, lean_object* v_a_00___x40___internal___hyg_182_, lean_object* v_a_00___x40___internal___hyg_183_, lean_object* v_a_00___x40___internal___hyg_184_, lean_object* v_a_00___x40___internal___hyg_185_, lean_object* v_a_00___x40___internal___hyg_186_, lean_object* v_a_00___x40___internal___hyg_187_, lean_object* v_a_00___x40___internal___hyg_188_, lean_object* v_a_00___x40___internal___hyg_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = lean_grind_cutsat_mk_var(v_e_178_, v_a_00___x40___internal___hyg_179_, v_a_00___x40___internal___hyg_180_, v_a_00___x40___internal___hyg_181_, v_a_00___x40___internal___hyg_182_, v_a_00___x40___internal___hyg_183_, v_a_00___x40___internal___hyg_184_, v_a_00___x40___internal___hyg_185_, v_a_00___x40___internal___hyg_186_, v_a_00___x40___internal___hyg_187_, v_a_00___x40___internal___hyg_188_);
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
size_t v_x_946__boxed_344_; uint8_t v_res_345_; lean_object* v_r_346_; 
v_x_946__boxed_344_ = lean_unbox_usize(v_x_342_);
lean_dec(v_x_342_);
v_res_345_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_341_, v_x_946__boxed_344_, v_x_343_);
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
size_t v_x_1095__boxed_429_; uint8_t v_res_430_; lean_object* v_r_431_; 
v_x_1095__boxed_429_ = lean_unbox_usize(v_x_427_);
lean_dec(v_x_427_);
v_res_430_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(v_00_u03b2_425_, v_x_426_, v_x_1095__boxed_429_, v_x_428_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_assert___boxed(lean_object* v_c_562_, lean_object* v_a_00___x40___internal___hyg_563_, lean_object* v_a_00___x40___internal___hyg_564_, lean_object* v_a_00___x40___internal___hyg_565_, lean_object* v_a_00___x40___internal___hyg_566_, lean_object* v_a_00___x40___internal___hyg_567_, lean_object* v_a_00___x40___internal___hyg_568_, lean_object* v_a_00___x40___internal___hyg_569_, lean_object* v_a_00___x40___internal___hyg_570_, lean_object* v_a_00___x40___internal___hyg_571_, lean_object* v_a_00___x40___internal___hyg_572_, lean_object* v_a_00___x40___internal___hyg_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = lean_grind_cutsat_assert_eq(v_c_562_, v_a_00___x40___internal___hyg_563_, v_a_00___x40___internal___hyg_564_, v_a_00___x40___internal___hyg_565_, v_a_00___x40___internal___hyg_566_, v_a_00___x40___internal___hyg_567_, v_a_00___x40___internal___hyg_568_, v_a_00___x40___internal___hyg_569_, v_a_00___x40___internal___hyg_570_, v_a_00___x40___internal___hyg_571_, v_a_00___x40___internal___hyg_572_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_nat_to_int(v___x_653_);
return v___x_654_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__5(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4));
v___x_657_ = l_Lean_stringToMessageData(v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(lean_object* v_r_658_, lean_object* v_p_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
if (lean_obj_tag(v_p_659_) == 0)
{
lean_object* v_k_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_692_; 
v_k_663_ = lean_ctor_get(v_p_659_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v_p_659_);
if (v_isSharedCheck_692_ == 0)
{
v___x_665_ = v_p_659_;
v_isShared_666_ = v_isSharedCheck_692_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_k_663_);
lean_dec(v_p_659_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_692_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_667_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_668_ = lean_int_dec_eq(v_k_663_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___y_672_; uint8_t v_isNeg_679_; 
v___x_669_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1);
v___x_670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_670_, 0, v_r_658_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v_isNeg_679_ = lean_int_dec_lt(v_k_663_, v___x_667_);
if (v_isNeg_679_ == 0)
{
lean_object* v_a_680_; lean_object* v___x_681_; 
v_a_680_ = lean_nat_abs(v_k_663_);
lean_dec(v_k_663_);
v___x_681_ = l_Nat_reprFast(v_a_680_);
v___y_672_ = v___x_681_;
goto v___jp_671_;
}
else
{
lean_object* v_abs_682_; lean_object* v_one_683_; lean_object* v_a_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_abs_682_ = lean_nat_abs(v_k_663_);
lean_dec(v_k_663_);
v_one_683_ = lean_unsigned_to_nat(1u);
v_a_684_ = lean_nat_sub(v_abs_682_, v_one_683_);
lean_dec(v_abs_682_);
v___x_685_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2));
v___x_686_ = lean_nat_add(v_a_684_, v_one_683_);
lean_dec(v_a_684_);
v___x_687_ = l_Nat_reprFast(v___x_686_);
v___x_688_ = lean_string_append(v___x_685_, v___x_687_);
lean_dec_ref(v___x_687_);
v___y_672_ = v___x_688_;
goto v___jp_671_;
}
v___jp_671_:
{
lean_object* v___x_674_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set_tag(v___x_665_, 3);
lean_ctor_set(v___x_665_, 0, v___y_672_);
v___x_674_ = v___x_665_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___y_672_);
v___x_674_ = v_reuseFailAlloc_678_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = l_Lean_MessageData_ofFormat(v___x_674_);
v___x_676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_670_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
else
{
lean_object* v___x_690_; 
lean_dec(v_k_663_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v_r_658_);
v___x_690_ = v___x_665_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_r_658_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
else
{
lean_object* v_k_693_; lean_object* v_v_694_; lean_object* v_p_695_; lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v_k_693_ = lean_ctor_get(v_p_659_, 0);
lean_inc(v_k_693_);
v_v_694_ = lean_ctor_get(v_p_659_, 1);
lean_inc(v_v_694_);
v_p_695_ = lean_ctor_get(v_p_659_, 2);
lean_inc_ref(v_p_695_);
lean_dec_ref(v_p_659_);
v___x_696_ = lean_unsigned_to_nat(1u);
v___x_697_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3);
v___x_698_ = lean_int_dec_eq(v_k_693_, v___x_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_694_, v_a_660_, v_a_661_);
lean_dec(v_v_694_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___y_704_; lean_object* v_intZero_713_; uint8_t v_isNeg_714_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref(v___x_699_);
v___x_701_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1);
v___x_702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_702_, 0, v_r_658_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v_intZero_713_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v_isNeg_714_ = lean_int_dec_lt(v_k_693_, v_intZero_713_);
if (v_isNeg_714_ == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; 
v_a_715_ = lean_nat_abs(v_k_693_);
lean_dec(v_k_693_);
v___x_716_ = l_Nat_reprFast(v_a_715_);
v___y_704_ = v___x_716_;
goto v___jp_703_;
}
else
{
lean_object* v_abs_717_; lean_object* v_a_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_abs_717_ = lean_nat_abs(v_k_693_);
lean_dec(v_k_693_);
v_a_718_ = lean_nat_sub(v_abs_717_, v___x_696_);
lean_dec(v_abs_717_);
v___x_719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2));
v___x_720_ = lean_nat_add(v_a_718_, v___x_696_);
lean_dec(v_a_718_);
v___x_721_ = l_Nat_reprFast(v___x_720_);
v___x_722_ = lean_string_append(v___x_719_, v___x_721_);
lean_dec_ref(v___x_721_);
v___y_704_ = v___x_722_;
goto v___jp_703_;
}
v___jp_703_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_705_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_705_, 0, v___y_704_);
v___x_706_ = l_Lean_MessageData_ofFormat(v___x_705_);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_702_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__5);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_700_);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v_r_658_ = v___x_711_;
v_p_659_ = v_p_695_;
goto _start;
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec_ref(v_p_695_);
lean_dec(v_k_693_);
lean_dec_ref(v_r_658_);
v_a_723_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_699_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_699_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
else
{
lean_object* v___x_731_; 
lean_dec(v_k_693_);
v___x_731_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_694_, v_a_660_, v_a_661_);
lean_dec(v_v_694_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref(v___x_731_);
v___x_733_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1);
v___x_734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_734_, 0, v_r_658_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_732_);
v___x_736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v_r_658_ = v___x_736_;
v_p_659_ = v_p_695_;
goto _start;
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v_p_695_);
lean_dec_ref(v_r_658_);
v_a_738_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_731_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_731_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___boxed(lean_object* v_r_746_, lean_object* v_p_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(v_r_746_, v_p_747_, v_a_748_, v_a_749_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go(lean_object* v_r_752_, lean_object* v_p_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(v_r_752_, v_p_753_, v_a_754_, v_a_762_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___boxed(lean_object* v_r_766_, lean_object* v_p_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go(v_r_766_, v_p_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_a_769_);
lean_dec(v_a_768_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_pp___redArg(lean_object* v_p_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___y_785_; 
if (lean_obj_tag(v_p_780_) == 0)
{
lean_object* v_k_789_; lean_object* v_intZero_790_; uint8_t v_isNeg_791_; 
v_k_789_ = lean_ctor_get(v_p_780_, 0);
lean_inc(v_k_789_);
lean_dec_ref(v_p_780_);
v_intZero_790_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v_isNeg_791_ = lean_int_dec_lt(v_k_789_, v_intZero_790_);
if (v_isNeg_791_ == 0)
{
lean_object* v_a_792_; lean_object* v___x_793_; 
v_a_792_ = lean_nat_abs(v_k_789_);
lean_dec(v_k_789_);
v___x_793_ = l_Nat_reprFast(v_a_792_);
v___y_785_ = v___x_793_;
goto v___jp_784_;
}
else
{
lean_object* v_abs_794_; lean_object* v_one_795_; lean_object* v_a_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_abs_794_ = lean_nat_abs(v_k_789_);
lean_dec(v_k_789_);
v_one_795_ = lean_unsigned_to_nat(1u);
v_a_796_ = lean_nat_sub(v_abs_794_, v_one_795_);
lean_dec(v_abs_794_);
v___x_797_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2));
v___x_798_ = lean_nat_add(v_a_796_, v_one_795_);
lean_dec(v_a_796_);
v___x_799_ = l_Nat_reprFast(v___x_798_);
v___x_800_ = lean_string_append(v___x_797_, v___x_799_);
lean_dec_ref(v___x_799_);
v___y_785_ = v___x_800_;
goto v___jp_784_;
}
}
else
{
lean_object* v_k_801_; lean_object* v_v_802_; lean_object* v_p_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_k_801_ = lean_ctor_get(v_p_780_, 0);
lean_inc(v_k_801_);
v_v_802_ = lean_ctor_get(v_p_780_, 1);
lean_inc(v_v_802_);
v_p_803_ = lean_ctor_get(v_p_780_, 2);
lean_inc_ref(v_p_803_);
lean_dec_ref(v_p_780_);
v___x_804_ = lean_unsigned_to_nat(1u);
v___x_805_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3);
v___x_806_ = lean_int_dec_eq(v_k_801_, v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_802_, v_a_781_, v_a_782_);
lean_dec(v_v_802_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___y_810_; lean_object* v_intZero_818_; uint8_t v_isNeg_819_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref(v___x_807_);
v_intZero_818_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v_isNeg_819_ = lean_int_dec_lt(v_k_801_, v_intZero_818_);
if (v_isNeg_819_ == 0)
{
lean_object* v_a_820_; lean_object* v___x_821_; 
v_a_820_ = lean_nat_abs(v_k_801_);
lean_dec(v_k_801_);
v___x_821_ = l_Nat_reprFast(v_a_820_);
v___y_810_ = v___x_821_;
goto v___jp_809_;
}
else
{
lean_object* v_abs_822_; lean_object* v_a_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_abs_822_ = lean_nat_abs(v_k_801_);
lean_dec(v_k_801_);
v_a_823_ = lean_nat_sub(v_abs_822_, v___x_804_);
lean_dec(v_abs_822_);
v___x_824_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2));
v___x_825_ = lean_nat_add(v_a_823_, v___x_804_);
lean_dec(v_a_823_);
v___x_826_ = l_Nat_reprFast(v___x_825_);
v___x_827_ = lean_string_append(v___x_824_, v___x_826_);
lean_dec_ref(v___x_826_);
v___y_810_ = v___x_827_;
goto v___jp_809_;
}
v___jp_809_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_811_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_811_, 0, v___y_810_);
v___x_812_ = l_Lean_MessageData_ofFormat(v___x_811_);
v___x_813_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__5);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_808_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(v___x_816_, v_p_803_, v_a_781_, v_a_782_);
return v___x_817_;
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec_ref(v_p_803_);
lean_dec(v_k_801_);
v_a_828_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_807_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_807_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
else
{
lean_object* v___x_836_; 
lean_dec(v_k_801_);
v___x_836_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_v_802_, v_a_781_, v_a_782_);
lean_dec(v_v_802_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref(v___x_836_);
v___x_838_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_837_);
v___x_839_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(v___x_838_, v_p_803_, v_a_781_, v_a_782_);
return v___x_839_;
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v_p_803_);
v_a_840_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_836_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_836_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
v___jp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_786_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_786_, 0, v___y_785_);
v___x_787_ = l_Lean_MessageData_ofFormat(v___x_786_);
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
return v___x_788_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_pp___redArg___boxed(lean_object* v_p_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Int_Linear_Poly_pp___redArg(v_p_848_, v_a_849_, v_a_850_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_pp(lean_object* v_p_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Int_Linear_Poly_pp___redArg(v_p_853_, v_a_854_, v_a_862_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_pp___boxed(lean_object* v_p_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Int_Linear_Poly_pp(v_p_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec_ref(v_a_869_);
lean_dec(v_a_868_);
lean_dec(v_a_867_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0(lean_object* v_a_879_, lean_object* v___x_880_, lean_object* v_x_881_){
_start:
{
lean_object* v_size_882_; uint8_t v___x_883_; 
v_size_882_ = lean_ctor_get(v_a_879_, 2);
v___x_883_ = lean_nat_dec_lt(v_x_881_, v_size_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; 
lean_dec_ref(v_a_879_);
v___x_884_ = l_outOfBounds___redArg(v___x_880_);
return v___x_884_;
}
else
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_PersistentArray_get_x21___redArg(v___x_880_, v_a_879_, v_x_881_);
return v___x_885_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed(lean_object* v_a_886_, lean_object* v___x_887_, lean_object* v_x_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0(v_a_886_, v___x_887_, v_x_888_);
lean_dec(v_x_888_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___redArg(lean_object* v_p_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_896_; lean_object* v___f_897_; lean_object* v___x_898_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref(v___x_894_);
v___x_896_ = l_Lean_instInhabitedExpr;
v___f_897_ = lean_alloc_closure((void*)(l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_897_, 0, v_a_895_);
lean_closure_set(v___f_897_, 1, v___x_896_);
v___x_898_ = l_Int_Linear_Poly_denoteExpr___redArg(v___f_897_, v_p_890_);
return v___x_898_;
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec_ref(v_p_890_);
v_a_899_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_894_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_894_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___redArg___boxed(lean_object* v_p_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_907_, v_a_908_, v_a_909_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27(lean_object* v_p_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_912_, v_a_913_, v_a_921_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_x27___boxed(lean_object* v_p_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Int_Linear_Poly_denoteExpr_x27(v_p_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec(v_a_926_);
return v_res_937_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object* v_c_938_){
_start:
{
lean_object* v_p_939_; 
v_p_939_ = lean_ctor_get(v_c_938_, 1);
if (lean_obj_tag(v_p_939_) == 0)
{
lean_object* v_d_940_; lean_object* v_k_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v_d_940_ = lean_ctor_get(v_c_938_, 0);
v_k_941_ = lean_ctor_get(v_p_939_, 0);
v___x_942_ = lean_int_emod(v_k_941_, v_d_940_);
v___x_943_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_944_ = lean_int_dec_eq(v___x_942_, v___x_943_);
lean_dec(v___x_942_);
return v___x_944_;
}
else
{
lean_object* v_d_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
v_d_945_ = lean_ctor_get(v_c_938_, 0);
v___x_946_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3);
v___x_947_ = lean_int_dec_eq(v_d_945_, v___x_946_);
return v___x_947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial___boxed(lean_object* v_c_948_){
_start:
{
uint8_t v_res_949_; lean_object* v_r_950_; 
v_res_949_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_c_948_);
lean_dec_ref(v_c_948_);
v_r_950_ = lean_box(v_res_949_);
return v_r_950_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0));
v___x_953_ = l_Lean_stringToMessageData(v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object* v_c_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_d_958_; lean_object* v_p_959_; lean_object* v___x_960_; 
v_d_958_ = lean_ctor_get(v_c_954_, 0);
lean_inc(v_d_958_);
v_p_959_ = lean_ctor_get(v_c_954_, 1);
lean_inc_ref(v_p_959_);
lean_dec_ref(v_c_954_);
v___x_960_ = l_Int_Linear_Poly_pp___redArg(v_p_959_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_986_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_986_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_986_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_986_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___y_966_; lean_object* v_intZero_975_; uint8_t v_isNeg_976_; 
v_intZero_975_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v_isNeg_976_ = lean_int_dec_lt(v_d_958_, v_intZero_975_);
if (v_isNeg_976_ == 0)
{
lean_object* v_a_977_; lean_object* v___x_978_; 
v_a_977_ = lean_nat_abs(v_d_958_);
lean_dec(v_d_958_);
v___x_978_ = l_Nat_reprFast(v_a_977_);
v___y_966_ = v___x_978_;
goto v___jp_965_;
}
else
{
lean_object* v_abs_979_; lean_object* v_one_980_; lean_object* v_a_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_abs_979_ = lean_nat_abs(v_d_958_);
lean_dec(v_d_958_);
v_one_980_ = lean_unsigned_to_nat(1u);
v_a_981_ = lean_nat_sub(v_abs_979_, v_one_980_);
lean_dec(v_abs_979_);
v___x_982_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2));
v___x_983_ = lean_nat_add(v_a_981_, v_one_980_);
lean_dec(v_a_981_);
v___x_984_ = l_Nat_reprFast(v___x_983_);
v___x_985_ = lean_string_append(v___x_982_, v___x_984_);
lean_dec_ref(v___x_984_);
v___y_966_ = v___x_985_;
goto v___jp_965_;
}
v___jp_965_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_967_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_967_, 0, v___y_966_);
v___x_968_ = l_Lean_MessageData_ofFormat(v___x_967_);
v___x_969_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1);
v___x_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v_a_961_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_971_);
v___x_973_ = v___x_963_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
else
{
lean_dec(v_d_958_);
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___boxed(lean_object* v_c_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_987_, v_a_988_, v_a_989_);
lean_dec_ref(v_a_989_);
lean_dec(v_a_988_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(lean_object* v_c_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_992_, v_a_993_, v_a_1001_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___boxed(lean_object* v_c_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(v_c_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec(v_a_1006_);
return v_res_1017_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = l_Lean_Level_ofNat(v___x_1023_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3);
v___x_1027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___x_1025_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4);
v___x_1029_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2));
v___x_1030_ = l_Lean_Expr_const___override(v___x_1029_, v___x_1028_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = lean_box(0);
v___x_1035_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7));
v___x_1036_ = l_Lean_Expr_const___override(v___x_1035_, v___x_1034_);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1041_ = lean_box(0);
v___x_1042_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10));
v___x_1043_ = l_Lean_Expr_const___override(v___x_1042_, v___x_1041_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(lean_object* v_c_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_d_1048_; lean_object* v_p_1049_; lean_object* v___x_1050_; 
v_d_1048_ = lean_ctor_get(v_c_1044_, 0);
lean_inc(v_d_1048_);
v_p_1049_ = lean_ctor_get(v_c_1044_, 1);
lean_inc_ref(v_p_1049_);
lean_dec_ref(v_c_1044_);
v___x_1050_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_1049_, v_a_1045_, v_a_1046_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1072_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1072_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1072_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___y_1056_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1061_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1062_ = lean_int_dec_le(v___x_1061_, v_d_1048_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1063_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5);
v___x_1064_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8);
v___x_1065_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11);
v___x_1066_ = lean_int_neg(v_d_1048_);
lean_dec(v_d_1048_);
v___x_1067_ = l_Int_toNat(v___x_1066_);
lean_dec(v___x_1066_);
v___x_1068_ = l_Lean_instToExprInt_mkNat(v___x_1067_);
v___x_1069_ = l_Lean_mkApp3(v___x_1063_, v___x_1064_, v___x_1065_, v___x_1068_);
v___y_1056_ = v___x_1069_;
goto v___jp_1055_;
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = l_Int_toNat(v_d_1048_);
lean_dec(v_d_1048_);
v___x_1071_ = l_Lean_instToExprInt_mkNat(v___x_1070_);
v___y_1056_ = v___x_1071_;
goto v___jp_1055_;
}
v___jp_1055_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = l_Lean_mkIntDvd(v___y_1056_, v_a_1051_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1057_);
v___x_1059_ = v___x_1053_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
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
lean_dec(v_d_1048_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1073_, v_a_1074_, v_a_1075_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(lean_object* v_c_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(v_c_1078_, v_a_1079_, v_a_1087_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___boxed(lean_object* v_c_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(v_c_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
lean_dec(v_a_1092_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(lean_object* v_msgData_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v_env_1111_; lean_object* v___x_1112_; lean_object* v_mctx_1113_; lean_object* v_lctx_1114_; lean_object* v_options_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1110_ = lean_st_ref_get(v___y_1108_);
v_env_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc_ref(v_env_1111_);
lean_dec(v___x_1110_);
v___x_1112_ = lean_st_ref_get(v___y_1106_);
v_mctx_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc_ref(v_mctx_1113_);
lean_dec(v___x_1112_);
v_lctx_1114_ = lean_ctor_get(v___y_1105_, 2);
v_options_1115_ = lean_ctor_get(v___y_1107_, 2);
lean_inc_ref(v_options_1115_);
lean_inc_ref(v_lctx_1114_);
v___x_1116_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1116_, 0, v_env_1111_);
lean_ctor_set(v___x_1116_, 1, v_mctx_1113_);
lean_ctor_set(v___x_1116_, 2, v_lctx_1114_);
lean_ctor_set(v___x_1116_, 3, v_options_1115_);
v___x_1117_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v_msgData_1104_);
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0___boxed(lean_object* v_msgData_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msgData_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(lean_object* v_msg_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_ref_1132_; lean_object* v___x_1133_; lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1142_; 
v_ref_1132_ = lean_ctor_get(v___y_1129_, 5);
v___x_1133_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msg_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
lean_inc(v_ref_1132_);
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v_ref_1132_);
lean_ctor_set(v___x_1138_, 1, v_a_1134_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set_tag(v___x_1136_, 1);
lean_ctor_set(v___x_1136_, 0, v___x_1138_);
v___x_1140_ = v___x_1136_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg___boxed(lean_object* v_msg_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
return v_res_1149_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0));
v___x_1152_ = l_Lean_stringToMessageData(v___x_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2));
v___x_1155_ = l_Lean_stringToMessageData(v___x_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object* v_c_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_1156_, v_a_1157_, v_a_1165_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref(v___x_1168_);
v___x_1170_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1171_ = l_Lean_indentD(v_a_1169_);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3);
v___x_1174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1174_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
return v___x_1175_;
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
v_a_1176_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1168_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1168_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec(v_a_1185_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(lean_object* v_00_u03b1_1197_, lean_object* v_c_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_c_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1211_, lean_object* v_c_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(v_00_u03b1_1211_, v_c_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec(v_a_1213_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(lean_object* v_00_u03b1_1225_, lean_object* v_msg_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_1226_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___boxed(lean_object* v_00_u03b1_1239_, lean_object* v_msg_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(v_00_u03b1_1239_, v_msg_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec(v___y_1241_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial_spec__0(lean_object* v_a_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_nat_to_int(v_a_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(lean_object* v_c_1255_){
_start:
{
lean_object* v_p_1256_; 
v_p_1256_ = lean_ctor_get(v_c_1255_, 0);
if (lean_obj_tag(v_p_1256_) == 0)
{
lean_object* v_k_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v_k_1257_ = lean_ctor_get(v_p_1256_, 0);
v___x_1258_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1259_ = lean_int_dec_eq(v_k_1257_, v___x_1258_);
if (v___x_1259_ == 0)
{
uint8_t v___x_1260_; 
v___x_1260_ = 1;
return v___x_1260_;
}
else
{
uint8_t v___x_1261_; 
v___x_1261_ = 0;
return v___x_1261_;
}
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1262_ = l_Int_Linear_Poly_getConst(v_p_1256_);
v___x_1263_ = l_Int_Linear_Poly_gcdCoeffs_x27(v_p_1256_);
v___x_1264_ = lean_nat_to_int(v___x_1263_);
v___x_1265_ = lean_int_emod(v___x_1262_, v___x_1264_);
lean_dec(v___x_1264_);
lean_dec(v___x_1262_);
v___x_1266_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1267_ = lean_int_dec_eq(v___x_1265_, v___x_1266_);
lean_dec(v___x_1265_);
if (v___x_1267_ == 0)
{
uint8_t v___x_1268_; 
v___x_1268_ = 1;
return v___x_1268_;
}
else
{
uint8_t v___x_1269_; 
v___x_1269_ = 0;
return v___x_1269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial___boxed(lean_object* v_c_1270_){
_start:
{
uint8_t v_res_1271_; lean_object* v_r_1272_; 
v_res_1271_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(v_c_1270_);
lean_dec_ref(v_c_1270_);
v_r_1272_ = lean_box(v_res_1271_);
return v_r_1272_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0));
v___x_1275_ = l_Lean_stringToMessageData(v___x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(lean_object* v_c_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v_p_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1297_; 
v_p_1280_ = lean_ctor_get(v_c_1276_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_c_1276_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; 
v_unused_1298_ = lean_ctor_get(v_c_1276_, 1);
lean_dec(v_unused_1298_);
v___x_1282_ = v_c_1276_;
v_isShared_1283_ = v_isSharedCheck_1297_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_p_1280_);
lean_dec(v_c_1276_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1297_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Int_Linear_Poly_pp___redArg(v_p_1280_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1296_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1296_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1296_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1289_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1);
if (v_isShared_1283_ == 0)
{
lean_ctor_set_tag(v___x_1282_, 7);
lean_ctor_set(v___x_1282_, 1, v___x_1289_);
lean_ctor_set(v___x_1282_, 0, v_a_1285_);
v___x_1291_ = v___x_1282_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1285_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1293_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1291_);
v___x_1293_ = v___x_1287_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_del_object(v___x_1282_);
return v___x_1284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___boxed(lean_object* v_c_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1299_, v_a_1300_, v_a_1301_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(lean_object* v_c_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1304_, v_a_1305_, v_a_1313_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___boxed(lean_object* v_c_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(v_c_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
lean_dec(v_a_1319_);
lean_dec(v_a_1318_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(lean_object* v_c_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_1330_, v_a_1331_, v_a_1334_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref(v___x_1337_);
v___x_1339_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1340_ = l_Lean_indentD(v_a_1338_);
v___x_1341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1339_);
lean_ctor_set(v___x_1341_, 1, v___x_1340_);
v___x_1342_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1341_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
return v___x_1342_;
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
v_a_1343_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1337_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1337_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(lean_object* v_00_u03b1_1359_, lean_object* v_c_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(v_c_1360_, v_a_1361_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1373_, lean_object* v_c_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(v_00_u03b1_1373_, v_c_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec_ref(v_a_1377_);
lean_dec(v_a_1376_);
lean_dec(v_a_1375_);
return v_res_1386_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1388_ = l_Lean_mkIntLit(v___x_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(lean_object* v_c_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_p_1393_; lean_object* v___x_1394_; 
v_p_1393_ = lean_ctor_get(v_c_1389_, 0);
lean_inc_ref(v_p_1393_);
lean_dec_ref(v_c_1389_);
v___x_1394_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_1393_, v_a_1390_, v_a_1391_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1405_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1397_ = v___x_1394_;
v_isShared_1398_ = v_isSharedCheck_1405_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1405_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1399_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1400_ = l_Lean_mkIntEq(v_a_1395_, v___x_1399_);
v___x_1401_ = l_Lean_mkNot(v___x_1400_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1401_);
v___x_1403_ = v___x_1397_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
else
{
return v___x_1394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1406_, v_a_1407_, v_a_1408_);
lean_dec_ref(v_a_1408_);
lean_dec(v_a_1407_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(lean_object* v_c_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(v_c_1411_, v_a_1412_, v_a_1420_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___boxed(lean_object* v_c_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(v_c_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec(v_a_1425_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert___boxed(lean_object* v_c_1449_, lean_object* v_a_00___x40___internal___hyg_1450_, lean_object* v_a_00___x40___internal___hyg_1451_, lean_object* v_a_00___x40___internal___hyg_1452_, lean_object* v_a_00___x40___internal___hyg_1453_, lean_object* v_a_00___x40___internal___hyg_1454_, lean_object* v_a_00___x40___internal___hyg_1455_, lean_object* v_a_00___x40___internal___hyg_1456_, lean_object* v_a_00___x40___internal___hyg_1457_, lean_object* v_a_00___x40___internal___hyg_1458_, lean_object* v_a_00___x40___internal___hyg_1459_, lean_object* v_a_00___x40___internal___hyg_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = lean_grind_cutsat_assert_le(v_c_1449_, v_a_00___x40___internal___hyg_1450_, v_a_00___x40___internal___hyg_1451_, v_a_00___x40___internal___hyg_1452_, v_a_00___x40___internal___hyg_1453_, v_a_00___x40___internal___hyg_1454_, v_a_00___x40___internal___hyg_1455_, v_a_00___x40___internal___hyg_1456_, v_a_00___x40___internal___hyg_1457_, v_a_00___x40___internal___hyg_1458_, v_a_00___x40___internal___hyg_1459_);
return v_res_1461_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(lean_object* v_c_1462_){
_start:
{
lean_object* v_p_1463_; 
v_p_1463_ = lean_ctor_get(v_c_1462_, 0);
if (lean_obj_tag(v_p_1463_) == 0)
{
lean_object* v_k_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v_k_1464_ = lean_ctor_get(v_p_1463_, 0);
v___x_1465_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1466_ = lean_int_dec_le(v_k_1464_, v___x_1465_);
return v___x_1466_;
}
else
{
uint8_t v___x_1467_; 
v___x_1467_ = 0;
return v___x_1467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial___boxed(lean_object* v_c_1468_){
_start:
{
uint8_t v_res_1469_; lean_object* v_r_1470_; 
v_res_1469_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_c_1468_);
lean_dec_ref(v_c_1468_);
v_r_1470_ = lean_box(v_res_1469_);
return v_r_1470_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0));
v___x_1473_ = l_Lean_stringToMessageData(v___x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(lean_object* v_c_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_p_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1495_; 
v_p_1478_ = lean_ctor_get(v_c_1474_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_c_1474_);
if (v_isSharedCheck_1495_ == 0)
{
lean_object* v_unused_1496_; 
v_unused_1496_ = lean_ctor_get(v_c_1474_, 1);
lean_dec(v_unused_1496_);
v___x_1480_ = v_c_1474_;
v_isShared_1481_ = v_isSharedCheck_1495_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_p_1478_);
lean_dec(v_c_1474_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1495_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Int_Linear_Poly_pp___redArg(v_p_1478_, v_a_1475_, v_a_1476_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1494_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1494_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1494_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1487_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1);
if (v_isShared_1481_ == 0)
{
lean_ctor_set_tag(v___x_1480_, 7);
lean_ctor_set(v___x_1480_, 1, v___x_1487_);
lean_ctor_set(v___x_1480_, 0, v_a_1483_);
v___x_1489_ = v___x_1480_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1483_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1491_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1489_);
v___x_1491_ = v___x_1485_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
else
{
lean_del_object(v___x_1480_);
return v___x_1482_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___boxed(lean_object* v_c_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1497_, v_a_1498_, v_a_1499_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(lean_object* v_c_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1502_, v_a_1503_, v_a_1511_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___boxed(lean_object* v_c_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(v_c_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
lean_dec(v_a_1523_);
lean_dec_ref(v_a_1522_);
lean_dec(v_a_1521_);
lean_dec_ref(v_a_1520_);
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_a_1517_);
lean_dec(v_a_1516_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(lean_object* v_c_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_p_1532_; lean_object* v___x_1533_; 
v_p_1532_ = lean_ctor_get(v_c_1528_, 0);
lean_inc_ref(v_p_1532_);
lean_dec_ref(v_c_1528_);
v___x_1533_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_1532_, v_a_1529_, v_a_1530_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1543_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1536_ = v___x_1533_;
v_isShared_1537_ = v_isSharedCheck_1543_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1543_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1538_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1539_ = l_Lean_mkIntLE(v_a_1534_, v___x_1538_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1539_);
v___x_1541_ = v___x_1536_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
else
{
return v___x_1533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1544_, v_a_1545_, v_a_1546_);
lean_dec_ref(v_a_1546_);
lean_dec(v_a_1545_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(lean_object* v_c_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_1549_, v_a_1550_, v_a_1558_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___boxed(lean_object* v_c_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(v_c_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
lean_dec(v_a_1566_);
lean_dec_ref(v_a_1565_);
lean_dec(v_a_1564_);
lean_dec(v_a_1563_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(lean_object* v_c_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_1575_, v_a_1576_, v_a_1579_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref(v___x_1582_);
v___x_1584_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1585_ = l_Lean_indentD(v_a_1583_);
v___x_1586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1586_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
return v___x_1587_;
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
v_a_1588_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1582_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1582_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec(v_a_1597_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(lean_object* v_00_u03b1_1604_, lean_object* v_c_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1605_, v_a_1606_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1618_, lean_object* v_c_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(v_00_u03b1_1618_, v_c_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec(v_a_1620_);
return v_res_1631_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(lean_object* v_c_1632_){
_start:
{
lean_object* v_p_1633_; 
v_p_1633_ = lean_ctor_get(v_c_1632_, 0);
if (lean_obj_tag(v_p_1633_) == 0)
{
lean_object* v_k_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v_k_1634_ = lean_ctor_get(v_p_1633_, 0);
v___x_1635_ = lean_obj_once(&l_Int_Linear_Poly_isZero___closed__0, &l_Int_Linear_Poly_isZero___closed__0_once, _init_l_Int_Linear_Poly_isZero___closed__0);
v___x_1636_ = lean_int_dec_eq(v_k_1634_, v___x_1635_);
return v___x_1636_;
}
else
{
uint8_t v___x_1637_; 
v___x_1637_ = 0;
return v___x_1637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial___boxed(lean_object* v_c_1638_){
_start:
{
uint8_t v_res_1639_; lean_object* v_r_1640_; 
v_res_1639_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(v_c_1638_);
lean_dec_ref(v_c_1638_);
v_r_1640_ = lean_box(v_res_1639_);
return v_r_1640_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0));
v___x_1643_ = l_Lean_stringToMessageData(v___x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object* v_c_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_p_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1665_; 
v_p_1648_ = lean_ctor_get(v_c_1644_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_c_1644_);
if (v_isSharedCheck_1665_ == 0)
{
lean_object* v_unused_1666_; 
v_unused_1666_ = lean_ctor_get(v_c_1644_, 1);
lean_dec(v_unused_1666_);
v___x_1650_ = v_c_1644_;
v_isShared_1651_ = v_isSharedCheck_1665_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_p_1648_);
lean_dec(v_c_1644_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1665_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Int_Linear_Poly_pp___redArg(v_p_1648_, v_a_1645_, v_a_1646_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1664_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1664_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1664_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1657_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1);
if (v_isShared_1651_ == 0)
{
lean_ctor_set_tag(v___x_1650_, 7);
lean_ctor_set(v___x_1650_, 1, v___x_1657_);
lean_ctor_set(v___x_1650_, 0, v_a_1653_);
v___x_1659_ = v___x_1650_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1653_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1661_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1659_);
v___x_1661_ = v___x_1655_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_del_object(v___x_1650_);
return v___x_1652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___boxed(lean_object* v_c_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1667_, v_a_1668_, v_a_1669_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(lean_object* v_c_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1672_, v_a_1673_, v_a_1681_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___boxed(lean_object* v_c_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(v_c_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
lean_dec(v_a_1695_);
lean_dec_ref(v_a_1694_);
lean_dec(v_a_1693_);
lean_dec_ref(v_a_1692_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec(v_a_1686_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(lean_object* v_c_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_p_1702_; lean_object* v___x_1703_; 
v_p_1702_ = lean_ctor_get(v_c_1698_, 0);
lean_inc_ref(v_p_1702_);
lean_dec_ref(v_c_1698_);
v___x_1703_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_1702_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1713_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1706_ = v___x_1703_;
v_isShared_1707_ = v_isSharedCheck_1713_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1703_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1713_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1708_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
v___x_1709_ = l_Lean_mkIntEq(v_a_1704_, v___x_1708_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 0, v___x_1709_);
v___x_1711_ = v___x_1706_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
else
{
return v___x_1703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg___boxed(lean_object* v_c_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1714_, v_a_1715_, v_a_1716_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(lean_object* v_c_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_1719_, v_a_1720_, v_a_1728_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___boxed(lean_object* v_c_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(v_c_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(lean_object* v_c_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_1745_, v_a_1746_, v_a_1749_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref(v___x_1752_);
v___x_1754_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
v___x_1755_ = l_Lean_indentD(v_a_1753_);
v___x_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1754_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_1756_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
return v___x_1757_;
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
v_a_1758_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1752_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1752_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg___boxed(lean_object* v_c_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_);
lean_dec(v_a_1771_);
lean_dec_ref(v_a_1770_);
lean_dec(v_a_1769_);
lean_dec_ref(v_a_1768_);
lean_dec(v_a_1767_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(lean_object* v_00_u03b1_1774_, lean_object* v_c_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(v_c_1775_, v_a_1776_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___boxed(lean_object* v_00_u03b1_1788_, lean_object* v_c_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(v_00_u03b1_1788_, v_c_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(lean_object* v_x_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1823_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1823_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1823_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v_occurs_1811_; lean_object* v_size_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v_occurs_1811_ = lean_ctor_get(v_a_1807_, 12);
lean_inc_ref(v_occurs_1811_);
lean_dec(v_a_1807_);
v_size_1812_ = lean_ctor_get(v_occurs_1811_, 2);
v___x_1813_ = lean_box(1);
v___x_1814_ = lean_nat_dec_lt(v_x_1802_, v_size_1812_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
lean_dec_ref(v_occurs_1811_);
v___x_1815_ = l_outOfBounds___redArg(v___x_1813_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1815_);
v___x_1817_ = v___x_1809_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1813_, v_occurs_1811_, v_x_1802_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1819_);
v___x_1821_ = v___x_1809_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1806_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1806_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg___boxed(lean_object* v_x_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_1832_, v_a_1833_, v_a_1834_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec(v_x_1832_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(lean_object* v_x_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_1837_, v_a_1838_, v_a_1846_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___boxed(lean_object* v_x_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(v_x_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1855_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
lean_dec(v_a_1852_);
lean_dec(v_a_1851_);
lean_dec(v_x_1850_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(lean_object* v_k_1863_, lean_object* v_v_1864_, lean_object* v_t_1865_){
_start:
{
if (lean_obj_tag(v_t_1865_) == 0)
{
lean_object* v_size_1866_; lean_object* v_k_1867_; lean_object* v_v_1868_; lean_object* v_l_1869_; lean_object* v_r_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_2151_; 
v_size_1866_ = lean_ctor_get(v_t_1865_, 0);
v_k_1867_ = lean_ctor_get(v_t_1865_, 1);
v_v_1868_ = lean_ctor_get(v_t_1865_, 2);
v_l_1869_ = lean_ctor_get(v_t_1865_, 3);
v_r_1870_ = lean_ctor_get(v_t_1865_, 4);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_t_1865_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_1872_ = v_t_1865_;
v_isShared_1873_ = v_isSharedCheck_2151_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_r_1870_);
lean_inc(v_l_1869_);
lean_inc(v_v_1868_);
lean_inc(v_k_1867_);
lean_inc(v_size_1866_);
lean_dec(v_t_1865_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_2151_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
uint8_t v___x_1874_; 
v___x_1874_ = lean_nat_dec_lt(v_k_1863_, v_k_1867_);
if (v___x_1874_ == 0)
{
uint8_t v___x_1875_; 
v___x_1875_ = lean_nat_dec_eq(v_k_1863_, v_k_1867_);
if (v___x_1875_ == 0)
{
lean_object* v_impl_1876_; lean_object* v___x_1877_; 
lean_dec(v_size_1866_);
v_impl_1876_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_1863_, v_v_1864_, v_r_1870_);
v___x_1877_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1869_) == 0)
{
lean_object* v_size_1878_; lean_object* v_size_1879_; lean_object* v_k_1880_; lean_object* v_v_1881_; lean_object* v_l_1882_; lean_object* v_r_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v_size_1878_ = lean_ctor_get(v_l_1869_, 0);
v_size_1879_ = lean_ctor_get(v_impl_1876_, 0);
lean_inc(v_size_1879_);
v_k_1880_ = lean_ctor_get(v_impl_1876_, 1);
lean_inc(v_k_1880_);
v_v_1881_ = lean_ctor_get(v_impl_1876_, 2);
lean_inc(v_v_1881_);
v_l_1882_ = lean_ctor_get(v_impl_1876_, 3);
lean_inc(v_l_1882_);
v_r_1883_ = lean_ctor_get(v_impl_1876_, 4);
lean_inc(v_r_1883_);
v___x_1884_ = lean_unsigned_to_nat(3u);
v___x_1885_ = lean_nat_mul(v___x_1884_, v_size_1878_);
v___x_1886_ = lean_nat_dec_lt(v___x_1885_, v_size_1879_);
lean_dec(v___x_1885_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
lean_dec(v_r_1883_);
lean_dec(v_l_1882_);
lean_dec(v_v_1881_);
lean_dec(v_k_1880_);
v___x_1887_ = lean_nat_add(v___x_1877_, v_size_1878_);
v___x_1888_ = lean_nat_add(v___x_1887_, v_size_1879_);
lean_dec(v_size_1879_);
lean_dec(v___x_1887_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 4, v_impl_1876_);
lean_ctor_set(v___x_1872_, 0, v___x_1888_);
v___x_1890_ = v___x_1872_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_k_1867_);
lean_ctor_set(v_reuseFailAlloc_1891_, 2, v_v_1868_);
lean_ctor_set(v_reuseFailAlloc_1891_, 3, v_l_1869_);
lean_ctor_set(v_reuseFailAlloc_1891_, 4, v_impl_1876_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
else
{
lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1955_; 
v_isSharedCheck_1955_ = !lean_is_exclusive(v_impl_1876_);
if (v_isSharedCheck_1955_ == 0)
{
lean_object* v_unused_1956_; lean_object* v_unused_1957_; lean_object* v_unused_1958_; lean_object* v_unused_1959_; lean_object* v_unused_1960_; 
v_unused_1956_ = lean_ctor_get(v_impl_1876_, 4);
lean_dec(v_unused_1956_);
v_unused_1957_ = lean_ctor_get(v_impl_1876_, 3);
lean_dec(v_unused_1957_);
v_unused_1958_ = lean_ctor_get(v_impl_1876_, 2);
lean_dec(v_unused_1958_);
v_unused_1959_ = lean_ctor_get(v_impl_1876_, 1);
lean_dec(v_unused_1959_);
v_unused_1960_ = lean_ctor_get(v_impl_1876_, 0);
lean_dec(v_unused_1960_);
v___x_1893_ = v_impl_1876_;
v_isShared_1894_ = v_isSharedCheck_1955_;
goto v_resetjp_1892_;
}
else
{
lean_dec(v_impl_1876_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1955_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v_size_1895_; lean_object* v_k_1896_; lean_object* v_v_1897_; lean_object* v_l_1898_; lean_object* v_r_1899_; lean_object* v_size_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; 
v_size_1895_ = lean_ctor_get(v_l_1882_, 0);
v_k_1896_ = lean_ctor_get(v_l_1882_, 1);
v_v_1897_ = lean_ctor_get(v_l_1882_, 2);
v_l_1898_ = lean_ctor_get(v_l_1882_, 3);
v_r_1899_ = lean_ctor_get(v_l_1882_, 4);
v_size_1900_ = lean_ctor_get(v_r_1883_, 0);
v___x_1901_ = lean_unsigned_to_nat(2u);
v___x_1902_ = lean_nat_mul(v___x_1901_, v_size_1900_);
v___x_1903_ = lean_nat_dec_lt(v_size_1895_, v___x_1902_);
lean_dec(v___x_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1931_; 
lean_inc(v_r_1899_);
lean_inc(v_l_1898_);
lean_inc(v_v_1897_);
lean_inc(v_k_1896_);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_l_1882_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; lean_object* v_unused_1933_; lean_object* v_unused_1934_; lean_object* v_unused_1935_; lean_object* v_unused_1936_; 
v_unused_1932_ = lean_ctor_get(v_l_1882_, 4);
lean_dec(v_unused_1932_);
v_unused_1933_ = lean_ctor_get(v_l_1882_, 3);
lean_dec(v_unused_1933_);
v_unused_1934_ = lean_ctor_get(v_l_1882_, 2);
lean_dec(v_unused_1934_);
v_unused_1935_ = lean_ctor_get(v_l_1882_, 1);
lean_dec(v_unused_1935_);
v_unused_1936_ = lean_ctor_get(v_l_1882_, 0);
lean_dec(v_unused_1936_);
v___x_1905_ = v_l_1882_;
v_isShared_1906_ = v_isSharedCheck_1931_;
goto v_resetjp_1904_;
}
else
{
lean_dec(v_l_1882_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1931_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1921_; 
v___x_1907_ = lean_nat_add(v___x_1877_, v_size_1878_);
v___x_1908_ = lean_nat_add(v___x_1907_, v_size_1879_);
lean_dec(v_size_1879_);
if (lean_obj_tag(v_l_1898_) == 0)
{
lean_object* v_size_1929_; 
v_size_1929_ = lean_ctor_get(v_l_1898_, 0);
lean_inc(v_size_1929_);
v___y_1921_ = v_size_1929_;
goto v___jp_1920_;
}
else
{
lean_object* v___x_1930_; 
v___x_1930_ = lean_unsigned_to_nat(0u);
v___y_1921_ = v___x_1930_;
goto v___jp_1920_;
}
v___jp_1909_:
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
v___x_1913_ = lean_nat_add(v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec(v___y_1911_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 4, v_r_1883_);
lean_ctor_set(v___x_1905_, 3, v_r_1899_);
lean_ctor_set(v___x_1905_, 2, v_v_1881_);
lean_ctor_set(v___x_1905_, 1, v_k_1880_);
lean_ctor_set(v___x_1905_, 0, v___x_1913_);
v___x_1915_ = v___x_1905_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_k_1880_);
lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_v_1881_);
lean_ctor_set(v_reuseFailAlloc_1919_, 3, v_r_1899_);
lean_ctor_set(v_reuseFailAlloc_1919_, 4, v_r_1883_);
v___x_1915_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1917_; 
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 4, v___x_1915_);
lean_ctor_set(v___x_1893_, 3, v___y_1910_);
lean_ctor_set(v___x_1893_, 2, v_v_1897_);
lean_ctor_set(v___x_1893_, 1, v_k_1896_);
lean_ctor_set(v___x_1893_, 0, v___x_1908_);
v___x_1917_ = v___x_1893_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1908_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_k_1896_);
lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_v_1897_);
lean_ctor_set(v_reuseFailAlloc_1918_, 3, v___y_1910_);
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
v___jp_1920_:
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1922_ = lean_nat_add(v___x_1907_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec(v___x_1907_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 4, v_l_1898_);
lean_ctor_set(v___x_1872_, 0, v___x_1922_);
v___x_1924_ = v___x_1872_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1922_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_k_1867_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v_v_1868_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v_l_1869_);
lean_ctor_set(v_reuseFailAlloc_1928_, 4, v_l_1898_);
v___x_1924_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1925_; 
v___x_1925_ = lean_nat_add(v___x_1877_, v_size_1900_);
if (lean_obj_tag(v_r_1899_) == 0)
{
lean_object* v_size_1926_; 
v_size_1926_ = lean_ctor_get(v_r_1899_, 0);
lean_inc(v_size_1926_);
v___y_1910_ = v___x_1924_;
v___y_1911_ = v___x_1925_;
v___y_1912_ = v_size_1926_;
goto v___jp_1909_;
}
else
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_unsigned_to_nat(0u);
v___y_1910_ = v___x_1924_;
v___y_1911_ = v___x_1925_;
v___y_1912_ = v___x_1927_;
goto v___jp_1909_;
}
}
}
}
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
lean_del_object(v___x_1872_);
v___x_1937_ = lean_nat_add(v___x_1877_, v_size_1878_);
v___x_1938_ = lean_nat_add(v___x_1937_, v_size_1879_);
lean_dec(v_size_1879_);
v___x_1939_ = lean_nat_add(v___x_1937_, v_size_1895_);
lean_dec(v___x_1937_);
lean_inc_ref(v_l_1869_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 4, v_l_1882_);
lean_ctor_set(v___x_1893_, 3, v_l_1869_);
lean_ctor_set(v___x_1893_, 2, v_v_1868_);
lean_ctor_set(v___x_1893_, 1, v_k_1867_);
lean_ctor_set(v___x_1893_, 0, v___x_1939_);
v___x_1941_ = v___x_1893_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1939_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_k_1867_);
lean_ctor_set(v_reuseFailAlloc_1954_, 2, v_v_1868_);
lean_ctor_set(v_reuseFailAlloc_1954_, 3, v_l_1869_);
lean_ctor_set(v_reuseFailAlloc_1954_, 4, v_l_1882_);
v___x_1941_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
v_isSharedCheck_1948_ = !lean_is_exclusive(v_l_1869_);
if (v_isSharedCheck_1948_ == 0)
{
lean_object* v_unused_1949_; lean_object* v_unused_1950_; lean_object* v_unused_1951_; lean_object* v_unused_1952_; lean_object* v_unused_1953_; 
v_unused_1949_ = lean_ctor_get(v_l_1869_, 4);
lean_dec(v_unused_1949_);
v_unused_1950_ = lean_ctor_get(v_l_1869_, 3);
lean_dec(v_unused_1950_);
v_unused_1951_ = lean_ctor_get(v_l_1869_, 2);
lean_dec(v_unused_1951_);
v_unused_1952_ = lean_ctor_get(v_l_1869_, 1);
lean_dec(v_unused_1952_);
v_unused_1953_ = lean_ctor_get(v_l_1869_, 0);
lean_dec(v_unused_1953_);
v___x_1943_ = v_l_1869_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_dec(v_l_1869_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 4, v_r_1883_);
lean_ctor_set(v___x_1943_, 3, v___x_1941_);
lean_ctor_set(v___x_1943_, 2, v_v_1881_);
lean_ctor_set(v___x_1943_, 1, v_k_1880_);
lean_ctor_set(v___x_1943_, 0, v___x_1938_);
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1938_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_k_1880_);
lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_v_1881_);
lean_ctor_set(v_reuseFailAlloc_1947_, 3, v___x_1941_);
lean_ctor_set(v_reuseFailAlloc_1947_, 4, v_r_1883_);
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
}
}
}
else
{
lean_object* v_l_1961_; 
v_l_1961_ = lean_ctor_get(v_impl_1876_, 3);
lean_inc(v_l_1961_);
if (lean_obj_tag(v_l_1961_) == 0)
{
lean_object* v_r_1962_; lean_object* v_k_1963_; lean_object* v_v_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1987_; 
v_r_1962_ = lean_ctor_get(v_impl_1876_, 4);
v_k_1963_ = lean_ctor_get(v_impl_1876_, 1);
v_v_1964_ = lean_ctor_get(v_impl_1876_, 2);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_impl_1876_);
if (v_isSharedCheck_1987_ == 0)
{
lean_object* v_unused_1988_; lean_object* v_unused_1989_; 
v_unused_1988_ = lean_ctor_get(v_impl_1876_, 3);
lean_dec(v_unused_1988_);
v_unused_1989_ = lean_ctor_get(v_impl_1876_, 0);
lean_dec(v_unused_1989_);
v___x_1966_ = v_impl_1876_;
v_isShared_1967_ = v_isSharedCheck_1987_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_r_1962_);
lean_inc(v_v_1964_);
lean_inc(v_k_1963_);
lean_dec(v_impl_1876_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1987_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v_k_1968_; lean_object* v_v_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1983_; 
v_k_1968_ = lean_ctor_get(v_l_1961_, 1);
v_v_1969_ = lean_ctor_get(v_l_1961_, 2);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_l_1961_);
if (v_isSharedCheck_1983_ == 0)
{
lean_object* v_unused_1984_; lean_object* v_unused_1985_; lean_object* v_unused_1986_; 
v_unused_1984_ = lean_ctor_get(v_l_1961_, 4);
lean_dec(v_unused_1984_);
v_unused_1985_ = lean_ctor_get(v_l_1961_, 3);
lean_dec(v_unused_1985_);
v_unused_1986_ = lean_ctor_get(v_l_1961_, 0);
lean_dec(v_unused_1986_);
v___x_1971_ = v_l_1961_;
v_isShared_1972_ = v_isSharedCheck_1983_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_v_1969_);
lean_inc(v_k_1968_);
lean_dec(v_l_1961_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1983_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1973_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1962_, 2);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 4, v_r_1962_);
lean_ctor_set(v___x_1971_, 3, v_r_1962_);
lean_ctor_set(v___x_1971_, 2, v_v_1868_);
lean_ctor_set(v___x_1971_, 1, v_k_1867_);
lean_ctor_set(v___x_1971_, 0, v___x_1877_);
v___x_1975_ = v___x_1971_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_k_1867_);
lean_ctor_set(v_reuseFailAlloc_1982_, 2, v_v_1868_);
lean_ctor_set(v_reuseFailAlloc_1982_, 3, v_r_1962_);
lean_ctor_set(v_reuseFailAlloc_1982_, 4, v_r_1962_);
v___x_1975_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1977_; 
lean_inc(v_r_1962_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 3, v_r_1962_);
lean_ctor_set(v___x_1966_, 0, v___x_1877_);
v___x_1977_ = v___x_1966_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_k_1963_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_v_1964_);
lean_ctor_set(v_reuseFailAlloc_1981_, 3, v_r_1962_);
lean_ctor_set(v_reuseFailAlloc_1981_, 4, v_r_1962_);
v___x_1977_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
lean_object* v___x_1979_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 4, v___x_1977_);
lean_ctor_set(v___x_1872_, 3, v___x_1975_);
lean_ctor_set(v___x_1872_, 2, v_v_1969_);
lean_ctor_set(v___x_1872_, 1, v_k_1968_);
lean_ctor_set(v___x_1872_, 0, v___x_1973_);
v___x_1979_ = v___x_1872_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_k_1968_);
lean_ctor_set(v_reuseFailAlloc_1980_, 2, v_v_1969_);
lean_ctor_set(v_reuseFailAlloc_1980_, 3, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_1980_, 4, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
}
else
{
lean_object* v_r_1990_; 
v_r_1990_ = lean_ctor_get(v_impl_1876_, 4);
lean_inc(v_r_1990_);
if (lean_obj_tag(v_r_1990_) == 0)
{
lean_object* v_k_1991_; lean_object* v_v_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2003_; 
v_k_1991_ = lean_ctor_get(v_impl_1876_, 1);
v_v_1992_ = lean_ctor_get(v_impl_1876_, 2);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_impl_1876_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; lean_object* v_unused_2005_; lean_object* v_unused_2006_; 
v_unused_2004_ = lean_ctor_get(v_impl_1876_, 4);
lean_dec(v_unused_2004_);
v_unused_2005_ = lean_ctor_get(v_impl_1876_, 3);
lean_dec(v_unused_2005_);
v_unused_2006_ = lean_ctor_get(v_impl_1876_, 0);
lean_dec(v_unused_2006_);
v___x_1994_ = v_impl_1876_;
v_isShared_1995_ = v_isSharedCheck_2003_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_v_1992_);
lean_inc(v_k_1991_);
lean_dec(v_impl_1876_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2003_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1996_ = lean_unsigned_to_nat(3u);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 4, v_l_1961_);
lean_ctor_set(v___x_1994_, 2, v_v_1868_);
lean_ctor_set(v___x_1994_, 1, v_k_1867_);
lean_ctor_set(v___x_1994_, 0, v___x_1877_);
v___x_1998_ = v___x_1994_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_k_1867_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v_v_1868_);
lean_ctor_set(v_reuseFailAlloc_2002_, 3, v_l_1961_);
lean_ctor_set(v_reuseFailAlloc_2002_, 4, v_l_1961_);
v___x_1998_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
lean_object* v___x_2000_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 4, v_r_1990_);
lean_ctor_set(v___x_1872_, 3, v___x_1998_);
lean_ctor_set(v___x_1872_, 2, v_v_1992_);
lean_ctor_set(v___x_1872_, 1, v_k_1991_);
lean_ctor_set(v___x_1872_, 0, v___x_1996_);
v___x_2000_ = v___x_1872_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1996_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_k_1991_);
lean_ctor_set(v_reuseFailAlloc_2001_, 2, v_v_1992_);
lean_ctor_set(v_reuseFailAlloc_2001_, 3, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2001_, 4, v_r_1990_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2007_ = lean_unsigned_to_nat(2u);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 4, v_impl_1876_);
lean_ctor_set(v___x_1872_, 3, v_r_1990_);
lean_ctor_set(v___x_1872_, 0, v___x_2007_);
v___x_2009_ = v___x_1872_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_k_1867_);
lean_ctor_set(v_reuseFailAlloc_2010_, 2, v_v_1868_);
lean_ctor_set(v_reuseFailAlloc_2010_, 3, v_r_1990_);
lean_ctor_set(v_reuseFailAlloc_2010_, 4, v_impl_1876_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
else
{
lean_object* v___x_2012_; 
lean_dec(v_v_1868_);
lean_dec(v_k_1867_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 2, v_v_1864_);
lean_ctor_set(v___x_1872_, 1, v_k_1863_);
v___x_2012_ = v___x_1872_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_size_1866_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_k_1863_);
lean_ctor_set(v_reuseFailAlloc_2013_, 2, v_v_1864_);
lean_ctor_set(v_reuseFailAlloc_2013_, 3, v_l_1869_);
lean_ctor_set(v_reuseFailAlloc_2013_, 4, v_r_1870_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
else
{
lean_object* v_impl_2014_; lean_object* v___x_2015_; 
lean_dec(v_size_1866_);
v_impl_2014_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_1863_, v_v_1864_, v_l_1869_);
v___x_2015_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1870_) == 0)
{
lean_object* v_size_2016_; lean_object* v_size_2017_; lean_object* v_k_2018_; lean_object* v_v_2019_; lean_object* v_l_2020_; lean_object* v_r_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v_size_2016_ = lean_ctor_get(v_r_1870_, 0);
v_size_2017_ = lean_ctor_get(v_impl_2014_, 0);
lean_inc(v_size_2017_);
v_k_2018_ = lean_ctor_get(v_impl_2014_, 1);
lean_inc(v_k_2018_);
v_v_2019_ = lean_ctor_get(v_impl_2014_, 2);
lean_inc(v_v_2019_);
v_l_2020_ = lean_ctor_get(v_impl_2014_, 3);
lean_inc(v_l_2020_);
v_r_2021_ = lean_ctor_get(v_impl_2014_, 4);
lean_inc(v_r_2021_);
v___x_2022_ = lean_unsigned_to_nat(3u);
v___x_2023_ = lean_nat_mul(v___x_2022_, v_size_2016_);
v___x_2024_ = lean_nat_dec_lt(v___x_2023_, v_size_2017_);
lean_dec(v___x_2023_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
lean_dec(v_r_2021_);
lean_dec(v_l_2020_);
lean_dec(v_v_2019_);
lean_dec(v_k_2018_);
v___x_2025_ = lean_nat_add(v___x_2015_, v_size_2017_);
lean_dec(v_size_2017_);
v___x_2026_ = lean_nat_add(v___x_2025_, v_size_2016_);
lean_dec(v___x_2025_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 3, v_impl_2014_);
lean_ctor_set(v___x_1872_, 0, v___x_2026_);
v___x_2028_ = v___x_1872_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_k_1867_);
lean_ctor_set(v_reuseFailAlloc_2029_, 2, v_v_1868_);
lean_ctor_set(v_reuseFailAlloc_2029_, 3, v_impl_2014_);
lean_ctor_set(v_reuseFailAlloc_2029_, 4, v_r_1870_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
else
{
lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2095_; 
v_isSharedCheck_2095_ = !lean_is_exclusive(v_impl_2014_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; lean_object* v_unused_2097_; lean_object* v_unused_2098_; lean_object* v_unused_2099_; lean_object* v_unused_2100_; 
v_unused_2096_ = lean_ctor_get(v_impl_2014_, 4);
lean_dec(v_unused_2096_);
v_unused_2097_ = lean_ctor_get(v_impl_2014_, 3);
lean_dec(v_unused_2097_);
v_unused_2098_ = lean_ctor_get(v_impl_2014_, 2);
lean_dec(v_unused_2098_);
v_unused_2099_ = lean_ctor_get(v_impl_2014_, 1);
lean_dec(v_unused_2099_);
v_unused_2100_ = lean_ctor_get(v_impl_2014_, 0);
lean_dec(v_unused_2100_);
v___x_2031_ = v_impl_2014_;
v_isShared_2032_ = v_isSharedCheck_2095_;
goto v_resetjp_2030_;
}
else
{
lean_dec(v_impl_2014_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2095_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v_size_2033_; lean_object* v_size_2034_; lean_object* v_k_2035_; lean_object* v_v_2036_; lean_object* v_l_2037_; lean_object* v_r_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; 
v_size_2033_ = lean_ctor_get(v_l_2020_, 0);
v_size_2034_ = lean_ctor_get(v_r_2021_, 0);
v_k_2035_ = lean_ctor_get(v_r_2021_, 1);
v_v_2036_ = lean_ctor_get(v_r_2021_, 2);
v_l_2037_ = lean_ctor_get(v_r_2021_, 3);
v_r_2038_ = lean_ctor_get(v_r_2021_, 4);
v___x_2039_ = lean_unsigned_to_nat(2u);
v___x_2040_ = lean_nat_mul(v___x_2039_, v_size_2033_);
v___x_2041_ = lean_nat_dec_lt(v_size_2034_, v___x_2040_);
lean_dec(v___x_2040_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2070_; 
lean_inc(v_r_2038_);
lean_inc(v_l_2037_);
lean_inc(v_v_2036_);
lean_inc(v_k_2035_);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_r_2021_);
if (v_isSharedCheck_2070_ == 0)
{
lean_object* v_unused_2071_; lean_object* v_unused_2072_; lean_object* v_unused_2073_; lean_object* v_unused_2074_; lean_object* v_unused_2075_; 
v_unused_2071_ = lean_ctor_get(v_r_2021_, 4);
lean_dec(v_unused_2071_);
v_unused_2072_ = lean_ctor_get(v_r_2021_, 3);
lean_dec(v_unused_2072_);
v_unused_2073_ = lean_ctor_get(v_r_2021_, 2);
lean_dec(v_unused_2073_);
v_unused_2074_ = lean_ctor_get(v_r_2021_, 1);
lean_dec(v_unused_2074_);
v_unused_2075_ = lean_ctor_get(v_r_2021_, 0);
lean_dec(v_unused_2075_);
v___x_2043_ = v_r_2021_;
v_isShared_2044_ = v_isSharedCheck_2070_;
goto v_resetjp_2042_;
}
else
{
lean_dec(v_r_2021_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2070_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___x_2058_; lean_object* v___y_2060_; 
v___x_2045_ = lean_nat_add(v___x_2015_, v_size_2017_);
lean_dec(v_size_2017_);
v___x_2046_ = lean_nat_add(v___x_2045_, v_size_2016_);
lean_dec(v___x_2045_);
v___x_2058_ = lean_nat_add(v___x_2015_, v_size_2033_);
if (lean_obj_tag(v_l_2037_) == 0)
{
lean_object* v_size_2068_; 
v_size_2068_ = lean_ctor_get(v_l_2037_, 0);
lean_inc(v_size_2068_);
v___y_2060_ = v_size_2068_;
goto v___jp_2059_;
}
else
{
lean_object* v___x_2069_; 
v___x_2069_ = lean_unsigned_to_nat(0u);
v___y_2060_ = v___x_2069_;
goto v___jp_2059_;
}
v___jp_2047_:
{
lean_object* v___x_2051_; lean_object* v___x_2053_; 
v___x_2051_ = lean_nat_add(v___y_2048_, v___y_2050_);
lean_dec(v___y_2050_);
lean_dec(v___y_2048_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 4, v_r_1870_);
lean_ctor_set(v___x_2043_, 3, v_r_2038_);
lean_ctor_set(v___x_2043_, 2, v_v_1868_);
lean_ctor_set(v___x_2043_, 1, v_k_1867_);
lean_ctor_set(v___x_2043_, 0, v___x_2051_);
v___x_2053_ = v___x_2043_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2051_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_k_1867_);
lean_ctor_set(v_reuseFailAlloc_2057_, 2, v_v_1868_);
lean_ctor_set(v_reuseFailAlloc_2057_, 3, v_r_2038_);
lean_ctor_set(v_reuseFailAlloc_2057_, 4, v_r_1870_);
v___x_2053_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2055_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 4, v___x_2053_);
lean_ctor_set(v___x_2031_, 3, v___y_2049_);
lean_ctor_set(v___x_2031_, 2, v_v_2036_);
lean_ctor_set(v___x_2031_, 1, v_k_2035_);
lean_ctor_set(v___x_2031_, 0, v___x_2046_);
v___x_2055_ = v___x_2031_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_k_2035_);
lean_ctor_set(v_reuseFailAlloc_2056_, 2, v_v_2036_);
lean_ctor_set(v_reuseFailAlloc_2056_, 3, v___y_2049_);
lean_ctor_set(v_reuseFailAlloc_2056_, 4, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
v___jp_2059_:
{
lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2061_ = lean_nat_add(v___x_2058_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec(v___x_2058_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 4, v_l_2037_);
lean_ctor_set(v___x_1872_, 3, v_l_2020_);
lean_ctor_set(v___x_1872_, 2, v_v_2019_);
lean_ctor_set(v___x_1872_, 1, v_k_2018_);
lean_ctor_set(v___x_1872_, 0, v___x_2061_);
v___x_2063_ = v___x_1872_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2061_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_k_2018_);
lean_ctor_set(v_reuseFailAlloc_2067_, 2, v_v_2019_);
lean_ctor_set(v_reuseFailAlloc_2067_, 3, v_l_2020_);
lean_ctor_set(v_reuseFailAlloc_2067_, 4, v_l_2037_);
v___x_2063_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_nat_add(v___x_2015_, v_size_2016_);
if (lean_obj_tag(v_r_2038_) == 0)
{
lean_object* v_size_2065_; 
v_size_2065_ = lean_ctor_get(v_r_2038_, 0);
lean_inc(v_size_2065_);
v___y_2048_ = v___x_2064_;
v___y_2049_ = v___x_2063_;
v___y_2050_ = v_size_2065_;
goto v___jp_2047_;
}
else
{
lean_object* v___x_2066_; 
v___x_2066_ = lean_unsigned_to_nat(0u);
v___y_2048_ = v___x_2064_;
v___y_2049_ = v___x_2063_;
v___y_2050_ = v___x_2066_;
goto v___jp_2047_;
}
}
}
}
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2081_; 
lean_del_object(v___x_1872_);
v___x_2076_ = lean_nat_add(v___x_2015_, v_size_2017_);
lean_dec(v_size_2017_);
v___x_2077_ = lean_nat_add(v___x_2076_, v_size_2016_);
lean_dec(v___x_2076_);
v___x_2078_ = lean_nat_add(v___x_2015_, v_size_2016_);
v___x_2079_ = lean_nat_add(v___x_2078_, v_size_2034_);
lean_dec(v___x_2078_);
lean_inc_ref(v_r_1870_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 4, v_r_1870_);
lean_ctor_set(v___x_2031_, 3, v_r_2021_);
lean_ctor_set(v___x_2031_, 2, v_v_1868_);
lean_ctor_set(v___x_2031_, 1, v_k_1867_);
lean_ctor_set(v___x_2031_, 0, v___x_2079_);
v___x_2081_ = v___x_2031_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2079_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_k_1867_);
lean_ctor_set(v_reuseFailAlloc_2094_, 2, v_v_1868_);
lean_ctor_set(v_reuseFailAlloc_2094_, 3, v_r_2021_);
lean_ctor_set(v_reuseFailAlloc_2094_, 4, v_r_1870_);
v___x_2081_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
v_isSharedCheck_2088_ = !lean_is_exclusive(v_r_1870_);
if (v_isSharedCheck_2088_ == 0)
{
lean_object* v_unused_2089_; lean_object* v_unused_2090_; lean_object* v_unused_2091_; lean_object* v_unused_2092_; lean_object* v_unused_2093_; 
v_unused_2089_ = lean_ctor_get(v_r_1870_, 4);
lean_dec(v_unused_2089_);
v_unused_2090_ = lean_ctor_get(v_r_1870_, 3);
lean_dec(v_unused_2090_);
v_unused_2091_ = lean_ctor_get(v_r_1870_, 2);
lean_dec(v_unused_2091_);
v_unused_2092_ = lean_ctor_get(v_r_1870_, 1);
lean_dec(v_unused_2092_);
v_unused_2093_ = lean_ctor_get(v_r_1870_, 0);
lean_dec(v_unused_2093_);
v___x_2083_ = v_r_1870_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_dec(v_r_1870_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 4, v___x_2081_);
lean_ctor_set(v___x_2083_, 3, v_l_2020_);
lean_ctor_set(v___x_2083_, 2, v_v_2019_);
lean_ctor_set(v___x_2083_, 1, v_k_2018_);
lean_ctor_set(v___x_2083_, 0, v___x_2077_);
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_k_2018_);
lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_v_2019_);
lean_ctor_set(v_reuseFailAlloc_2087_, 3, v_l_2020_);
lean_ctor_set(v_reuseFailAlloc_2087_, 4, v___x_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2101_; 
v_l_2101_ = lean_ctor_get(v_impl_2014_, 3);
lean_inc(v_l_2101_);
if (lean_obj_tag(v_l_2101_) == 0)
{
lean_object* v_r_2102_; lean_object* v_k_2103_; lean_object* v_v_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2115_; 
v_r_2102_ = lean_ctor_get(v_impl_2014_, 4);
v_k_2103_ = lean_ctor_get(v_impl_2014_, 1);
v_v_2104_ = lean_ctor_get(v_impl_2014_, 2);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_impl_2014_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; lean_object* v_unused_2117_; 
v_unused_2116_ = lean_ctor_get(v_impl_2014_, 3);
lean_dec(v_unused_2116_);
v_unused_2117_ = lean_ctor_get(v_impl_2014_, 0);
lean_dec(v_unused_2117_);
v___x_2106_ = v_impl_2014_;
v_isShared_2107_ = v_isSharedCheck_2115_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_r_2102_);
lean_inc(v_v_2104_);
lean_inc(v_k_2103_);
lean_dec(v_impl_2014_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2115_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
v___x_2108_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2102_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 3, v_r_2102_);
lean_ctor_set(v___x_2106_, 2, v_v_1868_);
lean_ctor_set(v___x_2106_, 1, v_k_1867_);
lean_ctor_set(v___x_2106_, 0, v___x_2015_);
v___x_2110_ = v___x_2106_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2015_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_k_1867_);
lean_ctor_set(v_reuseFailAlloc_2114_, 2, v_v_1868_);
lean_ctor_set(v_reuseFailAlloc_2114_, 3, v_r_2102_);
lean_ctor_set(v_reuseFailAlloc_2114_, 4, v_r_2102_);
v___x_2110_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2112_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 4, v___x_2110_);
lean_ctor_set(v___x_1872_, 3, v_l_2101_);
lean_ctor_set(v___x_1872_, 2, v_v_2104_);
lean_ctor_set(v___x_1872_, 1, v_k_2103_);
lean_ctor_set(v___x_1872_, 0, v___x_2108_);
v___x_2112_ = v___x_1872_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2108_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_k_2103_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_v_2104_);
lean_ctor_set(v_reuseFailAlloc_2113_, 3, v_l_2101_);
lean_ctor_set(v_reuseFailAlloc_2113_, 4, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
lean_object* v_r_2118_; 
v_r_2118_ = lean_ctor_get(v_impl_2014_, 4);
lean_inc(v_r_2118_);
if (lean_obj_tag(v_r_2118_) == 0)
{
lean_object* v_k_2119_; lean_object* v_v_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2143_; 
v_k_2119_ = lean_ctor_get(v_impl_2014_, 1);
v_v_2120_ = lean_ctor_get(v_impl_2014_, 2);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_impl_2014_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; lean_object* v_unused_2145_; lean_object* v_unused_2146_; 
v_unused_2144_ = lean_ctor_get(v_impl_2014_, 4);
lean_dec(v_unused_2144_);
v_unused_2145_ = lean_ctor_get(v_impl_2014_, 3);
lean_dec(v_unused_2145_);
v_unused_2146_ = lean_ctor_get(v_impl_2014_, 0);
lean_dec(v_unused_2146_);
v___x_2122_ = v_impl_2014_;
v_isShared_2123_ = v_isSharedCheck_2143_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_v_2120_);
lean_inc(v_k_2119_);
lean_dec(v_impl_2014_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2143_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v_k_2124_; lean_object* v_v_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2139_; 
v_k_2124_ = lean_ctor_get(v_r_2118_, 1);
v_v_2125_ = lean_ctor_get(v_r_2118_, 2);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_r_2118_);
if (v_isSharedCheck_2139_ == 0)
{
lean_object* v_unused_2140_; lean_object* v_unused_2141_; lean_object* v_unused_2142_; 
v_unused_2140_ = lean_ctor_get(v_r_2118_, 4);
lean_dec(v_unused_2140_);
v_unused_2141_ = lean_ctor_get(v_r_2118_, 3);
lean_dec(v_unused_2141_);
v_unused_2142_ = lean_ctor_get(v_r_2118_, 0);
lean_dec(v_unused_2142_);
v___x_2127_ = v_r_2118_;
v_isShared_2128_ = v_isSharedCheck_2139_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_v_2125_);
lean_inc(v_k_2124_);
lean_dec(v_r_2118_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2139_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2129_ = lean_unsigned_to_nat(3u);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 4, v_l_2101_);
lean_ctor_set(v___x_2127_, 3, v_l_2101_);
lean_ctor_set(v___x_2127_, 2, v_v_2120_);
lean_ctor_set(v___x_2127_, 1, v_k_2119_);
lean_ctor_set(v___x_2127_, 0, v___x_2015_);
v___x_2131_ = v___x_2127_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2015_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_k_2119_);
lean_ctor_set(v_reuseFailAlloc_2138_, 2, v_v_2120_);
lean_ctor_set(v_reuseFailAlloc_2138_, 3, v_l_2101_);
lean_ctor_set(v_reuseFailAlloc_2138_, 4, v_l_2101_);
v___x_2131_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2133_; 
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 4, v_l_2101_);
lean_ctor_set(v___x_2122_, 2, v_v_1868_);
lean_ctor_set(v___x_2122_, 1, v_k_1867_);
lean_ctor_set(v___x_2122_, 0, v___x_2015_);
v___x_2133_ = v___x_2122_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2015_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_k_1867_);
lean_ctor_set(v_reuseFailAlloc_2137_, 2, v_v_1868_);
lean_ctor_set(v_reuseFailAlloc_2137_, 3, v_l_2101_);
lean_ctor_set(v_reuseFailAlloc_2137_, 4, v_l_2101_);
v___x_2133_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2135_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 4, v___x_2133_);
lean_ctor_set(v___x_1872_, 3, v___x_2131_);
lean_ctor_set(v___x_1872_, 2, v_v_2125_);
lean_ctor_set(v___x_1872_, 1, v_k_2124_);
lean_ctor_set(v___x_1872_, 0, v___x_2129_);
v___x_2135_ = v___x_1872_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2129_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_k_2124_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_v_2125_);
lean_ctor_set(v_reuseFailAlloc_2136_, 3, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2136_, 4, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2149_; 
v___x_2147_ = lean_unsigned_to_nat(2u);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 4, v_r_2118_);
lean_ctor_set(v___x_1872_, 3, v_impl_2014_);
lean_ctor_set(v___x_1872_, 0, v___x_2147_);
v___x_2149_ = v___x_1872_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v_k_1867_);
lean_ctor_set(v_reuseFailAlloc_2150_, 2, v_v_1868_);
lean_ctor_set(v_reuseFailAlloc_2150_, 3, v_impl_2014_);
lean_ctor_set(v_reuseFailAlloc_2150_, 4, v_r_2118_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = lean_unsigned_to_nat(1u);
v___x_2153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
lean_ctor_set(v___x_2153_, 1, v_k_1863_);
lean_ctor_set(v___x_2153_, 2, v_v_1864_);
lean_ctor_set(v___x_2153_, 3, v_t_1865_);
lean_ctor_set(v___x_2153_, 4, v_t_1865_);
return v___x_2153_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(lean_object* v_k_2154_, lean_object* v_t_2155_){
_start:
{
if (lean_obj_tag(v_t_2155_) == 0)
{
lean_object* v_k_2156_; lean_object* v_l_2157_; lean_object* v_r_2158_; uint8_t v___x_2159_; 
v_k_2156_ = lean_ctor_get(v_t_2155_, 1);
v_l_2157_ = lean_ctor_get(v_t_2155_, 3);
v_r_2158_ = lean_ctor_get(v_t_2155_, 4);
v___x_2159_ = lean_nat_dec_lt(v_k_2154_, v_k_2156_);
if (v___x_2159_ == 0)
{
uint8_t v___x_2160_; 
v___x_2160_ = lean_nat_dec_eq(v_k_2154_, v_k_2156_);
if (v___x_2160_ == 0)
{
v_t_2155_ = v_r_2158_;
goto _start;
}
else
{
return v___x_2160_;
}
}
else
{
v_t_2155_ = v_l_2157_;
goto _start;
}
}
else
{
uint8_t v___x_2163_; 
v___x_2163_ = 0;
return v___x_2163_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg___boxed(lean_object* v_k_2164_, lean_object* v_t_2165_){
_start:
{
uint8_t v_res_2166_; lean_object* v_r_2167_; 
v_res_2166_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2164_, v_t_2165_);
lean_dec(v_t_2165_);
lean_dec(v_k_2164_);
v_r_2167_ = lean_box(v_res_2166_);
return v_r_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___redArg(lean_object* v_y_2168_, lean_object* v_x_2169_, size_t v_x_2170_, size_t v_x_2171_){
_start:
{
if (lean_obj_tag(v_x_2169_) == 0)
{
lean_object* v_cs_2172_; size_t v_j_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v_cs_2172_ = lean_ctor_get(v_x_2169_, 0);
v_j_2173_ = lean_usize_shift_right(v_x_2170_, v_x_2171_);
v___x_2174_ = lean_usize_to_nat(v_j_2173_);
v___x_2175_ = lean_array_get_size(v_cs_2172_);
v___x_2176_ = lean_nat_dec_lt(v___x_2174_, v___x_2175_);
if (v___x_2176_ == 0)
{
lean_dec(v___x_2174_);
lean_dec(v_y_2168_);
return v_x_2169_;
}
else
{
lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2194_; 
lean_inc_ref(v_cs_2172_);
v_isSharedCheck_2194_ = !lean_is_exclusive(v_x_2169_);
if (v_isSharedCheck_2194_ == 0)
{
lean_object* v_unused_2195_; 
v_unused_2195_ = lean_ctor_get(v_x_2169_, 0);
lean_dec(v_unused_2195_);
v___x_2178_ = v_x_2169_;
v_isShared_2179_ = v_isSharedCheck_2194_;
goto v_resetjp_2177_;
}
else
{
lean_dec(v_x_2169_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2194_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
size_t v___x_2180_; size_t v___x_2181_; size_t v___x_2182_; size_t v_i_2183_; size_t v___x_2184_; size_t v_shift_2185_; lean_object* v_v_2186_; lean_object* v___x_2187_; lean_object* v_xs_x27_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2180_ = ((size_t)1ULL);
v___x_2181_ = lean_usize_shift_left(v___x_2180_, v_x_2171_);
v___x_2182_ = lean_usize_sub(v___x_2181_, v___x_2180_);
v_i_2183_ = lean_usize_land(v_x_2170_, v___x_2182_);
v___x_2184_ = ((size_t)5ULL);
v_shift_2185_ = lean_usize_sub(v_x_2171_, v___x_2184_);
v_v_2186_ = lean_array_fget(v_cs_2172_, v___x_2174_);
v___x_2187_ = lean_box(0);
v_xs_x27_2188_ = lean_array_fset(v_cs_2172_, v___x_2174_, v___x_2187_);
v___x_2189_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___redArg(v_y_2168_, v_v_2186_, v_i_2183_, v_shift_2185_);
v___x_2190_ = lean_array_fset(v_xs_x27_2188_, v___x_2174_, v___x_2189_);
lean_dec(v___x_2174_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___x_2190_);
v___x_2192_ = v___x_2178_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
else
{
lean_object* v_vs_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
v_vs_2196_ = lean_ctor_get(v_x_2169_, 0);
v___x_2197_ = lean_usize_to_nat(v_x_2170_);
v___x_2198_ = lean_array_get_size(v_vs_2196_);
v___x_2199_ = lean_nat_dec_lt(v___x_2197_, v___x_2198_);
if (v___x_2199_ == 0)
{
lean_dec(v___x_2197_);
lean_dec(v_y_2168_);
return v_x_2169_;
}
else
{
lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2214_; 
lean_inc_ref(v_vs_2196_);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_x_2169_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; 
v_unused_2215_ = lean_ctor_get(v_x_2169_, 0);
lean_dec(v_unused_2215_);
v___x_2201_ = v_x_2169_;
v_isShared_2202_ = v_isSharedCheck_2214_;
goto v_resetjp_2200_;
}
else
{
lean_dec(v_x_2169_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2214_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v_v_2203_; lean_object* v___x_2204_; lean_object* v_xs_x27_2205_; lean_object* v___y_2207_; uint8_t v___x_2212_; 
v_v_2203_ = lean_array_fget(v_vs_2196_, v___x_2197_);
v___x_2204_ = lean_box(0);
v_xs_x27_2205_ = lean_array_fset(v_vs_2196_, v___x_2197_, v___x_2204_);
v___x_2212_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2168_, v_v_2203_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2168_, v___x_2204_, v_v_2203_);
v___y_2207_ = v___x_2213_;
goto v___jp_2206_;
}
else
{
lean_dec(v_y_2168_);
v___y_2207_ = v_v_2203_;
goto v___jp_2206_;
}
v___jp_2206_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = lean_array_fset(v_xs_x27_2205_, v___x_2197_, v___y_2207_);
lean_dec(v___x_2197_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2208_);
v___x_2210_ = v___x_2201_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___redArg___boxed(lean_object* v_y_2216_, lean_object* v_x_2217_, lean_object* v_x_2218_, lean_object* v_x_2219_){
_start:
{
size_t v_x_4619__boxed_2220_; size_t v_x_4620__boxed_2221_; lean_object* v_res_2222_; 
v_x_4619__boxed_2220_ = lean_unbox_usize(v_x_2218_);
lean_dec(v_x_2218_);
v_x_4620__boxed_2221_ = lean_unbox_usize(v_x_2219_);
lean_dec(v_x_2219_);
v_res_2222_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___redArg(v_y_2216_, v_x_2217_, v_x_4619__boxed_2220_, v_x_4620__boxed_2221_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(lean_object* v_y_2223_, lean_object* v_inst_2224_, lean_object* v_t_2225_, lean_object* v_i_2226_){
_start:
{
lean_object* v_root_2227_; lean_object* v_tail_2228_; lean_object* v_size_2229_; size_t v_shift_2230_; lean_object* v_tailOff_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2258_; 
v_root_2227_ = lean_ctor_get(v_t_2225_, 0);
v_tail_2228_ = lean_ctor_get(v_t_2225_, 1);
v_size_2229_ = lean_ctor_get(v_t_2225_, 2);
v_shift_2230_ = lean_ctor_get_usize(v_t_2225_, 4);
v_tailOff_2231_ = lean_ctor_get(v_t_2225_, 3);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_t_2225_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2233_ = v_t_2225_;
v_isShared_2234_ = v_isSharedCheck_2258_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_tailOff_2231_);
lean_inc(v_size_2229_);
lean_inc(v_tail_2228_);
lean_inc(v_root_2227_);
lean_dec(v_t_2225_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2258_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
uint8_t v___x_2235_; 
v___x_2235_ = lean_nat_dec_le(v_tailOff_2231_, v_i_2226_);
if (v___x_2235_ == 0)
{
size_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2236_ = lean_usize_of_nat(v_i_2226_);
v___x_2237_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___redArg(v_y_2223_, v_root_2227_, v___x_2236_, v_shift_2230_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2237_);
v___x_2239_ = v___x_2233_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_tail_2228_);
lean_ctor_set(v_reuseFailAlloc_2240_, 2, v_size_2229_);
lean_ctor_set(v_reuseFailAlloc_2240_, 3, v_tailOff_2231_);
lean_ctor_set_usize(v_reuseFailAlloc_2240_, 4, v_shift_2230_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; uint8_t v___x_2243_; 
v___x_2241_ = lean_nat_sub(v_i_2226_, v_tailOff_2231_);
v___x_2242_ = lean_array_get_size(v_tail_2228_);
v___x_2243_ = lean_nat_dec_lt(v___x_2241_, v___x_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2245_; 
lean_dec(v___x_2241_);
lean_dec(v_y_2223_);
if (v_isShared_2234_ == 0)
{
v___x_2245_ = v___x_2233_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_root_2227_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_tail_2228_);
lean_ctor_set(v_reuseFailAlloc_2246_, 2, v_size_2229_);
lean_ctor_set(v_reuseFailAlloc_2246_, 3, v_tailOff_2231_);
lean_ctor_set_usize(v_reuseFailAlloc_2246_, 4, v_shift_2230_);
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
lean_object* v_v_2247_; lean_object* v___x_2248_; lean_object* v_xs_x27_2249_; lean_object* v___y_2251_; uint8_t v___x_2256_; 
v_v_2247_ = lean_array_fget(v_tail_2228_, v___x_2241_);
v___x_2248_ = lean_box(0);
v_xs_x27_2249_ = lean_array_fset(v_tail_2228_, v___x_2241_, v___x_2248_);
v___x_2256_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2223_, v_v_2247_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_2223_, v___x_2248_, v_v_2247_);
v___y_2251_ = v___x_2257_;
goto v___jp_2250_;
}
else
{
lean_dec(v_y_2223_);
v___y_2251_ = v_v_2247_;
goto v___jp_2250_;
}
v___jp_2250_:
{
lean_object* v___x_2252_; lean_object* v___x_2254_; 
v___x_2252_ = lean_array_fset(v_xs_x27_2249_, v___x_2241_, v___y_2251_);
lean_dec(v___x_2241_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 1, v___x_2252_);
v___x_2254_ = v___x_2233_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_root_2227_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v___x_2252_);
lean_ctor_set(v_reuseFailAlloc_2255_, 2, v_size_2229_);
lean_ctor_set(v_reuseFailAlloc_2255_, 3, v_tailOff_2231_);
lean_ctor_set_usize(v_reuseFailAlloc_2255_, 4, v_shift_2230_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2___boxed(lean_object* v_y_2259_, lean_object* v_inst_2260_, lean_object* v_t_2261_, lean_object* v_i_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2259_, v_inst_2260_, v_t_2261_, v_i_2262_);
lean_dec(v_i_2262_);
lean_dec(v_inst_2260_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(lean_object* v_y_2264_, lean_object* v_x_2265_, lean_object* v_s_2266_){
_start:
{
lean_object* v_vars_2267_; lean_object* v_varMap_2268_; lean_object* v_vars_x27_2269_; lean_object* v_varMap_x27_2270_; lean_object* v_natToIntMap_2271_; lean_object* v_natDef_2272_; lean_object* v_dvds_2273_; lean_object* v_lowers_2274_; lean_object* v_uppers_2275_; lean_object* v_diseqs_2276_; lean_object* v_elimEqs_2277_; lean_object* v_elimStack_2278_; lean_object* v_occurs_2279_; lean_object* v_assignment_2280_; lean_object* v_nextCnstrId_2281_; uint8_t v_caseSplits_2282_; lean_object* v_conflict_x3f_2283_; lean_object* v_diseqSplits_2284_; lean_object* v_divMod_2285_; lean_object* v_toIntIds_2286_; lean_object* v_toIntInfos_2287_; lean_object* v_toIntTermMap_2288_; lean_object* v_toIntVarMap_2289_; uint8_t v_usedCommRing_2290_; lean_object* v_nonlinearOccs_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2300_; 
v_vars_2267_ = lean_ctor_get(v_s_2266_, 0);
v_varMap_2268_ = lean_ctor_get(v_s_2266_, 1);
v_vars_x27_2269_ = lean_ctor_get(v_s_2266_, 2);
v_varMap_x27_2270_ = lean_ctor_get(v_s_2266_, 3);
v_natToIntMap_2271_ = lean_ctor_get(v_s_2266_, 4);
v_natDef_2272_ = lean_ctor_get(v_s_2266_, 5);
v_dvds_2273_ = lean_ctor_get(v_s_2266_, 6);
v_lowers_2274_ = lean_ctor_get(v_s_2266_, 7);
v_uppers_2275_ = lean_ctor_get(v_s_2266_, 8);
v_diseqs_2276_ = lean_ctor_get(v_s_2266_, 9);
v_elimEqs_2277_ = lean_ctor_get(v_s_2266_, 10);
v_elimStack_2278_ = lean_ctor_get(v_s_2266_, 11);
v_occurs_2279_ = lean_ctor_get(v_s_2266_, 12);
v_assignment_2280_ = lean_ctor_get(v_s_2266_, 13);
v_nextCnstrId_2281_ = lean_ctor_get(v_s_2266_, 14);
v_caseSplits_2282_ = lean_ctor_get_uint8(v_s_2266_, sizeof(void*)*23);
v_conflict_x3f_2283_ = lean_ctor_get(v_s_2266_, 15);
v_diseqSplits_2284_ = lean_ctor_get(v_s_2266_, 16);
v_divMod_2285_ = lean_ctor_get(v_s_2266_, 17);
v_toIntIds_2286_ = lean_ctor_get(v_s_2266_, 18);
v_toIntInfos_2287_ = lean_ctor_get(v_s_2266_, 19);
v_toIntTermMap_2288_ = lean_ctor_get(v_s_2266_, 20);
v_toIntVarMap_2289_ = lean_ctor_get(v_s_2266_, 21);
v_usedCommRing_2290_ = lean_ctor_get_uint8(v_s_2266_, sizeof(void*)*23 + 1);
v_nonlinearOccs_2291_ = lean_ctor_get(v_s_2266_, 22);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_s_2266_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2293_ = v_s_2266_;
v_isShared_2294_ = v_isSharedCheck_2300_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_nonlinearOccs_2291_);
lean_inc(v_toIntVarMap_2289_);
lean_inc(v_toIntTermMap_2288_);
lean_inc(v_toIntInfos_2287_);
lean_inc(v_toIntIds_2286_);
lean_inc(v_divMod_2285_);
lean_inc(v_diseqSplits_2284_);
lean_inc(v_conflict_x3f_2283_);
lean_inc(v_nextCnstrId_2281_);
lean_inc(v_assignment_2280_);
lean_inc(v_occurs_2279_);
lean_inc(v_elimStack_2278_);
lean_inc(v_elimEqs_2277_);
lean_inc(v_diseqs_2276_);
lean_inc(v_uppers_2275_);
lean_inc(v_lowers_2274_);
lean_inc(v_dvds_2273_);
lean_inc(v_natDef_2272_);
lean_inc(v_natToIntMap_2271_);
lean_inc(v_varMap_x27_2270_);
lean_inc(v_vars_x27_2269_);
lean_inc(v_varMap_2268_);
lean_inc(v_vars_2267_);
lean_dec(v_s_2266_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2300_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2298_; 
v___x_2295_ = lean_box(1);
v___x_2296_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_2264_, v___x_2295_, v_occurs_2279_, v_x_2265_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 12, v___x_2296_);
v___x_2298_ = v___x_2293_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_vars_2267_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_varMap_2268_);
lean_ctor_set(v_reuseFailAlloc_2299_, 2, v_vars_x27_2269_);
lean_ctor_set(v_reuseFailAlloc_2299_, 3, v_varMap_x27_2270_);
lean_ctor_set(v_reuseFailAlloc_2299_, 4, v_natToIntMap_2271_);
lean_ctor_set(v_reuseFailAlloc_2299_, 5, v_natDef_2272_);
lean_ctor_set(v_reuseFailAlloc_2299_, 6, v_dvds_2273_);
lean_ctor_set(v_reuseFailAlloc_2299_, 7, v_lowers_2274_);
lean_ctor_set(v_reuseFailAlloc_2299_, 8, v_uppers_2275_);
lean_ctor_set(v_reuseFailAlloc_2299_, 9, v_diseqs_2276_);
lean_ctor_set(v_reuseFailAlloc_2299_, 10, v_elimEqs_2277_);
lean_ctor_set(v_reuseFailAlloc_2299_, 11, v_elimStack_2278_);
lean_ctor_set(v_reuseFailAlloc_2299_, 12, v___x_2296_);
lean_ctor_set(v_reuseFailAlloc_2299_, 13, v_assignment_2280_);
lean_ctor_set(v_reuseFailAlloc_2299_, 14, v_nextCnstrId_2281_);
lean_ctor_set(v_reuseFailAlloc_2299_, 15, v_conflict_x3f_2283_);
lean_ctor_set(v_reuseFailAlloc_2299_, 16, v_diseqSplits_2284_);
lean_ctor_set(v_reuseFailAlloc_2299_, 17, v_divMod_2285_);
lean_ctor_set(v_reuseFailAlloc_2299_, 18, v_toIntIds_2286_);
lean_ctor_set(v_reuseFailAlloc_2299_, 19, v_toIntInfos_2287_);
lean_ctor_set(v_reuseFailAlloc_2299_, 20, v_toIntTermMap_2288_);
lean_ctor_set(v_reuseFailAlloc_2299_, 21, v_toIntVarMap_2289_);
lean_ctor_set(v_reuseFailAlloc_2299_, 22, v_nonlinearOccs_2291_);
lean_ctor_set_uint8(v_reuseFailAlloc_2299_, sizeof(void*)*23, v_caseSplits_2282_);
lean_ctor_set_uint8(v_reuseFailAlloc_2299_, sizeof(void*)*23 + 1, v_usedCommRing_2290_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed(lean_object* v_y_2301_, lean_object* v_x_2302_, lean_object* v_s_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(v_y_2301_, v_x_2302_, v_s_2303_);
lean_dec(v_x_2302_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(lean_object* v_x_2305_, lean_object* v_y_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_2305_, v_a_2307_, v_a_2308_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2323_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2313_ = v___x_2310_;
v_isShared_2314_ = v_isSharedCheck_2323_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2323_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
uint8_t v___x_2315_; 
v___x_2315_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_2306_, v_a_2311_);
lean_dec(v_a_2311_);
if (v___x_2315_ == 0)
{
lean_object* v___f_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_del_object(v___x_2313_);
v___f_2316_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2316_, 0, v_y_2306_);
lean_closure_set(v___f_2316_, 1, v_x_2305_);
v___x_2317_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2318_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2317_, v___f_2316_, v_a_2307_);
return v___x_2318_;
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2321_; 
lean_dec(v_y_2306_);
lean_dec(v_x_2305_);
v___x_2319_ = lean_box(0);
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 0, v___x_2319_);
v___x_2321_ = v___x_2313_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec(v_y_2306_);
lean_dec(v_x_2305_);
v_a_2324_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2310_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2310_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___boxed(lean_object* v_x_2332_, lean_object* v_y_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2332_, v_y_2333_, v_a_2334_, v_a_2335_);
lean_dec_ref(v_a_2335_);
lean_dec(v_a_2334_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc(lean_object* v_x_2338_, lean_object* v_y_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v___x_2351_; 
v___x_2351_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_2338_, v_y_2339_, v_a_2340_, v_a_2348_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addOcc___boxed(lean_object* v_x_2352_, lean_object* v_y_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc(v_x_2352_, v_y_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
lean_dec(v_a_2361_);
lean_dec_ref(v_a_2360_);
lean_dec(v_a_2359_);
lean_dec_ref(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
lean_dec(v_a_2355_);
lean_dec(v_a_2354_);
return v_res_2365_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(lean_object* v_00_u03b2_2366_, lean_object* v_k_2367_, lean_object* v_t_2368_){
_start:
{
uint8_t v___x_2369_; 
v___x_2369_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_2367_, v_t_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2370_, lean_object* v_k_2371_, lean_object* v_t_2372_){
_start:
{
uint8_t v_res_2373_; lean_object* v_r_2374_; 
v_res_2373_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(v_00_u03b2_2370_, v_k_2371_, v_t_2372_);
lean_dec(v_t_2372_);
lean_dec(v_k_2371_);
v_r_2374_ = lean_box(v_res_2373_);
return v_r_2374_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1(lean_object* v_00_u03b2_2375_, lean_object* v_k_2376_, lean_object* v_v_2377_, lean_object* v_t_2378_, lean_object* v_hl_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_2376_, v_v_2377_, v_t_2378_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(lean_object* v_y_2381_, lean_object* v_inst_2382_, lean_object* v_x_2383_, size_t v_x_2384_, size_t v_x_2385_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___redArg(v_y_2381_, v_x_2383_, v_x_2384_, v_x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2387_, lean_object* v_inst_2388_, lean_object* v_x_2389_, lean_object* v_x_2390_, lean_object* v_x_2391_){
_start:
{
size_t v_x_4866__boxed_2392_; size_t v_x_4867__boxed_2393_; lean_object* v_res_2394_; 
v_x_4866__boxed_2392_ = lean_unbox_usize(v_x_2390_);
lean_dec(v_x_2390_);
v_x_4867__boxed_2393_ = lean_unbox_usize(v_x_2391_);
lean_dec(v_x_2391_);
v_res_2394_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_2387_, v_inst_2388_, v_x_2389_, v_x_4866__boxed_2392_, v_x_4867__boxed_2393_);
lean_dec(v_inst_2388_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(lean_object* v_y_2395_, lean_object* v_p_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
if (lean_obj_tag(v_p_2396_) == 1)
{
lean_object* v_v_2400_; lean_object* v_p_2401_; lean_object* v___x_2402_; 
v_v_2400_ = lean_ctor_get(v_p_2396_, 1);
lean_inc(v_v_2400_);
v_p_2401_ = lean_ctor_get(v_p_2396_, 2);
lean_inc_ref(v_p_2401_);
lean_dec_ref(v_p_2396_);
lean_inc(v_y_2395_);
v___x_2402_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_v_2400_, v_y_2395_, v_a_2397_, v_a_2398_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_dec_ref(v___x_2402_);
v_p_2396_ = v_p_2401_;
goto _start;
}
else
{
lean_dec_ref(v_p_2401_);
lean_dec(v_y_2395_);
return v___x_2402_;
}
}
else
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
lean_dec_ref(v_p_2396_);
lean_dec(v_y_2395_);
v___x_2404_ = lean_box(0);
v___x_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
return v___x_2405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg___boxed(lean_object* v_y_2406_, lean_object* v_p_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(v_y_2406_, v_p_2407_, v_a_2408_, v_a_2409_);
lean_dec_ref(v_a_2409_);
lean_dec(v_a_2408_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go(lean_object* v_y_2412_, lean_object* v_p_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(v_y_2412_, v_p_2413_, v_a_2414_, v_a_2422_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___boxed(lean_object* v_y_2426_, lean_object* v_p_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go(v_y_2426_, v_p_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
lean_dec(v_a_2429_);
lean_dec(v_a_2428_);
return v_res_2439_;
}
}
static lean_object* _init_l_Int_Linear_Poly_updateOccs___redArg___closed__1(void){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = ((lean_object*)(l_Int_Linear_Poly_updateOccs___redArg___closed__0));
v___x_2442_ = l_Lean_stringToMessageData(v___x_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_updateOccs___redArg(lean_object* v_p_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
if (lean_obj_tag(v_p_2443_) == 1)
{
lean_object* v_v_2450_; lean_object* v_p_2451_; lean_object* v___x_2452_; 
v_v_2450_ = lean_ctor_get(v_p_2443_, 1);
lean_inc(v_v_2450_);
v_p_2451_ = lean_ctor_get(v_p_2443_, 2);
lean_inc_ref(v_p_2451_);
lean_dec_ref(v_p_2443_);
v___x_2452_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(v_v_2450_, v_p_2451_, v_a_2444_, v_a_2447_);
return v___x_2452_;
}
else
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
lean_dec_ref(v_p_2443_);
v___x_2453_ = lean_obj_once(&l_Int_Linear_Poly_updateOccs___redArg___closed__1, &l_Int_Linear_Poly_updateOccs___redArg___closed__1_once, _init_l_Int_Linear_Poly_updateOccs___redArg___closed__1);
v___x_2454_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_2453_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
return v___x_2454_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_updateOccs___redArg___boxed(lean_object* v_p_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Int_Linear_Poly_updateOccs___redArg(v_p_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_);
lean_dec(v_a_2460_);
lean_dec_ref(v_a_2459_);
lean_dec(v_a_2458_);
lean_dec_ref(v_a_2457_);
lean_dec(v_a_2456_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_updateOccs(lean_object* v_p_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Int_Linear_Poly_updateOccs___redArg(v_p_2463_, v_a_2464_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_updateOccs___boxed(lean_object* v_p_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Int_Linear_Poly_updateOccs(v_p_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_);
lean_dec(v_a_2486_);
lean_dec_ref(v_a_2485_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
lean_dec(v_a_2478_);
lean_dec(v_a_2477_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go_spec__0(lean_object* v_a_2489_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Rat_ofInt(v_a_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go(lean_object* v_a_2491_, lean_object* v_v_2492_, lean_object* v_a_2493_){
_start:
{
if (lean_obj_tag(v_a_2493_) == 0)
{
lean_object* v_k_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2503_; 
lean_dec_ref(v_a_2491_);
v_k_2494_ = lean_ctor_get(v_a_2493_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_a_2493_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2496_ = v_a_2493_;
v_isShared_2497_ = v_isSharedCheck_2503_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_k_2494_);
lean_dec(v_a_2493_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2503_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2501_; 
v___x_2498_ = l_Rat_ofInt(v_k_2494_);
v___x_2499_ = l_Rat_add(v_v_2492_, v___x_2498_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set_tag(v___x_2496_, 1);
lean_ctor_set(v___x_2496_, 0, v___x_2499_);
v___x_2501_ = v___x_2496_;
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
else
{
lean_object* v_k_2504_; lean_object* v_v_2505_; lean_object* v_p_2506_; lean_object* v_size_2507_; uint8_t v___x_2508_; 
v_k_2504_ = lean_ctor_get(v_a_2493_, 0);
lean_inc(v_k_2504_);
v_v_2505_ = lean_ctor_get(v_a_2493_, 1);
lean_inc(v_v_2505_);
v_p_2506_ = lean_ctor_get(v_a_2493_, 2);
lean_inc_ref(v_p_2506_);
lean_dec_ref(v_a_2493_);
v_size_2507_ = lean_ctor_get(v_a_2491_, 2);
v___x_2508_ = lean_nat_dec_lt(v_v_2505_, v_size_2507_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; 
lean_dec_ref(v_p_2506_);
lean_dec(v_v_2505_);
lean_dec(v_k_2504_);
lean_dec_ref(v_v_2492_);
lean_dec_ref(v_a_2491_);
v___x_2509_ = lean_box(0);
return v___x_2509_;
}
else
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2510_ = l_Rat_ofInt(v_k_2504_);
v___x_2511_ = l_instInhabitedRat;
lean_inc_ref(v_a_2491_);
v___x_2512_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2511_, v_a_2491_, v_v_2505_);
lean_dec(v_v_2505_);
v___x_2513_ = l_Rat_mul(v___x_2510_, v___x_2512_);
lean_dec_ref(v___x_2510_);
v___x_2514_ = l_Rat_add(v_v_2492_, v___x_2513_);
v_v_2492_ = v___x_2514_;
v_a_2493_ = v_p_2506_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_Linear_Poly_eval_x3f_spec__0(lean_object* v_a_2516_){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_nat_to_int(v_a_2516_);
v___x_2518_ = l_Rat_ofInt(v___x_2517_);
return v___x_2518_;
}
}
static lean_object* _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = lean_unsigned_to_nat(0u);
v___x_2520_ = l_Nat_cast___at___00Int_Linear_Poly_eval_x3f_spec__0(v___x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_eval_x3f___redArg(lean_object* v_p_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_){
_start:
{
lean_object* v___x_2525_; 
v___x_2525_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2522_, v_a_2523_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2536_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2536_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2536_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v_assignment_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2534_; 
v_assignment_2530_ = lean_ctor_get(v_a_2526_, 13);
lean_inc_ref(v_assignment_2530_);
lean_dec(v_a_2526_);
v___x_2531_ = lean_obj_once(&l_Int_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2532_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go(v_assignment_2530_, v___x_2531_, v_p_2521_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v___x_2532_);
v___x_2534_ = v___x_2528_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec_ref(v_p_2521_);
v_a_2537_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2525_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2525_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_eval_x3f___redArg___boxed(lean_object* v_p_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2545_, v_a_2546_, v_a_2547_);
lean_dec_ref(v_a_2547_);
lean_dec(v_a_2546_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_eval_x3f(lean_object* v_p_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2550_, v_a_2551_, v_a_2559_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_eval_x3f___boxed(lean_object* v_p_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Int_Linear_Poly_eval_x3f(v_p_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
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
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(lean_object* v_c_2576_){
_start:
{
lean_object* v_p_2577_; uint8_t v___x_2578_; 
v_p_2577_ = lean_ctor_get(v_c_2576_, 0);
v___x_2578_ = l_Int_Linear_Poly_isUnsatLe(v_p_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat___boxed(lean_object* v_c_2579_){
_start:
{
uint8_t v_res_2580_; lean_object* v_r_2581_; 
v_res_2580_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(v_c_2579_);
lean_dec_ref(v_c_2579_);
v_r_2581_ = lean_box(v_res_2580_);
return v_r_2581_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(lean_object* v_c_2582_){
_start:
{
lean_object* v_d_2583_; lean_object* v_p_2584_; uint8_t v___x_2585_; 
v_d_2583_ = lean_ctor_get(v_c_2582_, 0);
lean_inc(v_d_2583_);
v_p_2584_ = lean_ctor_get(v_c_2582_, 1);
lean_inc_ref(v_p_2584_);
lean_dec_ref(v_c_2582_);
v___x_2585_ = l_Int_Linear_Poly_isUnsatDvd(v_d_2583_, v_p_2584_);
lean_dec_ref(v_p_2584_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat___boxed(lean_object* v_c_2586_){
_start:
{
uint8_t v_res_2587_; lean_object* v_r_2588_; 
v_res_2587_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(v_c_2586_);
v_r_2588_ = lean_box(v_res_2587_);
return v_r_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object* v_c_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v_d_2593_; lean_object* v_p_2594_; lean_object* v___x_2595_; 
v_d_2593_ = lean_ctor_get(v_c_2589_, 0);
lean_inc(v_d_2593_);
v_p_2594_ = lean_ctor_get(v_c_2589_, 1);
lean_inc_ref(v_p_2594_);
lean_dec_ref(v_c_2589_);
v___x_2595_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2594_, v_a_2590_, v_a_2591_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2621_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2598_ = v___x_2595_;
v_isShared_2599_ = v_isSharedCheck_2621_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2595_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2621_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
if (lean_obj_tag(v_a_2596_) == 1)
{
lean_object* v_val_2600_; lean_object* v_num_2601_; lean_object* v_den_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
v_val_2600_ = lean_ctor_get(v_a_2596_, 0);
lean_inc(v_val_2600_);
lean_dec_ref(v_a_2596_);
v_num_2601_ = lean_ctor_get(v_val_2600_, 0);
lean_inc(v_num_2601_);
v_den_2602_ = lean_ctor_get(v_val_2600_, 1);
lean_inc(v_den_2602_);
lean_dec(v_val_2600_);
v___x_2603_ = lean_unsigned_to_nat(1u);
v___x_2604_ = lean_nat_dec_eq(v_den_2602_, v___x_2603_);
lean_dec(v_den_2602_);
if (v___x_2604_ == 0)
{
uint8_t v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2608_; 
lean_dec(v_num_2601_);
lean_dec(v_d_2593_);
v___x_2605_ = 0;
v___x_2606_ = lean_box(v___x_2605_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2606_);
v___x_2608_ = v___x_2598_;
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
else
{
uint8_t v___x_2610_; uint8_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2610_ = l_Int_decidableDvd(v_d_2593_, v_num_2601_);
lean_dec(v_num_2601_);
lean_dec(v_d_2593_);
v___x_2611_ = l_Bool_toLBool(v___x_2610_);
v___x_2612_ = lean_box(v___x_2611_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2612_);
v___x_2614_ = v___x_2598_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
else
{
uint8_t v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2619_; 
lean_dec(v_a_2596_);
lean_dec(v_d_2593_);
v___x_2616_ = 2;
v___x_2617_ = lean_box(v___x_2616_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2617_);
v___x_2619_ = v___x_2598_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec(v_d_2593_);
v_a_2622_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2595_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2595_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg___boxed(lean_object* v_c_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2630_, v_a_2631_, v_a_2632_);
lean_dec_ref(v_a_2632_);
lean_dec(v_a_2631_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(lean_object* v_c_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_2635_, v_a_2636_, v_a_2644_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___boxed(lean_object* v_c_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(v_c_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec(v_a_2649_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_satisfiedLe___redArg(lean_object* v_p_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2661_, v_a_2662_, v_a_2663_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2683_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2668_ = v___x_2665_;
v_isShared_2669_ = v_isSharedCheck_2683_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2683_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
if (lean_obj_tag(v_a_2666_) == 1)
{
lean_object* v_val_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; uint8_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
v_val_2670_ = lean_ctor_get(v_a_2666_, 0);
lean_inc(v_val_2670_);
lean_dec_ref(v_a_2666_);
v___x_2671_ = lean_obj_once(&l_Int_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2672_ = l_Rat_instDecidableLe(v_val_2670_, v___x_2671_);
v___x_2673_ = l_Bool_toLBool(v___x_2672_);
v___x_2674_ = lean_box(v___x_2673_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2674_);
v___x_2676_ = v___x_2668_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
else
{
uint8_t v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2681_; 
lean_dec(v_a_2666_);
v___x_2678_ = 2;
v___x_2679_ = lean_box(v___x_2678_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2679_);
v___x_2681_ = v___x_2668_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
v_a_2684_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2665_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2665_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_satisfiedLe___redArg___boxed(lean_object* v_p_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l_Int_Linear_Poly_satisfiedLe___redArg(v_p_2692_, v_a_2693_, v_a_2694_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_satisfiedLe(lean_object* v_p_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Int_Linear_Poly_satisfiedLe___redArg(v_p_2697_, v_a_2698_, v_a_2706_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_satisfiedLe___boxed(lean_object* v_p_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Int_Linear_Poly_satisfiedLe(v_p_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
lean_dec(v_a_2720_);
lean_dec_ref(v_a_2719_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec(v_a_2711_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(lean_object* v_c_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v_p_2727_; lean_object* v___x_2728_; 
v_p_2727_ = lean_ctor_get(v_c_2723_, 0);
lean_inc_ref(v_p_2727_);
lean_dec_ref(v_c_2723_);
v___x_2728_ = l_Int_Linear_Poly_satisfiedLe___redArg(v_p_2727_, v_a_2724_, v_a_2725_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg___boxed(lean_object* v_c_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2729_, v_a_2730_, v_a_2731_);
lean_dec_ref(v_a_2731_);
lean_dec(v_a_2730_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(lean_object* v_c_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_2734_, v_a_2735_, v_a_2743_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___boxed(lean_object* v_c_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(v_c_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
lean_dec(v_a_2757_);
lean_dec_ref(v_a_2756_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
lean_dec(v_a_2751_);
lean_dec_ref(v_a_2750_);
lean_dec(v_a_2749_);
lean_dec(v_a_2748_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(lean_object* v_c_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v_p_2764_; lean_object* v___x_2765_; 
v_p_2764_ = lean_ctor_get(v_c_2760_, 0);
lean_inc_ref(v_p_2764_);
lean_dec_ref(v_c_2760_);
v___x_2765_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2764_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2785_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2785_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2765_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2785_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
uint8_t v___y_2771_; 
if (lean_obj_tag(v_a_2766_) == 1)
{
lean_object* v_val_2777_; lean_object* v___x_2778_; uint8_t v___x_2779_; 
v_val_2777_ = lean_ctor_get(v_a_2766_, 0);
lean_inc(v_val_2777_);
lean_dec_ref(v_a_2766_);
v___x_2778_ = lean_obj_once(&l_Int_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2779_ = l_instDecidableEqRat_decEq(v_val_2777_, v___x_2778_);
lean_dec(v_val_2777_);
if (v___x_2779_ == 0)
{
uint8_t v___x_2780_; 
v___x_2780_ = 1;
v___y_2771_ = v___x_2780_;
goto v___jp_2770_;
}
else
{
uint8_t v___x_2781_; 
v___x_2781_ = 0;
v___y_2771_ = v___x_2781_;
goto v___jp_2770_;
}
}
else
{
uint8_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
lean_del_object(v___x_2768_);
lean_dec(v_a_2766_);
v___x_2782_ = 2;
v___x_2783_ = lean_box(v___x_2782_);
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
return v___x_2784_;
}
v___jp_2770_:
{
uint8_t v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2775_; 
v___x_2772_ = l_Bool_toLBool(v___y_2771_);
v___x_2773_ = lean_box(v___x_2772_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 0, v___x_2773_);
v___x_2775_ = v___x_2768_;
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
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
v_a_2786_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2765_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2765_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg___boxed(lean_object* v_c_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_2794_, v_a_2795_, v_a_2796_);
lean_dec_ref(v_a_2796_);
lean_dec(v_a_2795_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(lean_object* v_c_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(v_c_2799_, v_a_2800_, v_a_2808_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___boxed(lean_object* v_c_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(v_c_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
lean_dec(v_a_2814_);
lean_dec(v_a_2813_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(lean_object* v_c_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_){
_start:
{
lean_object* v_p_2829_; lean_object* v___x_2830_; 
v_p_2829_ = lean_ctor_get(v_c_2825_, 0);
lean_inc_ref(v_p_2829_);
lean_dec_ref(v_c_2825_);
v___x_2830_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_2829_, v_a_2826_, v_a_2827_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2848_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2833_ = v___x_2830_;
v_isShared_2834_ = v_isSharedCheck_2848_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2830_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2848_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
if (lean_obj_tag(v_a_2831_) == 1)
{
lean_object* v_val_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; uint8_t v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2841_; 
v_val_2835_ = lean_ctor_get(v_a_2831_, 0);
lean_inc(v_val_2835_);
lean_dec_ref(v_a_2831_);
v___x_2836_ = lean_obj_once(&l_Int_Linear_Poly_eval_x3f___redArg___closed__0, &l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once, _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0);
v___x_2837_ = l_instDecidableEqRat_decEq(v_val_2835_, v___x_2836_);
lean_dec(v_val_2835_);
v___x_2838_ = l_Bool_toLBool(v___x_2837_);
v___x_2839_ = lean_box(v___x_2838_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v___x_2839_);
v___x_2841_ = v___x_2833_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2839_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
else
{
uint8_t v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2846_; 
lean_dec(v_a_2831_);
v___x_2843_ = 2;
v___x_2844_ = lean_box(v___x_2843_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v___x_2844_);
v___x_2846_ = v___x_2833_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
v_a_2849_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2830_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2830_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg___boxed(lean_object* v_c_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_2857_, v_a_2858_, v_a_2859_);
lean_dec_ref(v_a_2859_);
lean_dec(v_a_2858_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(lean_object* v_c_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_2862_, v_a_2863_, v_a_2871_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___boxed(lean_object* v_c_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(v_c_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_);
lean_dec(v_a_2885_);
lean_dec_ref(v_a_2884_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
lean_dec(v_a_2881_);
lean_dec_ref(v_a_2880_);
lean_dec(v_a_2879_);
lean_dec_ref(v_a_2878_);
lean_dec(v_a_2877_);
lean_dec(v_a_2876_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_findVarToSubst___redArg(lean_object* v_p_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_){
_start:
{
if (lean_obj_tag(v_p_2888_) == 0)
{
lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2899_; 
v_isSharedCheck_2899_ = !lean_is_exclusive(v_p_2888_);
if (v_isSharedCheck_2899_ == 0)
{
lean_object* v_unused_2900_; 
v_unused_2900_ = lean_ctor_get(v_p_2888_, 0);
lean_dec(v_unused_2900_);
v___x_2893_ = v_p_2888_;
v_isShared_2894_ = v_isSharedCheck_2899_;
goto v_resetjp_2892_;
}
else
{
lean_dec(v_p_2888_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2899_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2895_ = lean_box(0);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v___x_2895_);
v___x_2897_ = v___x_2893_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2895_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
else
{
lean_object* v_k_2901_; lean_object* v_v_2902_; lean_object* v_p_2903_; lean_object* v___x_2904_; 
v_k_2901_ = lean_ctor_get(v_p_2888_, 0);
lean_inc(v_k_2901_);
v_v_2902_ = lean_ctor_get(v_p_2888_, 1);
lean_inc(v_v_2902_);
v_p_2903_ = lean_ctor_get(v_p_2888_, 2);
lean_inc_ref(v_p_2903_);
lean_dec_ref(v_p_2888_);
v___x_2904_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2889_, v_a_2890_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2931_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2907_ = v___x_2904_;
v_isShared_2908_ = v_isSharedCheck_2931_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2904_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2931_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___y_2910_; lean_object* v_elimEqs_2925_; lean_object* v_size_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; 
v_elimEqs_2925_ = lean_ctor_get(v_a_2905_, 10);
lean_inc_ref(v_elimEqs_2925_);
lean_dec(v_a_2905_);
v_size_2926_ = lean_ctor_get(v_elimEqs_2925_, 2);
v___x_2927_ = lean_box(0);
v___x_2928_ = lean_nat_dec_lt(v_v_2902_, v_size_2926_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; 
lean_dec_ref(v_elimEqs_2925_);
v___x_2929_ = l_outOfBounds___redArg(v___x_2927_);
v___y_2910_ = v___x_2929_;
goto v___jp_2909_;
}
else
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2927_, v_elimEqs_2925_, v_v_2902_);
v___y_2910_ = v___x_2930_;
goto v___jp_2909_;
}
v___jp_2909_:
{
if (lean_obj_tag(v___y_2910_) == 1)
{
lean_object* v_val_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2923_; 
lean_dec_ref(v_p_2903_);
v_val_2911_ = lean_ctor_get(v___y_2910_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___y_2910_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2913_ = v___y_2910_;
v_isShared_2914_ = v_isSharedCheck_2923_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_val_2911_);
lean_dec(v___y_2910_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2923_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2915_, 0, v_v_2902_);
lean_ctor_set(v___x_2915_, 1, v_val_2911_);
v___x_2916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2916_, 0, v_k_2901_);
lean_ctor_set(v___x_2916_, 1, v___x_2915_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v___x_2916_);
v___x_2918_ = v___x_2913_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2920_; 
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v___x_2918_);
v___x_2920_ = v___x_2907_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2918_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
else
{
lean_dec(v___y_2910_);
lean_del_object(v___x_2907_);
lean_dec(v_v_2902_);
lean_dec(v_k_2901_);
v_p_2888_ = v_p_2903_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
lean_dec_ref(v_p_2903_);
lean_dec(v_v_2902_);
lean_dec(v_k_2901_);
v_a_2932_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2904_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2904_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_findVarToSubst___redArg___boxed(lean_object* v_p_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_2940_, v_a_2941_, v_a_2942_);
lean_dec_ref(v_a_2942_);
lean_dec(v_a_2941_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_findVarToSubst(lean_object* v_p_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_2945_, v_a_2946_, v_a_2954_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_findVarToSubst___boxed(lean_object* v_p_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Int_Linear_Poly_findVarToSubst(v_p_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
lean_dec(v_a_2968_);
lean_dec_ref(v_a_2967_);
lean_dec(v_a_2966_);
lean_dec_ref(v_a_2965_);
lean_dec(v_a_2964_);
lean_dec_ref(v_a_2963_);
lean_dec(v_a_2962_);
lean_dec_ref(v_a_2961_);
lean_dec(v_a_2960_);
lean_dec(v_a_2959_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(lean_object* v_pred_2971_){
_start:
{
lean_object* v_c_u2081_2972_; lean_object* v_c_u2082_2973_; uint8_t v_left_2974_; lean_object* v_c_u2083_x3f_2975_; lean_object* v_p_2976_; lean_object* v_p_2977_; lean_object* v_a_2978_; lean_object* v_b_2979_; 
v_c_u2081_2972_ = lean_ctor_get(v_pred_2971_, 0);
v_c_u2082_2973_ = lean_ctor_get(v_pred_2971_, 1);
v_left_2974_ = lean_ctor_get_uint8(v_pred_2971_, sizeof(void*)*3);
v_c_u2083_x3f_2975_ = lean_ctor_get(v_pred_2971_, 2);
v_p_2976_ = lean_ctor_get(v_c_u2081_2972_, 0);
v_p_2977_ = lean_ctor_get(v_c_u2082_2973_, 0);
v_a_2978_ = l_Int_Linear_Poly_leadCoeff(v_p_2976_);
v_b_2979_ = l_Int_Linear_Poly_leadCoeff(v_p_2977_);
if (lean_obj_tag(v_c_u2083_x3f_2975_) == 0)
{
if (v_left_2974_ == 0)
{
lean_object* v___x_2980_; 
lean_dec(v_a_2978_);
v___x_2980_ = lean_nat_abs(v_b_2979_);
lean_dec(v_b_2979_);
return v___x_2980_;
}
else
{
lean_object* v___x_2981_; 
lean_dec(v_b_2979_);
v___x_2981_ = lean_nat_abs(v_a_2978_);
lean_dec(v_a_2978_);
return v___x_2981_;
}
}
else
{
lean_object* v_val_2982_; lean_object* v_d_2983_; lean_object* v_p_2984_; lean_object* v_c_2985_; 
v_val_2982_ = lean_ctor_get(v_c_u2083_x3f_2975_, 0);
v_d_2983_ = lean_ctor_get(v_val_2982_, 0);
v_p_2984_ = lean_ctor_get(v_val_2982_, 1);
v_c_2985_ = l_Int_Linear_Poly_leadCoeff(v_p_2984_);
if (v_left_2974_ == 0)
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
lean_dec(v_a_2978_);
v___x_2986_ = lean_int_mul(v_b_2979_, v_d_2983_);
v___x_2987_ = l_Int_gcd(v___x_2986_, v_c_2985_);
lean_dec(v_c_2985_);
v___x_2988_ = lean_nat_to_int(v___x_2987_);
v___x_2989_ = lean_int_ediv(v___x_2986_, v___x_2988_);
lean_dec(v___x_2988_);
lean_dec(v___x_2986_);
v___x_2990_ = l_Int_lcm(v_b_2979_, v___x_2989_);
lean_dec(v___x_2989_);
lean_dec(v_b_2979_);
return v___x_2990_;
}
else
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
lean_dec(v_b_2979_);
v___x_2991_ = lean_int_mul(v_a_2978_, v_d_2983_);
v___x_2992_ = l_Int_gcd(v___x_2991_, v_c_2985_);
lean_dec(v_c_2985_);
v___x_2993_ = lean_nat_to_int(v___x_2992_);
v___x_2994_ = lean_int_ediv(v___x_2991_, v___x_2993_);
lean_dec(v___x_2993_);
lean_dec(v___x_2991_);
v___x_2995_ = l_Int_lcm(v_a_2978_, v___x_2994_);
lean_dec(v___x_2994_);
lean_dec(v_a_2978_);
return v___x_2995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases___boxed(lean_object* v_pred_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(v_pred_2996_);
lean_dec_ref(v_pred_2996_);
return v_res_2997_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1(void){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0));
v___x_3000_ = l_Lean_stringToMessageData(v___x_2999_);
return v___x_3000_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4(void){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3));
v___x_3005_ = l_Lean_MessageData_ofFormat(v___x_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(lean_object* v_pred_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v_c_u2081_3010_; lean_object* v_c_u2082_3011_; lean_object* v_c_u2083_x3f_3012_; lean_object* v___x_3013_; 
v_c_u2081_3010_ = lean_ctor_get(v_pred_3006_, 0);
lean_inc_ref(v_c_u2081_3010_);
v_c_u2082_3011_ = lean_ctor_get(v_pred_3006_, 1);
lean_inc_ref(v_c_u2082_3011_);
v_c_u2083_x3f_3012_ = lean_ctor_get(v_pred_3006_, 2);
lean_inc(v_c_u2083_x3f_3012_);
lean_dec_ref(v_pred_3006_);
v___x_3013_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3010_, v_a_3007_, v_a_3008_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3015_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref(v___x_3013_);
v___x_3015_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3011_, v_a_3007_, v_a_3008_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3034_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3018_ = v___x_3015_;
v_isShared_3019_ = v_isSharedCheck_3034_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3015_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3034_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v_a_3021_; 
if (lean_obj_tag(v_c_u2083_x3f_3012_) == 1)
{
lean_object* v_val_3030_; lean_object* v___x_3031_; 
v_val_3030_ = lean_ctor_get(v_c_u2083_x3f_3012_, 0);
lean_inc(v_val_3030_);
lean_dec_ref(v_c_u2083_x3f_3012_);
v___x_3031_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_val_3030_, v_a_3007_, v_a_3008_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref(v___x_3031_);
v_a_3021_ = v_a_3032_;
goto v___jp_3020_;
}
else
{
lean_del_object(v___x_3018_);
lean_dec(v_a_3016_);
lean_dec(v_a_3014_);
return v___x_3031_;
}
}
else
{
lean_object* v___x_3033_; 
lean_dec(v_c_u2083_x3f_3012_);
v___x_3033_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4);
v_a_3021_ = v___x_3033_;
goto v___jp_3020_;
}
v___jp_3020_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3028_; 
v___x_3022_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3023_, 0, v_a_3014_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
v___x_3024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
lean_ctor_set(v___x_3024_, 1, v_a_3016_);
v___x_3025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
lean_ctor_set(v___x_3025_, 1, v___x_3022_);
v___x_3026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
lean_ctor_set(v___x_3026_, 1, v_a_3021_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 0, v___x_3026_);
v___x_3028_ = v___x_3018_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_3026_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
else
{
lean_dec(v_a_3014_);
lean_dec(v_c_u2083_x3f_3012_);
return v___x_3015_;
}
}
else
{
lean_dec(v_c_u2083_x3f_3012_);
lean_dec_ref(v_c_u2082_3011_);
return v___x_3013_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___boxed(lean_object* v_pred_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_3035_, v_a_3036_, v_a_3037_);
lean_dec_ref(v_a_3037_);
lean_dec(v_a_3036_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(lean_object* v_pred_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(v_pred_3040_, v_a_3041_, v_a_3049_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___boxed(lean_object* v_pred_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(v_pred_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(lean_object* v_h_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
switch(lean_obj_tag(v_h_3066_))
{
case 0:
{
lean_object* v_c_3070_; lean_object* v___x_3071_; 
v_c_3070_ = lean_ctor_get(v_h_3066_, 0);
lean_inc_ref(v_c_3070_);
lean_dec_ref(v_h_3066_);
v___x_3071_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_3070_, v_a_3067_, v_a_3068_);
return v___x_3071_;
}
case 1:
{
lean_object* v_c_3072_; lean_object* v___x_3073_; 
v_c_3072_ = lean_ctor_get(v_h_3066_, 0);
lean_inc_ref(v_c_3072_);
lean_dec_ref(v_h_3066_);
v___x_3073_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3072_, v_a_3067_, v_a_3068_);
return v___x_3073_;
}
case 2:
{
lean_object* v_c_3074_; lean_object* v___x_3075_; 
v_c_3074_ = lean_ctor_get(v_h_3066_, 0);
lean_inc_ref(v_c_3074_);
lean_dec_ref(v_h_3066_);
v___x_3075_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_3074_, v_a_3067_, v_a_3068_);
return v___x_3075_;
}
case 3:
{
lean_object* v_c_3076_; lean_object* v___x_3077_; 
v_c_3076_ = lean_ctor_get(v_h_3066_, 0);
lean_inc_ref(v_c_3076_);
lean_dec_ref(v_h_3066_);
v___x_3077_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_3076_, v_a_3067_, v_a_3068_);
return v___x_3077_;
}
default: 
{
lean_object* v_c_u2081_3078_; lean_object* v_c_u2082_3079_; lean_object* v_c_u2083_3080_; lean_object* v___x_3081_; 
v_c_u2081_3078_ = lean_ctor_get(v_h_3066_, 0);
lean_inc_ref(v_c_u2081_3078_);
v_c_u2082_3079_ = lean_ctor_get(v_h_3066_, 1);
lean_inc_ref(v_c_u2082_3079_);
v_c_u2083_3080_ = lean_ctor_get(v_h_3066_, 2);
lean_inc_ref(v_c_u2083_3080_);
lean_dec_ref(v_h_3066_);
v___x_3081_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2081_3078_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v___x_3083_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3082_);
lean_dec_ref(v___x_3081_);
v___x_3083_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_3079_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3085_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref(v___x_3083_);
v___x_3085_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2083_3080_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3098_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3088_ = v___x_3085_;
v_isShared_3089_ = v_isSharedCheck_3098_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3085_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3098_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3090_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1);
v___x_3091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3091_, 0, v_a_3082_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
v___x_3092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
lean_ctor_set(v___x_3092_, 1, v_a_3084_);
v___x_3093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
lean_ctor_set(v___x_3093_, 1, v___x_3090_);
v___x_3094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v_a_3086_);
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 0, v___x_3094_);
v___x_3096_ = v___x_3088_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
else
{
lean_dec(v_a_3084_);
lean_dec(v_a_3082_);
return v___x_3085_;
}
}
else
{
lean_dec(v_a_3082_);
lean_dec_ref(v_c_u2083_3080_);
return v___x_3083_;
}
}
else
{
lean_dec_ref(v_c_u2083_3080_);
lean_dec_ref(v_c_u2082_3079_);
return v___x_3081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg___boxed(lean_object* v_h_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3099_, v_a_3100_, v_a_3101_);
lean_dec_ref(v_a_3101_);
lean_dec(v_a_3100_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(lean_object* v_h_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_3104_, v_a_3105_, v_a_3113_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___boxed(lean_object* v_h_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(v_h_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
lean_dec(v_a_3127_);
lean_dec_ref(v_a_3126_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
lean_dec(v_a_3123_);
lean_dec_ref(v_a_3122_);
lean_dec(v_a_3121_);
lean_dec_ref(v_a_3120_);
lean_dec(v_a_3119_);
lean_dec(v_a_3118_);
return v_res_3129_;
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
