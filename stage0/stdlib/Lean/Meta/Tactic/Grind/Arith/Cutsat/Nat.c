// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Init.Data.Int.OfNat import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt import Lean.Meta.NatInstTesters
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHDivInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHModInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHPowInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_mkIntNatCast(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkIntMul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHDivNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkIntDiv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkIntMod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHPowNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkIntPowNat(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toInt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte;
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "val"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__1_value),LEAN_SCALAR_PTR_LITERAL(165, 91, 87, 132, 175, 103, 206, 109)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__6_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__7_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__9_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__10_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__12_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__13_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__15_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__16_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__18_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__19_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ToInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__23_value),LEAN_SCALAR_PTR_LITERAL(34, 126, 174, 185, 27, 56, 123, 61)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mul_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__26_value),LEAN_SCALAR_PTR_LITERAL(246, 119, 195, 92, 68, 86, 209, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "div_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__29_value),LEAN_SCALAR_PTR_LITERAL(34, 168, 146, 132, 240, 126, 147, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mod_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__32_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__32_value),LEAN_SCALAR_PTR_LITERAL(88, 250, 102, 19, 8, 50, 252, 167)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "pow_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__35 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__35_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__35_value),LEAN_SCALAR_PTR_LITERAL(252, 58, 93, 228, 192, 253, 115, 4)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "natCast_ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__38 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__38_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__38_value),LEAN_SCALAR_PTR_LITERAL(238, 161, 137, 195, 161, 239, 200, 79)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__41 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__41_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "finVal"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__43 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__43_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__21_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__22_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__43_value),LEAN_SCALAR_PTR_LITERAL(253, 227, 103, 7, 1, 145, 189, 213)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "isLt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__46_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__46_value),LEAN_SCALAR_PTR_LITERAL(222, 150, 50, 101, 25, 222, 136, 68)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastInt"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 224, 75, 57, 255, 108, 159, 197)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 96, .m_capacity = 96, .m_length = 95, .m_data = "_private.Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat.0.Lean.Meta.Grind.Arith.Cutsat.mkNonnegThm\?.go"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Nonneg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(219, 60, 236, 27, 19, 252, 65, 16)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1_value),LEAN_SCALAR_PTR_LITERAL(221, 113, 7, 185, 57, 18, 171, 207)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(219, 60, 236, 27, 19, 252, 65, 16)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__8_value),LEAN_SCALAR_PTR_LITERAL(18, 216, 199, 74, 39, 140, 254, 20)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(219, 60, 236, 27, 19, 252, 65, 16)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__11_value),LEAN_SCALAR_PTR_LITERAL(188, 150, 118, 217, 197, 2, 106, 60)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "div"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(219, 60, 236, 27, 19, 252, 65, 16)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__14_value),LEAN_SCALAR_PTR_LITERAL(3, 105, 42, 253, 30, 168, 164, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(219, 60, 236, 27, 19, 252, 65, 16)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__17_value),LEAN_SCALAR_PTR_LITERAL(52, 118, 58, 105, 21, 29, 158, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(219, 60, 236, 27, 19, 252, 65, 16)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__20_value),LEAN_SCALAR_PTR_LITERAL(91, 38, 36, 71, 236, 90, 216, 150)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(219, 60, 236, 27, 19, 252, 65, 16)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__23_value),LEAN_SCALAR_PTR_LITERAL(195, 74, 119, 167, 0, 49, 135, 237)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toPoly"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(219, 60, 236, 27, 19, 252, 65, 16)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 134, 248, 74, 100, 20, 67, 14)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_x_3_, lean_object* v_x_4_){
_start:
{
lean_object* v_ks_5_; lean_object* v_vs_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_30_; 
v_ks_5_ = lean_ctor_get(v_x_1_, 0);
v_vs_6_ = lean_ctor_get(v_x_1_, 1);
v_isSharedCheck_30_ = !lean_is_exclusive(v_x_1_);
if (v_isSharedCheck_30_ == 0)
{
v___x_8_ = v_x_1_;
v_isShared_9_ = v_isSharedCheck_30_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_vs_6_);
lean_inc(v_ks_5_);
lean_dec(v_x_1_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_30_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_10_ = lean_array_get_size(v_ks_5_);
v___x_11_ = lean_nat_dec_lt(v_x_2_, v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_15_; 
lean_dec(v_x_2_);
v___x_12_ = lean_array_push(v_ks_5_, v_x_3_);
v___x_13_ = lean_array_push(v_vs_6_, v_x_4_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v___x_13_);
lean_ctor_set(v___x_8_, 0, v___x_12_);
v___x_15_ = v___x_8_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v___x_12_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v___x_13_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
else
{
lean_object* v_k_x27_17_; uint8_t v___x_18_; 
v_k_x27_17_ = lean_array_fget_borrowed(v_ks_5_, v_x_2_);
v___x_18_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_3_, v_k_x27_17_);
if (v___x_18_ == 0)
{
lean_object* v___x_20_; 
if (v_isShared_9_ == 0)
{
v___x_20_ = v___x_8_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_ks_5_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v_vs_6_);
v___x_20_ = v_reuseFailAlloc_24_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_unsigned_to_nat(1u);
v___x_22_ = lean_nat_add(v_x_2_, v___x_21_);
lean_dec(v_x_2_);
v_x_1_ = v___x_20_;
v_x_2_ = v___x_22_;
goto _start;
}
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_25_ = lean_array_fset(v_ks_5_, v_x_2_, v_x_3_);
v___x_26_ = lean_array_fset(v_vs_6_, v_x_2_, v_x_4_);
lean_dec(v_x_2_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v___x_26_);
lean_ctor_set(v___x_8_, 0, v___x_25_);
v___x_28_ = v___x_8_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_25_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4___redArg(lean_object* v_n_31_, lean_object* v_k_32_, lean_object* v_v_33_){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5___redArg(v_n_31_, v___x_34_, v_k_32_, v_v_33_);
return v___x_35_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_36_; size_t v___x_37_; size_t v___x_38_; 
v___x_36_ = ((size_t)5ULL);
v___x_37_ = ((size_t)1ULL);
v___x_38_ = lean_usize_shift_left(v___x_37_, v___x_36_);
return v___x_38_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_39_; size_t v___x_40_; size_t v___x_41_; 
v___x_39_ = ((size_t)1ULL);
v___x_40_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0);
v___x_41_ = lean_usize_sub(v___x_40_, v___x_39_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(lean_object* v_x_43_, size_t v_x_44_, size_t v_x_45_, lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
lean_object* v_es_48_; size_t v___x_49_; size_t v___x_50_; size_t v___x_51_; size_t v___x_52_; lean_object* v_j_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
v_es_48_ = lean_ctor_get(v_x_43_, 0);
v___x_49_ = ((size_t)5ULL);
v___x_50_ = ((size_t)1ULL);
v___x_51_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1);
v___x_52_ = lean_usize_land(v_x_44_, v___x_51_);
v_j_53_ = lean_usize_to_nat(v___x_52_);
v___x_54_ = lean_array_get_size(v_es_48_);
v___x_55_ = lean_nat_dec_lt(v_j_53_, v___x_54_);
if (v___x_55_ == 0)
{
lean_dec(v_j_53_);
lean_dec(v_x_47_);
lean_dec_ref(v_x_46_);
return v_x_43_;
}
else
{
lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_92_; 
lean_inc_ref(v_es_48_);
v_isSharedCheck_92_ = !lean_is_exclusive(v_x_43_);
if (v_isSharedCheck_92_ == 0)
{
lean_object* v_unused_93_; 
v_unused_93_ = lean_ctor_get(v_x_43_, 0);
lean_dec(v_unused_93_);
v___x_57_ = v_x_43_;
v_isShared_58_ = v_isSharedCheck_92_;
goto v_resetjp_56_;
}
else
{
lean_dec(v_x_43_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_92_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v_v_59_; lean_object* v___x_60_; lean_object* v_xs_x27_61_; lean_object* v___y_63_; 
v_v_59_ = lean_array_fget(v_es_48_, v_j_53_);
v___x_60_ = lean_box(0);
v_xs_x27_61_ = lean_array_fset(v_es_48_, v_j_53_, v___x_60_);
switch(lean_obj_tag(v_v_59_))
{
case 0:
{
lean_object* v_key_68_; lean_object* v_val_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_79_; 
v_key_68_ = lean_ctor_get(v_v_59_, 0);
v_val_69_ = lean_ctor_get(v_v_59_, 1);
v_isSharedCheck_79_ = !lean_is_exclusive(v_v_59_);
if (v_isSharedCheck_79_ == 0)
{
v___x_71_ = v_v_59_;
v_isShared_72_ = v_isSharedCheck_79_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_val_69_);
lean_inc(v_key_68_);
lean_dec(v_v_59_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_79_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
uint8_t v___x_73_; 
v___x_73_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_46_, v_key_68_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_del_object(v___x_71_);
v___x_74_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_68_, v_val_69_, v_x_46_, v_x_47_);
v___x_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
v___y_63_ = v___x_75_;
goto v___jp_62_;
}
else
{
lean_object* v___x_77_; 
lean_dec(v_val_69_);
lean_dec(v_key_68_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v_x_47_);
lean_ctor_set(v___x_71_, 0, v_x_46_);
v___x_77_ = v___x_71_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_x_46_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v_x_47_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
v___y_63_ = v___x_77_;
goto v___jp_62_;
}
}
}
}
case 1:
{
lean_object* v_node_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_90_; 
v_node_80_ = lean_ctor_get(v_v_59_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v_v_59_);
if (v_isSharedCheck_90_ == 0)
{
v___x_82_ = v_v_59_;
v_isShared_83_ = v_isSharedCheck_90_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_node_80_);
lean_dec(v_v_59_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_90_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
size_t v___x_84_; size_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_84_ = lean_usize_shift_right(v_x_44_, v___x_49_);
v___x_85_ = lean_usize_add(v_x_45_, v___x_50_);
v___x_86_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_node_80_, v___x_84_, v___x_85_, v_x_46_, v_x_47_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_86_);
v___x_88_ = v___x_82_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
v___y_63_ = v___x_88_;
goto v___jp_62_;
}
}
}
default: 
{
lean_object* v___x_91_; 
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v_x_46_);
lean_ctor_set(v___x_91_, 1, v_x_47_);
v___y_63_ = v___x_91_;
goto v___jp_62_;
}
}
v___jp_62_:
{
lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_64_ = lean_array_fset(v_xs_x27_61_, v_j_53_, v___y_63_);
lean_dec(v_j_53_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_64_);
v___x_66_ = v___x_57_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_64_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
else
{
lean_object* v_ks_94_; lean_object* v_vs_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_115_; 
v_ks_94_ = lean_ctor_get(v_x_43_, 0);
v_vs_95_ = lean_ctor_get(v_x_43_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v_x_43_);
if (v_isSharedCheck_115_ == 0)
{
v___x_97_ = v_x_43_;
v_isShared_98_ = v_isSharedCheck_115_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_vs_95_);
lean_inc(v_ks_94_);
lean_dec(v_x_43_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_115_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_ks_94_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_vs_95_);
v___x_100_ = v_reuseFailAlloc_114_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v_newNode_101_; uint8_t v___y_103_; size_t v___x_109_; uint8_t v___x_110_; 
v_newNode_101_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4___redArg(v___x_100_, v_x_46_, v_x_47_);
v___x_109_ = ((size_t)7ULL);
v___x_110_ = lean_usize_dec_le(v___x_109_, v_x_45_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_111_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_101_);
v___x_112_ = lean_unsigned_to_nat(4u);
v___x_113_ = lean_nat_dec_lt(v___x_111_, v___x_112_);
lean_dec(v___x_111_);
v___y_103_ = v___x_113_;
goto v___jp_102_;
}
else
{
v___y_103_ = v___x_110_;
goto v___jp_102_;
}
v___jp_102_:
{
if (v___y_103_ == 0)
{
lean_object* v_ks_104_; lean_object* v_vs_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_ks_104_ = lean_ctor_get(v_newNode_101_, 0);
lean_inc_ref(v_ks_104_);
v_vs_105_ = lean_ctor_get(v_newNode_101_, 1);
lean_inc_ref(v_vs_105_);
lean_dec_ref(v_newNode_101_);
v___x_106_ = lean_unsigned_to_nat(0u);
v___x_107_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__2);
v___x_108_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(v_x_45_, v_ks_104_, v_vs_105_, v___x_106_, v___x_107_);
lean_dec_ref(v_vs_105_);
lean_dec_ref(v_ks_104_);
return v___x_108_;
}
else
{
return v_newNode_101_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(size_t v_depth_116_, lean_object* v_keys_117_, lean_object* v_vals_118_, lean_object* v_i_119_, lean_object* v_entries_120_){
_start:
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_array_get_size(v_keys_117_);
v___x_122_ = lean_nat_dec_lt(v_i_119_, v___x_121_);
if (v___x_122_ == 0)
{
lean_dec(v_i_119_);
return v_entries_120_;
}
else
{
lean_object* v_k_123_; lean_object* v_v_124_; uint64_t v___x_125_; size_t v_h_126_; size_t v___x_127_; lean_object* v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; size_t v_h_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_k_123_ = lean_array_fget_borrowed(v_keys_117_, v_i_119_);
v_v_124_ = lean_array_fget_borrowed(v_vals_118_, v_i_119_);
v___x_125_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_123_);
v_h_126_ = lean_uint64_to_usize(v___x_125_);
v___x_127_ = ((size_t)5ULL);
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_sub(v_depth_116_, v___x_129_);
v___x_131_ = lean_usize_mul(v___x_127_, v___x_130_);
v_h_132_ = lean_usize_shift_right(v_h_126_, v___x_131_);
v___x_133_ = lean_nat_add(v_i_119_, v___x_128_);
lean_dec(v_i_119_);
lean_inc(v_v_124_);
lean_inc(v_k_123_);
v___x_134_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_entries_120_, v_h_132_, v_depth_116_, v_k_123_, v_v_124_);
v_i_119_ = v___x_133_;
v_entries_120_ = v___x_134_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_136_, lean_object* v_keys_137_, lean_object* v_vals_138_, lean_object* v_i_139_, lean_object* v_entries_140_){
_start:
{
size_t v_depth_boxed_141_; lean_object* v_res_142_; 
v_depth_boxed_141_ = lean_unbox_usize(v_depth_136_);
lean_dec(v_depth_136_);
v_res_142_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(v_depth_boxed_141_, v_keys_137_, v_vals_138_, v_i_139_, v_entries_140_);
lean_dec_ref(v_vals_138_);
lean_dec_ref(v_keys_137_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___boxed(lean_object* v_x_143_, lean_object* v_x_144_, lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
size_t v_x_6481__boxed_148_; size_t v_x_6482__boxed_149_; lean_object* v_res_150_; 
v_x_6481__boxed_148_ = lean_unbox_usize(v_x_144_);
lean_dec(v_x_144_);
v_x_6482__boxed_149_ = lean_unbox_usize(v_x_145_);
lean_dec(v_x_145_);
v_res_150_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_x_143_, v_x_6481__boxed_148_, v_x_6482__boxed_149_, v_x_146_, v_x_147_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1___redArg(lean_object* v_x_151_, lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
uint64_t v___x_154_; size_t v___x_155_; size_t v___x_156_; lean_object* v___x_157_; 
v___x_154_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_152_);
v___x_155_ = lean_uint64_to_usize(v___x_154_);
v___x_156_ = ((size_t)1ULL);
v___x_157_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_x_151_, v___x_155_, v___x_156_, v_x_152_, v_x_153_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___lam__0(lean_object* v_e_158_, lean_object* v___x_159_, lean_object* v_s_160_){
_start:
{
lean_object* v_vars_161_; lean_object* v_varMap_162_; lean_object* v_vars_x27_163_; lean_object* v_varMap_x27_164_; lean_object* v_natToIntMap_165_; lean_object* v_natDef_166_; lean_object* v_dvds_167_; lean_object* v_lowers_168_; lean_object* v_uppers_169_; lean_object* v_diseqs_170_; lean_object* v_elimEqs_171_; lean_object* v_elimStack_172_; lean_object* v_occurs_173_; lean_object* v_assignment_174_; lean_object* v_nextCnstrId_175_; uint8_t v_caseSplits_176_; lean_object* v_conflict_x3f_177_; lean_object* v_diseqSplits_178_; lean_object* v_divMod_179_; lean_object* v_toIntIds_180_; lean_object* v_toIntInfos_181_; lean_object* v_toIntTermMap_182_; lean_object* v_toIntVarMap_183_; uint8_t v_usedCommRing_184_; lean_object* v_nonlinearOccs_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_193_; 
v_vars_161_ = lean_ctor_get(v_s_160_, 0);
v_varMap_162_ = lean_ctor_get(v_s_160_, 1);
v_vars_x27_163_ = lean_ctor_get(v_s_160_, 2);
v_varMap_x27_164_ = lean_ctor_get(v_s_160_, 3);
v_natToIntMap_165_ = lean_ctor_get(v_s_160_, 4);
v_natDef_166_ = lean_ctor_get(v_s_160_, 5);
v_dvds_167_ = lean_ctor_get(v_s_160_, 6);
v_lowers_168_ = lean_ctor_get(v_s_160_, 7);
v_uppers_169_ = lean_ctor_get(v_s_160_, 8);
v_diseqs_170_ = lean_ctor_get(v_s_160_, 9);
v_elimEqs_171_ = lean_ctor_get(v_s_160_, 10);
v_elimStack_172_ = lean_ctor_get(v_s_160_, 11);
v_occurs_173_ = lean_ctor_get(v_s_160_, 12);
v_assignment_174_ = lean_ctor_get(v_s_160_, 13);
v_nextCnstrId_175_ = lean_ctor_get(v_s_160_, 14);
v_caseSplits_176_ = lean_ctor_get_uint8(v_s_160_, sizeof(void*)*23);
v_conflict_x3f_177_ = lean_ctor_get(v_s_160_, 15);
v_diseqSplits_178_ = lean_ctor_get(v_s_160_, 16);
v_divMod_179_ = lean_ctor_get(v_s_160_, 17);
v_toIntIds_180_ = lean_ctor_get(v_s_160_, 18);
v_toIntInfos_181_ = lean_ctor_get(v_s_160_, 19);
v_toIntTermMap_182_ = lean_ctor_get(v_s_160_, 20);
v_toIntVarMap_183_ = lean_ctor_get(v_s_160_, 21);
v_usedCommRing_184_ = lean_ctor_get_uint8(v_s_160_, sizeof(void*)*23 + 1);
v_nonlinearOccs_185_ = lean_ctor_get(v_s_160_, 22);
v_isSharedCheck_193_ = !lean_is_exclusive(v_s_160_);
if (v_isSharedCheck_193_ == 0)
{
v___x_187_ = v_s_160_;
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_nonlinearOccs_185_);
lean_inc(v_toIntVarMap_183_);
lean_inc(v_toIntTermMap_182_);
lean_inc(v_toIntInfos_181_);
lean_inc(v_toIntIds_180_);
lean_inc(v_divMod_179_);
lean_inc(v_diseqSplits_178_);
lean_inc(v_conflict_x3f_177_);
lean_inc(v_nextCnstrId_175_);
lean_inc(v_assignment_174_);
lean_inc(v_occurs_173_);
lean_inc(v_elimStack_172_);
lean_inc(v_elimEqs_171_);
lean_inc(v_diseqs_170_);
lean_inc(v_uppers_169_);
lean_inc(v_lowers_168_);
lean_inc(v_dvds_167_);
lean_inc(v_natDef_166_);
lean_inc(v_natToIntMap_165_);
lean_inc(v_varMap_x27_164_);
lean_inc(v_vars_x27_163_);
lean_inc(v_varMap_162_);
lean_inc(v_vars_161_);
lean_dec(v_s_160_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_189_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1___redArg(v_natToIntMap_165_, v_e_158_, v___x_159_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 4, v___x_189_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_vars_161_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_varMap_162_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v_vars_x27_163_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v_varMap_x27_164_);
lean_ctor_set(v_reuseFailAlloc_192_, 4, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_192_, 5, v_natDef_166_);
lean_ctor_set(v_reuseFailAlloc_192_, 6, v_dvds_167_);
lean_ctor_set(v_reuseFailAlloc_192_, 7, v_lowers_168_);
lean_ctor_set(v_reuseFailAlloc_192_, 8, v_uppers_169_);
lean_ctor_set(v_reuseFailAlloc_192_, 9, v_diseqs_170_);
lean_ctor_set(v_reuseFailAlloc_192_, 10, v_elimEqs_171_);
lean_ctor_set(v_reuseFailAlloc_192_, 11, v_elimStack_172_);
lean_ctor_set(v_reuseFailAlloc_192_, 12, v_occurs_173_);
lean_ctor_set(v_reuseFailAlloc_192_, 13, v_assignment_174_);
lean_ctor_set(v_reuseFailAlloc_192_, 14, v_nextCnstrId_175_);
lean_ctor_set(v_reuseFailAlloc_192_, 15, v_conflict_x3f_177_);
lean_ctor_set(v_reuseFailAlloc_192_, 16, v_diseqSplits_178_);
lean_ctor_set(v_reuseFailAlloc_192_, 17, v_divMod_179_);
lean_ctor_set(v_reuseFailAlloc_192_, 18, v_toIntIds_180_);
lean_ctor_set(v_reuseFailAlloc_192_, 19, v_toIntInfos_181_);
lean_ctor_set(v_reuseFailAlloc_192_, 20, v_toIntTermMap_182_);
lean_ctor_set(v_reuseFailAlloc_192_, 21, v_toIntVarMap_183_);
lean_ctor_set(v_reuseFailAlloc_192_, 22, v_nonlinearOccs_185_);
lean_ctor_set_uint8(v_reuseFailAlloc_192_, sizeof(void*)*23, v_caseSplits_176_);
lean_ctor_set_uint8(v_reuseFailAlloc_192_, sizeof(void*)*23 + 1, v_usedCommRing_184_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_194_, lean_object* v_vals_195_, lean_object* v_i_196_, lean_object* v_k_197_){
_start:
{
lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_198_ = lean_array_get_size(v_keys_194_);
v___x_199_ = lean_nat_dec_lt(v_i_196_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; 
lean_dec(v_i_196_);
v___x_200_ = lean_box(0);
return v___x_200_;
}
else
{
lean_object* v_k_x27_201_; uint8_t v___x_202_; 
v_k_x27_201_ = lean_array_fget_borrowed(v_keys_194_, v_i_196_);
v___x_202_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_197_, v_k_x27_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = lean_nat_add(v_i_196_, v___x_203_);
lean_dec(v_i_196_);
v_i_196_ = v___x_204_;
goto _start;
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_array_fget_borrowed(v_vals_195_, v_i_196_);
lean_dec(v_i_196_);
lean_inc(v___x_206_);
v___x_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_208_, lean_object* v_vals_209_, lean_object* v_i_210_, lean_object* v_k_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(v_keys_208_, v_vals_209_, v_i_210_, v_k_211_);
lean_dec_ref(v_k_211_);
lean_dec_ref(v_vals_209_);
lean_dec_ref(v_keys_208_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(lean_object* v_x_213_, size_t v_x_214_, lean_object* v_x_215_){
_start:
{
if (lean_obj_tag(v_x_213_) == 0)
{
lean_object* v_es_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_237_; 
v_es_216_ = lean_ctor_get(v_x_213_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v_x_213_);
if (v_isSharedCheck_237_ == 0)
{
v___x_218_ = v_x_213_;
v_isShared_219_ = v_isSharedCheck_237_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_es_216_);
lean_dec(v_x_213_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_237_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; size_t v___x_221_; size_t v___x_222_; size_t v___x_223_; lean_object* v_j_224_; lean_object* v___x_225_; 
v___x_220_ = lean_box(2);
v___x_221_ = ((size_t)5ULL);
v___x_222_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1);
v___x_223_ = lean_usize_land(v_x_214_, v___x_222_);
v_j_224_ = lean_usize_to_nat(v___x_223_);
v___x_225_ = lean_array_get(v___x_220_, v_es_216_, v_j_224_);
lean_dec(v_j_224_);
lean_dec_ref(v_es_216_);
switch(lean_obj_tag(v___x_225_))
{
case 0:
{
lean_object* v_key_226_; lean_object* v_val_227_; uint8_t v___x_228_; 
v_key_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_key_226_);
v_val_227_ = lean_ctor_get(v___x_225_, 1);
lean_inc(v_val_227_);
lean_dec_ref(v___x_225_);
v___x_228_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_215_, v_key_226_);
lean_dec(v_key_226_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; 
lean_dec(v_val_227_);
lean_del_object(v___x_218_);
v___x_229_ = lean_box(0);
return v___x_229_;
}
else
{
lean_object* v___x_231_; 
if (v_isShared_219_ == 0)
{
lean_ctor_set_tag(v___x_218_, 1);
lean_ctor_set(v___x_218_, 0, v_val_227_);
v___x_231_ = v___x_218_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_val_227_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
case 1:
{
lean_object* v_node_233_; size_t v___x_234_; 
lean_del_object(v___x_218_);
v_node_233_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_node_233_);
lean_dec_ref(v___x_225_);
v___x_234_ = lean_usize_shift_right(v_x_214_, v___x_221_);
v_x_213_ = v_node_233_;
v_x_214_ = v___x_234_;
goto _start;
}
default: 
{
lean_object* v___x_236_; 
lean_del_object(v___x_218_);
v___x_236_ = lean_box(0);
return v___x_236_;
}
}
}
}
else
{
lean_object* v_ks_238_; lean_object* v_vs_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_ks_238_ = lean_ctor_get(v_x_213_, 0);
lean_inc_ref(v_ks_238_);
v_vs_239_ = lean_ctor_get(v_x_213_, 1);
lean_inc_ref(v_vs_239_);
lean_dec_ref(v_x_213_);
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(v_ks_238_, v_vs_239_, v___x_240_, v_x_215_);
lean_dec_ref(v_vs_239_);
lean_dec_ref(v_ks_238_);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg___boxed(lean_object* v_x_242_, lean_object* v_x_243_, lean_object* v_x_244_){
_start:
{
size_t v_x_6699__boxed_245_; lean_object* v_res_246_; 
v_x_6699__boxed_245_ = lean_unbox_usize(v_x_243_);
lean_dec(v_x_243_);
v_res_246_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(v_x_242_, v_x_6699__boxed_245_, v_x_244_);
lean_dec_ref(v_x_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
uint64_t v___x_249_; size_t v___x_250_; lean_object* v___x_251_; 
v___x_249_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_248_);
v___x_250_ = lean_uint64_to_usize(v___x_249_);
v___x_251_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(v_x_247_, v___x_250_, v_x_248_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg___boxed(lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(v_x_252_, v_x_253_);
lean_dec_ref(v_x_253_);
return v_res_254_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_unsigned_to_nat(1u);
v___x_261_ = l_Lean_Level_ofNat(v___x_260_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = lean_box(0);
v___x_263_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3);
v___x_264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4);
v___x_266_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2));
v___x_267_ = l_Lean_mkConst(v___x_266_, v___x_265_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = l_Lean_Int_mkType;
v___x_269_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5);
v___x_270_ = l_Lean_Expr_app___override(v___x_269_, v___x_268_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(lean_object* v_e_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_272_, v_a_280_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_336_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_336_ == 0)
{
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_336_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_336_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v_natToIntMap_288_; lean_object* v___x_289_; 
v_natToIntMap_288_ = lean_ctor_get(v_a_284_, 4);
lean_inc_ref(v_natToIntMap_288_);
lean_dec(v_a_284_);
v___x_289_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(v_natToIntMap_288_, v_e_271_);
if (lean_obj_tag(v___x_289_) == 1)
{
lean_object* v_val_290_; lean_object* v___x_292_; 
lean_dec_ref(v_e_271_);
v_val_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_val_290_);
lean_dec_ref(v___x_289_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v_val_290_);
v___x_292_ = v___x_286_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_val_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec(v___x_289_);
lean_del_object(v___x_286_);
lean_inc_ref(v_e_271_);
v___x_294_ = l_Lean_mkIntNatCast(v_e_271_);
v___x_295_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_294_, v_a_277_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___f_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc_n(v_a_296_, 2);
lean_dec_ref(v___x_295_);
v___x_297_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6);
v___x_298_ = l_Lean_Expr_app___override(v___x_297_, v_a_296_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_a_296_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
lean_inc_ref(v___x_299_);
lean_inc_ref(v_e_271_);
v___f_300_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___lam__0), 3, 2);
lean_closure_set(v___f_300_, 0, v_e_271_);
lean_closure_set(v___f_300_, 1, v___x_299_);
v___x_301_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_302_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_301_, v___f_300_, v_a_272_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v___x_303_; 
lean_dec_ref(v___x_302_);
v___x_303_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_301_, v_e_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; 
v_unused_311_ = lean_ctor_get(v___x_303_, 0);
lean_dec(v_unused_311_);
v___x_305_ = v___x_303_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_dec(v___x_303_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_299_);
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_299_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_dec_ref(v___x_299_);
v_a_312_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_303_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_303_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec_ref(v___x_299_);
lean_dec_ref(v_e_271_);
v_a_320_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_302_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_302_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec_ref(v_e_271_);
v_a_328_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_295_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_295_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_dec_ref(v_e_271_);
v_a_337_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_283_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_283_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___boxed(lean_object* v_e_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec(v_a_346_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0(lean_object* v_00_u03b2_358_, lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(v_x_359_, v_x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___boxed(lean_object* v_00_u03b2_362_, lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0(v_00_u03b2_362_, v_x_363_, v_x_364_);
lean_dec_ref(v_x_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1(lean_object* v_00_u03b2_366_, lean_object* v_x_367_, lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1___redArg(v_x_367_, v_x_368_, v_x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0(lean_object* v_00_u03b2_371_, lean_object* v_x_372_, size_t v_x_373_, lean_object* v_x_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(v_x_372_, v_x_373_, v_x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_376_, lean_object* v_x_377_, lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
size_t v_x_6963__boxed_380_; lean_object* v_res_381_; 
v_x_6963__boxed_380_ = lean_unbox_usize(v_x_378_);
lean_dec(v_x_378_);
v_res_381_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0(v_00_u03b2_376_, v_x_377_, v_x_6963__boxed_380_, v_x_379_);
lean_dec_ref(v_x_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2(lean_object* v_00_u03b2_382_, lean_object* v_x_383_, size_t v_x_384_, size_t v_x_385_, lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_x_383_, v_x_384_, v_x_385_, v_x_386_, v_x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_389_, lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v_x_392_, lean_object* v_x_393_, lean_object* v_x_394_){
_start:
{
size_t v_x_6974__boxed_395_; size_t v_x_6975__boxed_396_; lean_object* v_res_397_; 
v_x_6974__boxed_395_ = lean_unbox_usize(v_x_391_);
lean_dec(v_x_391_);
v_x_6975__boxed_396_ = lean_unbox_usize(v_x_392_);
lean_dec(v_x_392_);
v_res_397_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2(v_00_u03b2_389_, v_x_390_, v_x_6974__boxed_395_, v_x_6975__boxed_396_, v_x_393_, v_x_394_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_398_, lean_object* v_keys_399_, lean_object* v_vals_400_, lean_object* v_heq_401_, lean_object* v_i_402_, lean_object* v_k_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(v_keys_399_, v_vals_400_, v_i_402_, v_k_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_405_, lean_object* v_keys_406_, lean_object* v_vals_407_, lean_object* v_heq_408_, lean_object* v_i_409_, lean_object* v_k_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1(v_00_u03b2_405_, v_keys_406_, v_vals_407_, v_heq_408_, v_i_409_, v_k_410_);
lean_dec_ref(v_k_410_);
lean_dec_ref(v_vals_407_);
lean_dec_ref(v_keys_406_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_412_, lean_object* v_n_413_, lean_object* v_k_414_, lean_object* v_v_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4___redArg(v_n_413_, v_k_414_, v_v_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_417_, size_t v_depth_418_, lean_object* v_keys_419_, lean_object* v_vals_420_, lean_object* v_heq_421_, lean_object* v_i_422_, lean_object* v_entries_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(v_depth_418_, v_keys_419_, v_vals_420_, v_i_422_, v_entries_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_425_, lean_object* v_depth_426_, lean_object* v_keys_427_, lean_object* v_vals_428_, lean_object* v_heq_429_, lean_object* v_i_430_, lean_object* v_entries_431_){
_start:
{
size_t v_depth_boxed_432_; lean_object* v_res_433_; 
v_depth_boxed_432_ = lean_unbox_usize(v_depth_426_);
lean_dec(v_depth_426_);
v_res_433_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5(v_00_u03b2_425_, v_depth_boxed_432_, v_keys_427_, v_vals_428_, v_heq_429_, v_i_430_, v_entries_431_);
lean_dec_ref(v_vals_428_);
lean_dec_ref(v_keys_427_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_434_, lean_object* v_x_435_, lean_object* v_x_436_, lean_object* v_x_437_, lean_object* v_x_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5___redArg(v_x_435_, v_x_436_, v_x_437_, v_x_438_);
return v___x_439_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4);
v___x_444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__1));
v___x_445_ = l_Lean_mkConst(v___x_444_, v___x_443_);
return v___x_445_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = l_Lean_Int_mkType;
v___x_447_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2);
v___x_448_ = l_Lean_Expr_app___override(v___x_447_, v___x_446_);
return v___x_448_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte(void){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__0(lean_object* v_a_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = lean_nat_to_int(v_a_450_);
return v___x_451_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_452_, lean_object* v_i_453_, lean_object* v_k_454_){
_start:
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = lean_array_get_size(v_keys_452_);
v___x_456_ = lean_nat_dec_lt(v_i_453_, v___x_455_);
if (v___x_456_ == 0)
{
lean_dec(v_i_453_);
return v___x_456_;
}
else
{
lean_object* v_k_x27_457_; uint8_t v___x_458_; 
v_k_x27_457_ = lean_array_fget_borrowed(v_keys_452_, v_i_453_);
v___x_458_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_454_, v_k_x27_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_unsigned_to_nat(1u);
v___x_460_ = lean_nat_add(v_i_453_, v___x_459_);
lean_dec(v_i_453_);
v_i_453_ = v___x_460_;
goto _start;
}
else
{
lean_dec(v_i_453_);
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_462_, lean_object* v_i_463_, lean_object* v_k_464_){
_start:
{
uint8_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(v_keys_462_, v_i_463_, v_k_464_);
lean_dec_ref(v_k_464_);
lean_dec_ref(v_keys_462_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(lean_object* v_x_467_, size_t v_x_468_, lean_object* v_x_469_){
_start:
{
if (lean_obj_tag(v_x_467_) == 0)
{
lean_object* v_es_470_; lean_object* v___x_471_; size_t v___x_472_; size_t v___x_473_; size_t v___x_474_; lean_object* v_j_475_; lean_object* v___x_476_; 
v_es_470_ = lean_ctor_get(v_x_467_, 0);
v___x_471_ = lean_box(2);
v___x_472_ = ((size_t)5ULL);
v___x_473_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__1);
v___x_474_ = lean_usize_land(v_x_468_, v___x_473_);
v_j_475_ = lean_usize_to_nat(v___x_474_);
v___x_476_ = lean_array_get_borrowed(v___x_471_, v_es_470_, v_j_475_);
lean_dec(v_j_475_);
switch(lean_obj_tag(v___x_476_))
{
case 0:
{
lean_object* v_key_477_; uint8_t v___x_478_; 
v_key_477_ = lean_ctor_get(v___x_476_, 0);
v___x_478_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_469_, v_key_477_);
return v___x_478_;
}
case 1:
{
lean_object* v_node_479_; size_t v___x_480_; 
v_node_479_ = lean_ctor_get(v___x_476_, 0);
v___x_480_ = lean_usize_shift_right(v_x_468_, v___x_472_);
v_x_467_ = v_node_479_;
v_x_468_ = v___x_480_;
goto _start;
}
default: 
{
uint8_t v___x_482_; 
v___x_482_ = 0;
return v___x_482_;
}
}
}
else
{
lean_object* v_ks_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v_ks_483_ = lean_ctor_get(v_x_467_, 0);
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(v_ks_483_, v___x_484_, v_x_469_);
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg___boxed(lean_object* v_x_486_, lean_object* v_x_487_, lean_object* v_x_488_){
_start:
{
size_t v_x_61908__boxed_489_; uint8_t v_res_490_; lean_object* v_r_491_; 
v_x_61908__boxed_489_ = lean_unbox_usize(v_x_487_);
lean_dec(v_x_487_);
v_res_490_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(v_x_486_, v_x_61908__boxed_489_, v_x_488_);
lean_dec_ref(v_x_488_);
lean_dec_ref(v_x_486_);
v_r_491_ = lean_box(v_res_490_);
return v_r_491_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(lean_object* v_x_492_, lean_object* v_x_493_){
_start:
{
uint64_t v___x_494_; size_t v___x_495_; uint8_t v___x_496_; 
v___x_494_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_493_);
v___x_495_ = lean_uint64_to_usize(v___x_494_);
v___x_496_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(v_x_492_, v___x_495_, v_x_493_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg___boxed(lean_object* v_x_497_, lean_object* v_x_498_){
_start:
{
uint8_t v_res_499_; lean_object* v_r_500_; 
v_res_499_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_x_497_, v_x_498_);
lean_dec_ref(v_x_498_);
lean_dec_ref(v_x_497_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = lean_box(0);
v___x_544_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24));
v___x_545_ = l_Lean_mkConst(v___x_544_, v___x_543_);
return v___x_545_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = lean_box(0);
v___x_552_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27));
v___x_553_ = l_Lean_mkConst(v___x_552_, v___x_551_);
return v___x_553_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_box(0);
v___x_560_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30));
v___x_561_ = l_Lean_mkConst(v___x_560_, v___x_559_);
return v___x_561_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = lean_box(0);
v___x_568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33));
v___x_569_ = l_Lean_mkConst(v___x_568_, v___x_567_);
return v___x_569_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_box(0);
v___x_576_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36));
v___x_577_ = l_Lean_mkConst(v___x_576_, v___x_575_);
return v___x_577_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = lean_box(0);
v___x_584_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39));
v___x_585_ = l_Lean_mkConst(v___x_584_, v___x_583_);
return v___x_585_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_box(0);
v___x_589_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__41));
v___x_590_ = l_Lean_mkConst(v___x_589_, v___x_588_);
return v___x_590_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_box(0);
v___x_597_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44));
v___x_598_ = l_Lean_mkConst(v___x_597_, v___x_596_);
return v___x_598_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = lean_box(0);
v___x_604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47));
v___x_605_ = l_Lean_mkConst(v___x_604_, v___x_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(lean_object* v_e_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v___x_618_; 
lean_inc_ref(v_e_606_);
v___x_618_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_606_, v_a_614_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref(v___x_618_);
v___x_620_ = l_Lean_Expr_cleanupAnnotations(v_a_619_);
v___x_621_ = l_Lean_Expr_isApp(v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
lean_dec_ref(v___x_620_);
v___x_622_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
return v___x_622_;
}
else
{
lean_object* v_arg_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v_arg_623_ = lean_ctor_get(v___x_620_, 1);
lean_inc_ref(v_arg_623_);
v___x_624_ = l_Lean_Expr_appFnCleanup___redArg(v___x_620_);
v___x_625_ = l_Lean_Expr_isApp(v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
lean_dec_ref(v___x_624_);
lean_dec_ref(v_arg_623_);
v___x_626_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
return v___x_626_;
}
else
{
lean_object* v_arg_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_arg_627_ = lean_ctor_get(v___x_624_, 1);
lean_inc_ref(v_arg_627_);
v___x_628_ = l_Lean_Expr_appFnCleanup___redArg(v___x_624_);
v___x_629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2));
v___x_630_ = l_Lean_Expr_isConstOf(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
uint8_t v___x_631_; 
v___x_631_ = l_Lean_Expr_isApp(v___x_628_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; 
lean_dec_ref(v___x_628_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
v___x_632_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
return v___x_632_;
}
else
{
lean_object* v_arg_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_arg_633_ = lean_ctor_get(v___x_628_, 1);
lean_inc_ref(v_arg_633_);
v___x_634_ = l_Lean_Expr_appFnCleanup___redArg(v___x_628_);
v___x_635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5));
v___x_636_ = l_Lean_Expr_isConstOf(v___x_634_, v___x_635_);
if (v___x_636_ == 0)
{
uint8_t v___x_637_; 
v___x_637_ = l_Lean_Expr_isApp(v___x_634_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
lean_dec_ref(v___x_634_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
v___x_638_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
return v___x_638_;
}
else
{
lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_639_ = l_Lean_Expr_appFnCleanup___redArg(v___x_634_);
v___x_640_ = l_Lean_Expr_isApp(v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
lean_dec_ref(v___x_639_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
v___x_641_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
return v___x_641_;
}
else
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = l_Lean_Expr_appFnCleanup___redArg(v___x_639_);
v___x_643_ = l_Lean_Expr_isApp(v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
lean_dec_ref(v___x_642_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
v___x_644_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
return v___x_644_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_645_ = l_Lean_Expr_appFnCleanup___redArg(v___x_642_);
v___x_646_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8));
v___x_647_ = l_Lean_Expr_isConstOf(v___x_645_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11));
v___x_649_ = l_Lean_Expr_isConstOf(v___x_645_, v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14));
v___x_651_ = l_Lean_Expr_isConstOf(v___x_645_, v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17));
v___x_653_ = l_Lean_Expr_isConstOf(v___x_645_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20));
v___x_655_ = l_Lean_Expr_isConstOf(v___x_645_, v___x_654_);
lean_dec_ref(v___x_645_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
v___x_656_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
return v___x_656_;
}
else
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_633_, v_a_614_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; uint8_t v___x_659_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref(v___x_657_);
v___x_659_ = lean_unbox(v_a_658_);
lean_dec(v_a_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
v___x_660_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
return v___x_660_;
}
else
{
lean_object* v___x_661_; 
lean_dec_ref(v_e_606_);
lean_inc_ref(v_arg_627_);
v___x_661_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_627_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v_fst_663_; lean_object* v_snd_664_; lean_object* v___x_665_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref(v___x_661_);
v_fst_663_ = lean_ctor_get(v_a_662_, 0);
lean_inc(v_fst_663_);
v_snd_664_ = lean_ctor_get(v_a_662_, 1);
lean_inc(v_snd_664_);
lean_dec(v_a_662_);
lean_inc_ref(v_arg_623_);
v___x_665_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_623_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_685_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_685_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_685_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_685_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v_fst_670_; lean_object* v_snd_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_684_; 
v_fst_670_ = lean_ctor_get(v_a_666_, 0);
v_snd_671_ = lean_ctor_get(v_a_666_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v_a_666_);
if (v_isSharedCheck_684_ == 0)
{
v___x_673_ = v_a_666_;
v_isShared_674_ = v_isSharedCheck_684_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_snd_671_);
lean_inc(v_fst_670_);
lean_dec(v_a_666_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_684_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_675_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25);
lean_inc(v_fst_670_);
lean_inc(v_fst_663_);
v___x_676_ = l_Lean_mkApp6(v___x_675_, v_arg_627_, v_arg_623_, v_fst_663_, v_fst_670_, v_snd_664_, v_snd_671_);
v___x_677_ = l_Lean_mkIntAdd(v_fst_663_, v_fst_670_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v___x_676_);
lean_ctor_set(v___x_673_, 0, v___x_677_);
v___x_679_ = v___x_673_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v___x_676_);
v___x_679_ = v_reuseFailAlloc_683_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_681_; 
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_679_);
v___x_681_ = v___x_668_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
else
{
lean_dec(v_snd_664_);
lean_dec(v_fst_663_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
return v___x_665_;
}
}
else
{
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
return v___x_661_;
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
lean_dec_ref(v_e_606_);
v_a_686_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_657_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_657_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
else
{
lean_object* v___x_694_; 
lean_dec_ref(v___x_645_);
v___x_694_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_633_, v_a_614_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; uint8_t v___x_696_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref(v___x_694_);
v___x_696_ = lean_unbox(v_a_695_);
lean_dec(v_a_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; 
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
v___x_697_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
return v___x_697_;
}
else
{
lean_object* v___x_698_; 
lean_dec_ref(v_e_606_);
lean_inc_ref(v_arg_627_);
v___x_698_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_627_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v_fst_700_; lean_object* v_snd_701_; lean_object* v___x_702_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref(v___x_698_);
v_fst_700_ = lean_ctor_get(v_a_699_, 0);
lean_inc(v_fst_700_);
v_snd_701_ = lean_ctor_get(v_a_699_, 1);
lean_inc(v_snd_701_);
lean_dec(v_a_699_);
lean_inc_ref(v_arg_623_);
v___x_702_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_623_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_722_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_722_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_722_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_722_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v_fst_707_; lean_object* v_snd_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_721_; 
v_fst_707_ = lean_ctor_get(v_a_703_, 0);
v_snd_708_ = lean_ctor_get(v_a_703_, 1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_a_703_);
if (v_isSharedCheck_721_ == 0)
{
v___x_710_ = v_a_703_;
v_isShared_711_ = v_isSharedCheck_721_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_snd_708_);
lean_inc(v_fst_707_);
lean_dec(v_a_703_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_721_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_712_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28);
lean_inc(v_fst_707_);
lean_inc(v_fst_700_);
v___x_713_ = l_Lean_mkApp6(v___x_712_, v_arg_627_, v_arg_623_, v_fst_700_, v_fst_707_, v_snd_701_, v_snd_708_);
v___x_714_ = l_Lean_mkIntMul(v_fst_700_, v_fst_707_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v___x_713_);
lean_ctor_set(v___x_710_, 0, v___x_714_);
v___x_716_ = v___x_710_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_713_);
v___x_716_ = v_reuseFailAlloc_720_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_716_);
v___x_718_ = v___x_705_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
else
{
lean_dec(v_snd_701_);
lean_dec(v_fst_700_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
return v___x_702_;
}
}
else
{
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
return v___x_698_;
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
lean_dec_ref(v_e_606_);
v_a_723_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_694_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_694_);
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
}
else
{
lean_object* v___x_731_; 
lean_dec_ref(v___x_645_);
v___x_731_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_633_, v_a_614_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; uint8_t v___x_733_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref(v___x_731_);
v___x_733_ = lean_unbox(v_a_732_);
lean_dec(v_a_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; 
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
v___x_734_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
return v___x_734_;
}
else
{
lean_object* v___x_735_; 
lean_dec_ref(v_e_606_);
lean_inc_ref(v_arg_627_);
v___x_735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_627_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v_fst_737_; lean_object* v_snd_738_; lean_object* v___x_739_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref(v___x_735_);
v_fst_737_ = lean_ctor_get(v_a_736_, 0);
lean_inc(v_fst_737_);
v_snd_738_ = lean_ctor_get(v_a_736_, 1);
lean_inc(v_snd_738_);
lean_dec(v_a_736_);
lean_inc_ref(v_arg_623_);
v___x_739_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_623_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_759_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_759_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_759_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_759_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v_fst_744_; lean_object* v_snd_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_758_; 
v_fst_744_ = lean_ctor_get(v_a_740_, 0);
v_snd_745_ = lean_ctor_get(v_a_740_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v_a_740_);
if (v_isSharedCheck_758_ == 0)
{
v___x_747_ = v_a_740_;
v_isShared_748_ = v_isSharedCheck_758_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_snd_745_);
lean_inc(v_fst_744_);
lean_dec(v_a_740_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_758_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_749_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31);
lean_inc(v_fst_744_);
lean_inc(v_fst_737_);
v___x_750_ = l_Lean_mkApp6(v___x_749_, v_arg_627_, v_arg_623_, v_fst_737_, v_fst_744_, v_snd_738_, v_snd_745_);
v___x_751_ = l_Lean_mkIntDiv(v_fst_737_, v_fst_744_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v___x_750_);
lean_ctor_set(v___x_747_, 0, v___x_751_);
v___x_753_ = v___x_747_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v___x_750_);
v___x_753_ = v_reuseFailAlloc_757_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_753_);
v___x_755_ = v___x_742_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
else
{
lean_dec(v_snd_738_);
lean_dec(v_fst_737_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
return v___x_739_;
}
}
else
{
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
return v___x_735_;
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
lean_dec_ref(v_e_606_);
v_a_760_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_731_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_731_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
else
{
lean_object* v___x_768_; 
lean_dec_ref(v___x_645_);
v___x_768_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_633_, v_a_614_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; uint8_t v___x_770_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref(v___x_768_);
v___x_770_ = lean_unbox(v_a_769_);
lean_dec(v_a_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; 
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
v___x_771_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
return v___x_771_;
}
else
{
lean_object* v___x_772_; 
lean_dec_ref(v_e_606_);
lean_inc_ref(v_arg_627_);
v___x_772_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_627_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v_fst_774_; lean_object* v_snd_775_; lean_object* v___x_776_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref(v___x_772_);
v_fst_774_ = lean_ctor_get(v_a_773_, 0);
lean_inc(v_fst_774_);
v_snd_775_ = lean_ctor_get(v_a_773_, 1);
lean_inc(v_snd_775_);
lean_dec(v_a_773_);
lean_inc_ref(v_arg_623_);
v___x_776_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_623_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_796_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_796_ == 0)
{
v___x_779_ = v___x_776_;
v_isShared_780_ = v_isSharedCheck_796_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_796_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v_fst_781_; lean_object* v_snd_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_795_; 
v_fst_781_ = lean_ctor_get(v_a_777_, 0);
v_snd_782_ = lean_ctor_get(v_a_777_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v_a_777_);
if (v_isSharedCheck_795_ == 0)
{
v___x_784_ = v_a_777_;
v_isShared_785_ = v_isSharedCheck_795_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_snd_782_);
lean_inc(v_fst_781_);
lean_dec(v_a_777_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_795_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_786_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34);
lean_inc(v_fst_781_);
lean_inc(v_fst_774_);
v___x_787_ = l_Lean_mkApp6(v___x_786_, v_arg_627_, v_arg_623_, v_fst_774_, v_fst_781_, v_snd_775_, v_snd_782_);
v___x_788_ = l_Lean_mkIntMod(v_fst_774_, v_fst_781_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v___x_787_);
lean_ctor_set(v___x_784_, 0, v___x_788_);
v___x_790_ = v___x_784_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___x_787_);
v___x_790_ = v_reuseFailAlloc_794_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_792_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_790_);
v___x_792_ = v___x_779_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
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
}
else
{
lean_dec(v_snd_775_);
lean_dec(v_fst_774_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
return v___x_776_;
}
}
else
{
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
return v___x_772_;
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
lean_dec_ref(v_e_606_);
v_a_797_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_768_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_768_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
else
{
lean_object* v___x_805_; 
lean_dec_ref(v___x_645_);
v___x_805_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_633_, v_a_614_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; uint8_t v___x_807_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref(v___x_805_);
v___x_807_ = lean_unbox(v_a_806_);
lean_dec(v_a_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; 
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
v___x_808_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
return v___x_808_;
}
else
{
lean_object* v___x_809_; 
lean_dec_ref(v_e_606_);
lean_inc_ref(v_arg_627_);
v___x_809_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_627_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_829_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_829_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_829_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_829_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v_fst_814_; lean_object* v_snd_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_828_; 
v_fst_814_ = lean_ctor_get(v_a_810_, 0);
v_snd_815_ = lean_ctor_get(v_a_810_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v_a_810_);
if (v_isSharedCheck_828_ == 0)
{
v___x_817_ = v_a_810_;
v_isShared_818_ = v_isSharedCheck_828_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_snd_815_);
lean_inc(v_fst_814_);
lean_dec(v_a_810_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_828_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_819_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37);
lean_inc(v_fst_814_);
lean_inc_ref(v_arg_623_);
v___x_820_ = l_Lean_mkApp4(v___x_819_, v_arg_627_, v_arg_623_, v_fst_814_, v_snd_815_);
v___x_821_ = l_Lean_mkIntPowNat(v_fst_814_, v_arg_623_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v___x_820_);
lean_ctor_set(v___x_817_, 0, v___x_821_);
v___x_823_ = v___x_817_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_821_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v___x_820_);
v___x_823_ = v_reuseFailAlloc_827_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_825_; 
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_823_);
v___x_825_ = v___x_812_;
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
}
}
}
else
{
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
return v___x_809_;
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
lean_dec_ref(v_e_606_);
v_a_830_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_805_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_805_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_838_; 
lean_dec_ref(v___x_634_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
v___x_838_ = l_Lean_Meta_getNatValue_x3f(v_e_606_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_853_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_853_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_853_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_853_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
if (lean_obj_tag(v_a_839_) == 1)
{
lean_object* v_val_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v_val_843_ = lean_ctor_get(v_a_839_, 0);
lean_inc(v_val_843_);
lean_dec_ref(v_a_839_);
v___x_844_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40);
v___x_845_ = l_Lean_Expr_app___override(v___x_844_, v_e_606_);
v___x_846_ = lean_nat_to_int(v_val_843_);
v___x_847_ = l_Lean_mkIntLit(v___x_846_);
lean_dec(v___x_846_);
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v___x_845_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_848_);
v___x_850_ = v___x_841_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
else
{
lean_object* v___x_852_; 
lean_del_object(v___x_841_);
lean_dec(v_a_839_);
v___x_852_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
return v___x_852_;
}
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec_ref(v_e_606_);
v_a_854_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_838_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_838_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
lean_dec_ref(v___x_628_);
v___x_862_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42);
lean_inc_ref(v_arg_627_);
v___x_863_ = l_Lean_Expr_app___override(v___x_862_, v_arg_627_);
v___x_864_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_863_, v_a_612_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_866_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref(v___x_864_);
lean_inc_ref(v_arg_623_);
v___x_866_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt_x3f(v_arg_623_, v_a_865_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_920_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_920_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_920_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_920_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
if (lean_obj_tag(v_a_867_) == 1)
{
lean_object* v_val_871_; lean_object* v_fst_872_; lean_object* v_snd_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_885_; 
lean_dec_ref(v_e_606_);
v_val_871_ = lean_ctor_get(v_a_867_, 0);
lean_inc(v_val_871_);
lean_dec_ref(v_a_867_);
v_fst_872_ = lean_ctor_get(v_val_871_, 0);
v_snd_873_ = lean_ctor_get(v_val_871_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_val_871_);
if (v_isSharedCheck_885_ == 0)
{
v___x_875_ = v_val_871_;
v_isShared_876_ = v_isSharedCheck_885_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_snd_873_);
lean_inc(v_fst_872_);
lean_dec(v_val_871_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_885_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_877_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45);
lean_inc(v_fst_872_);
v___x_878_ = l_Lean_mkApp4(v___x_877_, v_arg_627_, v_arg_623_, v_fst_872_, v_snd_873_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 1, v___x_878_);
v___x_880_ = v___x_875_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_fst_872_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v___x_878_);
v___x_880_ = v_reuseFailAlloc_884_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_882_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_880_);
v___x_882_ = v___x_869_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_object* v___x_886_; 
lean_del_object(v___x_869_);
lean_dec(v_a_867_);
v___x_886_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_607_, v_a_615_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_888_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref(v___x_886_);
lean_inc_ref(v_e_606_);
v___x_888_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v_natToIntMap_890_; uint8_t v___x_891_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
v_natToIntMap_890_ = lean_ctor_get(v_a_887_, 4);
lean_inc_ref(v_natToIntMap_890_);
lean_dec(v_a_887_);
v___x_891_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_natToIntMap_890_, v_e_606_);
lean_dec_ref(v_e_606_);
lean_dec_ref(v_natToIntMap_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec_ref(v___x_888_);
v___x_892_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48);
v___x_893_ = l_Lean_mkAppB(v___x_892_, v_arg_627_, v_arg_623_);
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = l_Lean_Meta_Grind_pushNewFact(v___x_893_, v___x_894_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v___x_895_, 0);
lean_dec(v_unused_903_);
v___x_897_ = v___x_895_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_dec(v___x_895_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v_a_889_);
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_889_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec(v_a_889_);
v_a_904_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_895_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_895_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_dec(v_a_889_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
return v___x_888_;
}
}
else
{
lean_dec(v_a_887_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
lean_dec_ref(v_e_606_);
return v___x_888_;
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
lean_dec_ref(v_e_606_);
v_a_912_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_886_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_886_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
lean_dec_ref(v_e_606_);
v_a_921_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_866_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_866_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_623_);
lean_dec_ref(v_e_606_);
v_a_929_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_864_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_864_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v_e_606_);
v_a_937_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_618_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_618_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___boxed(lean_object* v_e_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_e_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1(lean_object* v_00_u03b2_958_, lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
uint8_t v___x_961_; 
v___x_961_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_x_959_, v_x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___boxed(lean_object* v_00_u03b2_962_, lean_object* v_x_963_, lean_object* v_x_964_){
_start:
{
uint8_t v_res_965_; lean_object* v_r_966_; 
v_res_965_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1(v_00_u03b2_962_, v_x_963_, v_x_964_);
lean_dec_ref(v_x_964_);
lean_dec_ref(v_x_963_);
v_r_966_ = lean_box(v_res_965_);
return v_r_966_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1(lean_object* v_00_u03b2_967_, lean_object* v_x_968_, size_t v_x_969_, lean_object* v_x_970_){
_start:
{
uint8_t v___x_971_; 
v___x_971_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(v_x_968_, v_x_969_, v_x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___boxed(lean_object* v_00_u03b2_972_, lean_object* v_x_973_, lean_object* v_x_974_, lean_object* v_x_975_){
_start:
{
size_t v_x_62967__boxed_976_; uint8_t v_res_977_; lean_object* v_r_978_; 
v_x_62967__boxed_976_ = lean_unbox_usize(v_x_974_);
lean_dec(v_x_974_);
v_res_977_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1(v_00_u03b2_972_, v_x_973_, v_x_62967__boxed_976_, v_x_975_);
lean_dec_ref(v_x_975_);
lean_dec_ref(v_x_973_);
v_r_978_ = lean_box(v_res_977_);
return v_r_978_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_979_, lean_object* v_keys_980_, lean_object* v_vals_981_, lean_object* v_heq_982_, lean_object* v_i_983_, lean_object* v_k_984_){
_start:
{
uint8_t v___x_985_; 
v___x_985_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(v_keys_980_, v_i_983_, v_k_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_986_, lean_object* v_keys_987_, lean_object* v_vals_988_, lean_object* v_heq_989_, lean_object* v_i_990_, lean_object* v_k_991_){
_start:
{
uint8_t v_res_992_; lean_object* v_r_993_; 
v_res_992_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2(v_00_u03b2_986_, v_keys_987_, v_vals_988_, v_heq_989_, v_i_990_, v_k_991_);
lean_dec_ref(v_k_991_);
lean_dec_ref(v_vals_988_);
lean_dec_ref(v_keys_987_);
v_r_993_ = lean_box(v_res_992_);
return v_r_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v_fst_1008_; lean_object* v_snd_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1033_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref(v___x_1006_);
v_fst_1008_ = lean_ctor_get(v_a_1007_, 0);
v_snd_1009_ = lean_ctor_get(v_a_1007_, 1);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_a_1007_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1011_ = v_a_1007_;
v_isShared_1012_ = v_isSharedCheck_1033_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_snd_1009_);
lean_inc(v_fst_1008_);
lean_dec(v_a_1007_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1033_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_Meta_Sym_shareCommon___redArg(v_fst_1008_, v_a_1000_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1024_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1024_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1024_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v_a_1014_);
v___x_1019_ = v___x_1011_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1014_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_snd_1009_);
v___x_1019_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1019_);
v___x_1021_ = v___x_1016_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_del_object(v___x_1011_);
lean_dec(v_snd_1009_);
v_a_1025_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1013_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1013_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
else
{
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt___boxed(lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec(v_a_1035_);
return v_res_1046_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_unsigned_to_nat(1u);
v___x_1056_ = lean_nat_to_int(v___x_1055_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5);
v___x_1058_ = lean_int_neg(v___x_1057_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = lean_nat_to_int(v___x_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7);
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(lean_object* v_e_1063_, lean_object* v_x_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = l_Lean_Expr_cleanupAnnotations(v_e_1063_);
v___x_1080_ = l_Lean_Expr_isApp(v___x_1079_);
if (v___x_1080_ == 0)
{
lean_dec_ref(v___x_1079_);
lean_dec(v_x_1064_);
goto v___jp_1076_;
}
else
{
lean_object* v_arg_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v_arg_1081_ = lean_ctor_get(v___x_1079_, 1);
lean_inc_ref(v_arg_1081_);
v___x_1082_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1079_);
v___x_1083_ = l_Lean_Expr_isApp(v___x_1082_);
if (v___x_1083_ == 0)
{
lean_dec_ref(v___x_1082_);
lean_dec_ref(v_arg_1081_);
lean_dec(v_x_1064_);
goto v___jp_1076_;
}
else
{
lean_object* v_arg_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v_arg_1084_ = lean_ctor_get(v___x_1082_, 1);
lean_inc_ref(v_arg_1084_);
v___x_1085_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1082_);
v___x_1086_ = l_Lean_Expr_isApp(v___x_1085_);
if (v___x_1086_ == 0)
{
lean_dec_ref(v___x_1085_);
lean_dec_ref(v_arg_1084_);
lean_dec_ref(v_arg_1081_);
lean_dec(v_x_1064_);
goto v___jp_1076_;
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1087_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1085_);
v___x_1088_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2));
v___x_1089_ = l_Lean_Expr_isConstOf(v___x_1087_, v___x_1088_);
lean_dec_ref(v___x_1087_);
if (v___x_1089_ == 0)
{
lean_dec_ref(v_arg_1084_);
lean_dec_ref(v_arg_1081_);
lean_dec(v_x_1064_);
goto v___jp_1076_;
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1090_ = l_Lean_Expr_cleanupAnnotations(v_arg_1084_);
v___x_1091_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4));
v___x_1092_ = l_Lean_Expr_isConstOf(v___x_1090_, v___x_1091_);
lean_dec_ref(v___x_1090_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_dec_ref(v_arg_1081_);
lean_dec(v_x_1064_);
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5));
v___x_1096_ = l_Lean_Expr_isAppOf(v_arg_1081_, v___x_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1065_, v_a_1073_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1123_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1123_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1123_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_natDef_1102_; uint8_t v___x_1103_; 
v_natDef_1102_ = lean_ctor_get(v_a_1098_, 5);
lean_inc_ref(v_natDef_1102_);
lean_dec(v_a_1098_);
v___x_1103_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_natDef_1102_, v_arg_1081_);
lean_dec_ref(v_natDef_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
lean_del_object(v___x_1100_);
lean_inc_ref(v_arg_1081_);
v___x_1104_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_arg_1081_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
lean_dec_ref(v___x_1104_);
v___x_1105_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6);
v___x_1106_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8);
v___x_1107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v_x_1064_);
lean_ctor_set(v___x_1107_, 2, v___x_1106_);
v___x_1108_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1108_, 0, v_arg_1081_);
v___x_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
lean_inc(v_a_1074_);
lean_inc_ref(v_a_1073_);
lean_inc(v_a_1072_);
lean_inc_ref(v_a_1071_);
lean_inc(v_a_1070_);
lean_inc_ref(v_a_1069_);
lean_inc(v_a_1068_);
lean_inc_ref(v_a_1067_);
lean_inc(v_a_1066_);
lean_inc(v_a_1065_);
v___x_1110_ = lean_grind_cutsat_assert_le(v___x_1109_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
return v___x_1110_;
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec_ref(v_arg_1081_);
lean_dec(v_x_1064_);
v_a_1111_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1104_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1104_);
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
lean_object* v___x_1119_; lean_object* v___x_1121_; 
lean_dec_ref(v_arg_1081_);
lean_dec(v_x_1064_);
v___x_1119_ = lean_box(0);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1119_);
v___x_1121_ = v___x_1100_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
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
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec_ref(v_arg_1081_);
lean_dec(v_x_1064_);
v_a_1124_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1097_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1097_);
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
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_dec_ref(v_arg_1081_);
lean_dec(v_x_1064_);
v___x_1132_ = lean_box(0);
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
return v___x_1133_;
}
}
}
}
}
}
v___jp_1076_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_box(0);
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___boxed(lean_object* v_e_1134_, lean_object* v_x_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(v_e_1134_, v_x_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec(v_a_1136_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(lean_object* v_e_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1149_, v_a_1150_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1163_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1163_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1163_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v_natToIntMap_1157_; uint8_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v_natToIntMap_1157_ = lean_ctor_get(v_a_1153_, 4);
lean_inc_ref(v_natToIntMap_1157_);
lean_dec(v_a_1153_);
v___x_1158_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_natToIntMap_1157_, v_e_1148_);
lean_dec_ref(v_natToIntMap_1157_);
v___x_1159_ = lean_box(v___x_1158_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1159_);
v___x_1161_ = v___x_1155_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
v_a_1164_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1152_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1152_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg___boxed(lean_object* v_e_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(v_e_1172_, v_a_1173_, v_a_1174_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_e_1172_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm(lean_object* v_e_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(v_e_1177_, v_a_1178_, v_a_1186_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___boxed(lean_object* v_e_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm(v_e_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_);
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
lean_dec_ref(v_e_1190_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(lean_object* v_e_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v___x_1213_; 
lean_inc_ref(v_e_1203_);
v___x_1213_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1203_, v_a_1205_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___y_1216_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref(v___x_1213_);
v___x_1248_ = l_Lean_Expr_cleanupAnnotations(v_a_1214_);
v___x_1249_ = l_Lean_Expr_isApp(v___x_1248_);
if (v___x_1249_ == 0)
{
lean_dec_ref(v___x_1248_);
v___y_1216_ = v_a_1205_;
goto v___jp_1215_;
}
else
{
lean_object* v_arg_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v_arg_1250_ = lean_ctor_get(v___x_1248_, 1);
lean_inc_ref(v_arg_1250_);
v___x_1251_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1248_);
v___x_1252_ = l_Lean_Expr_isApp(v___x_1251_);
if (v___x_1252_ == 0)
{
lean_dec_ref(v___x_1251_);
lean_dec_ref(v_arg_1250_);
v___y_1216_ = v_a_1205_;
goto v___jp_1215_;
}
else
{
lean_object* v_arg_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v_arg_1253_ = lean_ctor_get(v___x_1251_, 1);
lean_inc_ref(v_arg_1253_);
v___x_1254_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1251_);
v___x_1255_ = l_Lean_Expr_isApp(v___x_1254_);
if (v___x_1255_ == 0)
{
lean_dec_ref(v___x_1254_);
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_arg_1250_);
v___y_1216_ = v_a_1205_;
goto v___jp_1215_;
}
else
{
lean_object* v_arg_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v_arg_1256_ = lean_ctor_get(v___x_1254_, 1);
lean_inc_ref(v_arg_1256_);
v___x_1257_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1254_);
v___x_1258_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5));
v___x_1259_ = l_Lean_Expr_isConstOf(v___x_1257_, v___x_1258_);
if (v___x_1259_ == 0)
{
uint8_t v___x_1260_; 
v___x_1260_ = l_Lean_Expr_isApp(v___x_1257_);
if (v___x_1260_ == 0)
{
lean_dec_ref(v___x_1257_);
lean_dec_ref(v_arg_1256_);
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_arg_1250_);
v___y_1216_ = v_a_1205_;
goto v___jp_1215_;
}
else
{
lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1257_);
v___x_1262_ = l_Lean_Expr_isApp(v___x_1261_);
if (v___x_1262_ == 0)
{
lean_dec_ref(v___x_1261_);
lean_dec_ref(v_arg_1256_);
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_arg_1250_);
v___y_1216_ = v_a_1205_;
goto v___jp_1215_;
}
else
{
lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1261_);
v___x_1264_ = l_Lean_Expr_isApp(v___x_1263_);
if (v___x_1264_ == 0)
{
lean_dec_ref(v___x_1263_);
lean_dec_ref(v_arg_1256_);
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_arg_1250_);
v___y_1216_ = v_a_1205_;
goto v___jp_1215_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1265_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1263_);
v___x_1266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8));
v___x_1267_ = l_Lean_Expr_isConstOf(v___x_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11));
v___x_1269_ = l_Lean_Expr_isConstOf(v___x_1265_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1270_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14));
v___x_1271_ = l_Lean_Expr_isConstOf(v___x_1265_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17));
v___x_1273_ = l_Lean_Expr_isConstOf(v___x_1265_, v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20));
v___x_1275_ = l_Lean_Expr_isConstOf(v___x_1265_, v___x_1274_);
lean_dec_ref(v___x_1265_);
if (v___x_1275_ == 0)
{
lean_dec_ref(v_arg_1256_);
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_arg_1250_);
v___y_1216_ = v_a_1205_;
goto v___jp_1215_;
}
else
{
lean_object* v___x_1276_; 
lean_dec_ref(v_e_1203_);
v___x_1276_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1256_, v_a_1205_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; uint8_t v___x_1278_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
v___x_1278_ = lean_unbox(v_a_1277_);
lean_dec(v_a_1277_);
if (v___x_1278_ == 0)
{
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_arg_1250_);
return v___x_1276_;
}
else
{
lean_object* v___x_1279_; 
lean_dec_ref(v___x_1276_);
v___x_1279_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_arg_1253_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; uint8_t v___x_1281_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
v___x_1281_ = lean_unbox(v_a_1280_);
lean_dec(v_a_1280_);
if (v___x_1281_ == 0)
{
lean_dec_ref(v_arg_1250_);
return v___x_1279_;
}
else
{
lean_dec_ref(v___x_1279_);
v_e_1203_ = v_arg_1250_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1250_);
return v___x_1279_;
}
}
}
else
{
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_arg_1250_);
return v___x_1276_;
}
}
}
else
{
lean_object* v___x_1283_; 
lean_dec_ref(v___x_1265_);
lean_dec_ref(v_e_1203_);
v___x_1283_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1256_, v_a_1205_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; uint8_t v___x_1285_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
v___x_1285_ = lean_unbox(v_a_1284_);
lean_dec(v_a_1284_);
if (v___x_1285_ == 0)
{
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_arg_1250_);
return v___x_1283_;
}
else
{
lean_object* v___x_1286_; 
lean_dec_ref(v___x_1283_);
v___x_1286_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_arg_1253_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; uint8_t v___x_1288_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
v___x_1288_ = lean_unbox(v_a_1287_);
lean_dec(v_a_1287_);
if (v___x_1288_ == 0)
{
lean_dec_ref(v_arg_1250_);
return v___x_1286_;
}
else
{
lean_dec_ref(v___x_1286_);
v_e_1203_ = v_arg_1250_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1250_);
return v___x_1286_;
}
}
}
else
{
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_arg_1250_);
return v___x_1283_;
}
}
}
else
{
lean_object* v___x_1290_; 
lean_dec_ref(v___x_1265_);
lean_dec_ref(v_e_1203_);
v___x_1290_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_1256_, v_a_1205_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; uint8_t v___x_1292_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
v___x_1292_ = lean_unbox(v_a_1291_);
lean_dec(v_a_1291_);
if (v___x_1292_ == 0)
{
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_arg_1250_);
return v___x_1290_;
}
else
{
lean_object* v___x_1293_; 
lean_dec_ref(v___x_1290_);
v___x_1293_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_arg_1253_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; uint8_t v___x_1295_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
v___x_1295_ = lean_unbox(v_a_1294_);
lean_dec(v_a_1294_);
if (v___x_1295_ == 0)
{
lean_dec_ref(v_arg_1250_);
return v___x_1293_;
}
else
{
lean_dec_ref(v___x_1293_);
v_e_1203_ = v_arg_1250_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1250_);
return v___x_1293_;
}
}
}
else
{
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_arg_1250_);
return v___x_1290_;
}
}
}
else
{
lean_object* v___x_1297_; 
lean_dec_ref(v___x_1265_);
lean_dec_ref(v_arg_1250_);
lean_dec_ref(v_e_1203_);
v___x_1297_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_1256_, v_a_1205_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; uint8_t v___x_1299_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
v___x_1299_ = lean_unbox(v_a_1298_);
lean_dec(v_a_1298_);
if (v___x_1299_ == 0)
{
lean_dec_ref(v_arg_1253_);
return v___x_1297_;
}
else
{
lean_dec_ref(v___x_1297_);
v_e_1203_ = v_arg_1253_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1253_);
return v___x_1297_;
}
}
}
else
{
lean_object* v___x_1301_; 
lean_dec_ref(v___x_1265_);
lean_dec_ref(v_arg_1250_);
lean_dec_ref(v_e_1203_);
v___x_1301_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_1256_, v_a_1205_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; uint8_t v___x_1303_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
v___x_1303_ = lean_unbox(v_a_1302_);
lean_dec(v_a_1302_);
if (v___x_1303_ == 0)
{
lean_dec_ref(v_arg_1253_);
return v___x_1301_;
}
else
{
lean_dec_ref(v___x_1301_);
v_e_1203_ = v_arg_1253_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1253_);
return v___x_1301_;
}
}
}
}
}
}
else
{
lean_object* v___x_1305_; 
lean_dec_ref(v___x_1257_);
lean_dec_ref(v_arg_1256_);
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_arg_1250_);
v___x_1305_ = l_Lean_Meta_getIntValue_x3f(v_e_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1322_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1322_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1322_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
if (lean_obj_tag(v_a_1306_) == 1)
{
lean_object* v_val_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
v_val_1310_ = lean_ctor_get(v_a_1306_, 0);
lean_inc(v_val_1310_);
lean_dec_ref(v_a_1306_);
v___x_1311_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7);
v___x_1312_ = lean_int_dec_le(v___x_1311_, v_val_1310_);
lean_dec(v_val_1310_);
v___x_1313_ = lean_box(v___x_1312_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1313_);
v___x_1315_ = v___x_1308_;
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
else
{
uint8_t v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1320_; 
lean_dec(v_a_1306_);
v___x_1317_ = 0;
v___x_1318_ = lean_box(v___x_1317_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1318_);
v___x_1320_ = v___x_1308_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
v_a_1323_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1305_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1305_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
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
}
}
}
v___jp_1215_:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1203_, v___y_1216_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1239_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1220_ = v___x_1217_;
v_isShared_1221_ = v_isSharedCheck_1239_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1217_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1239_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = l_Lean_Expr_cleanupAnnotations(v_a_1218_);
v___x_1223_ = l_Lean_Expr_isApp(v___x_1222_);
if (v___x_1223_ == 0)
{
lean_dec_ref(v___x_1222_);
lean_del_object(v___x_1220_);
goto v___jp_1209_;
}
else
{
lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1222_);
v___x_1225_ = l_Lean_Expr_isApp(v___x_1224_);
if (v___x_1225_ == 0)
{
lean_dec_ref(v___x_1224_);
lean_del_object(v___x_1220_);
goto v___jp_1209_;
}
else
{
lean_object* v_arg_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v_arg_1226_ = lean_ctor_get(v___x_1224_, 1);
lean_inc_ref(v_arg_1226_);
v___x_1227_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1224_);
v___x_1228_ = l_Lean_Expr_isApp(v___x_1227_);
if (v___x_1228_ == 0)
{
lean_dec_ref(v___x_1227_);
lean_dec_ref(v_arg_1226_);
lean_del_object(v___x_1220_);
goto v___jp_1209_;
}
else
{
lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1229_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1227_);
v___x_1230_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2));
v___x_1231_ = l_Lean_Expr_isConstOf(v___x_1229_, v___x_1230_);
lean_dec_ref(v___x_1229_);
if (v___x_1231_ == 0)
{
lean_dec_ref(v_arg_1226_);
lean_del_object(v___x_1220_);
goto v___jp_1209_;
}
else
{
lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1232_ = l_Lean_Expr_cleanupAnnotations(v_arg_1226_);
v___x_1233_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4));
v___x_1234_ = l_Lean_Expr_isConstOf(v___x_1232_, v___x_1233_);
lean_dec_ref(v___x_1232_);
v___x_1235_ = lean_box(v___x_1234_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1235_);
v___x_1237_ = v___x_1220_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
v_a_1240_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1217_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1217_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec_ref(v_e_1203_);
v_a_1331_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1213_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1213_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
v___jp_1209_:
{
uint8_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1210_ = 0;
v___x_1211_ = lean_box(v___x_1210_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg___boxed(lean_object* v_e_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_e_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0(lean_object* v_msg_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___f_1353_; lean_object* v___x_5805__overap_1354_; lean_object* v___x_1355_; 
v___f_1353_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___closed__0));
v___x_5805__overap_1354_ = lean_panic_fn_borrowed(v___f_1353_, v_msg_1347_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
v___x_1355_ = lean_apply_5(v___x_5805__overap_1354_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, lean_box(0));
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___boxed(lean_object* v_msg_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0(v_msg_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
return v_res_1362_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__2));
v___x_1367_ = lean_unsigned_to_nat(43u);
v___x_1368_ = lean_unsigned_to_nat(154u);
v___x_1369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__1));
v___x_1370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__0));
v___x_1371_ = l_mkPanicMessageWithDecl(v___x_1370_, v___x_1369_, v___x_1368_, v___x_1367_, v___x_1366_);
return v___x_1371_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6));
v___x_1380_ = l_Lean_mkConst(v___x_1379_, v___x_1378_);
return v___x_1380_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = lean_box(0);
v___x_1387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9));
v___x_1388_ = l_Lean_mkConst(v___x_1387_, v___x_1386_);
return v___x_1388_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1394_ = lean_box(0);
v___x_1395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12));
v___x_1396_ = l_Lean_mkConst(v___x_1395_, v___x_1394_);
return v___x_1396_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = lean_box(0);
v___x_1403_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15));
v___x_1404_ = l_Lean_mkConst(v___x_1403_, v___x_1402_);
return v___x_1404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = lean_box(0);
v___x_1411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18));
v___x_1412_ = l_Lean_mkConst(v___x_1411_, v___x_1410_);
return v___x_1412_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = lean_box(0);
v___x_1419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21));
v___x_1420_ = l_Lean_mkConst(v___x_1419_, v___x_1418_);
return v___x_1420_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = lean_box(0);
v___x_1427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24));
v___x_1428_ = l_Lean_mkConst(v___x_1427_, v___x_1426_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(lean_object* v_e_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___x_1442_; 
lean_inc_ref(v_e_1429_);
v___x_1442_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1429_, v_a_1431_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1567_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1567_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1567_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1473_ = l_Lean_Expr_cleanupAnnotations(v_a_1443_);
v___x_1474_ = l_Lean_Expr_isApp(v___x_1473_);
if (v___x_1474_ == 0)
{
lean_dec_ref(v___x_1473_);
lean_del_object(v___x_1445_);
v___y_1448_ = v_a_1430_;
v___y_1449_ = v_a_1431_;
v___y_1450_ = v_a_1432_;
v___y_1451_ = v_a_1433_;
goto v___jp_1447_;
}
else
{
lean_object* v_arg_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v_arg_1475_ = lean_ctor_get(v___x_1473_, 1);
lean_inc_ref(v_arg_1475_);
v___x_1476_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1473_);
v___x_1477_ = l_Lean_Expr_isApp(v___x_1476_);
if (v___x_1477_ == 0)
{
lean_dec_ref(v___x_1476_);
lean_dec_ref(v_arg_1475_);
lean_del_object(v___x_1445_);
v___y_1448_ = v_a_1430_;
v___y_1449_ = v_a_1431_;
v___y_1450_ = v_a_1432_;
v___y_1451_ = v_a_1433_;
goto v___jp_1447_;
}
else
{
lean_object* v_arg_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v_arg_1478_ = lean_ctor_get(v___x_1476_, 1);
lean_inc_ref(v_arg_1478_);
v___x_1479_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1476_);
v___x_1480_ = l_Lean_Expr_isApp(v___x_1479_);
if (v___x_1480_ == 0)
{
lean_dec_ref(v___x_1479_);
lean_dec_ref(v_arg_1478_);
lean_dec_ref(v_arg_1475_);
lean_del_object(v___x_1445_);
v___y_1448_ = v_a_1430_;
v___y_1449_ = v_a_1431_;
v___y_1450_ = v_a_1432_;
v___y_1451_ = v_a_1433_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; 
v___x_1481_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1479_);
v___x_1482_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5));
v___x_1483_ = l_Lean_Expr_isConstOf(v___x_1481_, v___x_1482_);
if (v___x_1483_ == 0)
{
uint8_t v___x_1484_; 
lean_del_object(v___x_1445_);
v___x_1484_ = l_Lean_Expr_isApp(v___x_1481_);
if (v___x_1484_ == 0)
{
lean_dec_ref(v___x_1481_);
lean_dec_ref(v_arg_1478_);
lean_dec_ref(v_arg_1475_);
v___y_1448_ = v_a_1430_;
v___y_1449_ = v_a_1431_;
v___y_1450_ = v_a_1432_;
v___y_1451_ = v_a_1433_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1485_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1481_);
v___x_1486_ = l_Lean_Expr_isApp(v___x_1485_);
if (v___x_1486_ == 0)
{
lean_dec_ref(v___x_1485_);
lean_dec_ref(v_arg_1478_);
lean_dec_ref(v_arg_1475_);
v___y_1448_ = v_a_1430_;
v___y_1449_ = v_a_1431_;
v___y_1450_ = v_a_1432_;
v___y_1451_ = v_a_1433_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1485_);
v___x_1488_ = l_Lean_Expr_isApp(v___x_1487_);
if (v___x_1488_ == 0)
{
lean_dec_ref(v___x_1487_);
lean_dec_ref(v_arg_1478_);
lean_dec_ref(v_arg_1475_);
v___y_1448_ = v_a_1430_;
v___y_1449_ = v_a_1431_;
v___y_1450_ = v_a_1432_;
v___y_1451_ = v_a_1433_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1489_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1487_);
v___x_1490_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8));
v___x_1491_ = l_Lean_Expr_isConstOf(v___x_1489_, v___x_1490_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1492_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11));
v___x_1493_ = l_Lean_Expr_isConstOf(v___x_1489_, v___x_1492_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___x_1494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14));
v___x_1495_ = l_Lean_Expr_isConstOf(v___x_1489_, v___x_1494_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; uint8_t v___x_1497_; 
v___x_1496_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17));
v___x_1497_ = l_Lean_Expr_isConstOf(v___x_1489_, v___x_1496_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___x_1498_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20));
v___x_1499_ = l_Lean_Expr_isConstOf(v___x_1489_, v___x_1498_);
lean_dec_ref(v___x_1489_);
if (v___x_1499_ == 0)
{
lean_dec_ref(v_arg_1478_);
lean_dec_ref(v_arg_1475_);
v___y_1448_ = v_a_1430_;
v___y_1449_ = v_a_1431_;
v___y_1450_ = v_a_1432_;
v___y_1451_ = v_a_1433_;
goto v___jp_1447_;
}
else
{
lean_object* v___x_1500_; 
lean_dec_ref(v_e_1429_);
lean_inc_ref(v_arg_1478_);
v___x_1500_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1478_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1502_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref(v___x_1500_);
lean_inc_ref(v_arg_1475_);
v___x_1502_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1475_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1512_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1512_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1512_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1507_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10);
v___x_1508_ = l_Lean_mkApp4(v___x_1507_, v_arg_1478_, v_arg_1475_, v_a_1501_, v_a_1503_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1508_);
v___x_1510_ = v___x_1505_;
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
else
{
lean_dec(v_a_1501_);
lean_dec_ref(v_arg_1478_);
lean_dec_ref(v_arg_1475_);
return v___x_1502_;
}
}
else
{
lean_dec_ref(v_arg_1478_);
lean_dec_ref(v_arg_1475_);
return v___x_1500_;
}
}
}
else
{
lean_object* v___x_1513_; 
lean_dec_ref(v___x_1489_);
lean_dec_ref(v_e_1429_);
lean_inc_ref(v_arg_1478_);
v___x_1513_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1478_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1515_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref(v___x_1513_);
lean_inc_ref(v_arg_1475_);
v___x_1515_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1475_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1525_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1525_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1525_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1520_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13);
v___x_1521_ = l_Lean_mkApp4(v___x_1520_, v_arg_1478_, v_arg_1475_, v_a_1514_, v_a_1516_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v___x_1521_);
v___x_1523_ = v___x_1518_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
else
{
lean_dec(v_a_1514_);
lean_dec_ref(v_arg_1478_);
lean_dec_ref(v_arg_1475_);
return v___x_1515_;
}
}
else
{
lean_dec_ref(v_arg_1478_);
lean_dec_ref(v_arg_1475_);
return v___x_1513_;
}
}
}
else
{
lean_object* v___x_1526_; 
lean_dec_ref(v___x_1489_);
lean_dec_ref(v_e_1429_);
lean_inc_ref(v_arg_1478_);
v___x_1526_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1478_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1528_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref(v___x_1526_);
lean_inc_ref(v_arg_1475_);
v___x_1528_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1475_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1538_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1531_ = v___x_1528_;
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1533_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16);
v___x_1534_ = l_Lean_mkApp4(v___x_1533_, v_arg_1478_, v_arg_1475_, v_a_1527_, v_a_1529_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1534_);
v___x_1536_ = v___x_1531_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
else
{
lean_dec(v_a_1527_);
lean_dec_ref(v_arg_1478_);
lean_dec_ref(v_arg_1475_);
return v___x_1528_;
}
}
else
{
lean_dec_ref(v_arg_1478_);
lean_dec_ref(v_arg_1475_);
return v___x_1526_;
}
}
}
else
{
lean_object* v___x_1539_; 
lean_dec_ref(v___x_1489_);
lean_dec_ref(v_e_1429_);
lean_inc_ref(v_arg_1478_);
v___x_1539_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1478_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1549_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1549_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1549_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1544_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19);
v___x_1545_ = l_Lean_mkApp3(v___x_1544_, v_arg_1478_, v_arg_1475_, v_a_1540_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1545_);
v___x_1547_ = v___x_1542_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
else
{
lean_dec_ref(v_arg_1478_);
lean_dec_ref(v_arg_1475_);
return v___x_1539_;
}
}
}
else
{
lean_object* v___x_1550_; 
lean_dec_ref(v___x_1489_);
lean_dec_ref(v_e_1429_);
lean_inc_ref(v_arg_1478_);
v___x_1550_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1478_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1560_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1560_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1560_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1555_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22);
v___x_1556_ = l_Lean_mkApp3(v___x_1555_, v_arg_1478_, v_arg_1475_, v_a_1551_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1556_);
v___x_1558_ = v___x_1553_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
else
{
lean_dec_ref(v_arg_1478_);
lean_dec_ref(v_arg_1475_);
return v___x_1550_;
}
}
}
}
}
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
lean_dec_ref(v___x_1481_);
lean_dec_ref(v_arg_1478_);
lean_dec_ref(v_arg_1475_);
v___x_1561_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25);
v___x_1562_ = l_Lean_eagerReflBoolTrue;
v___x_1563_ = l_Lean_mkAppB(v___x_1561_, v_e_1429_, v___x_1562_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1563_);
v___x_1565_ = v___x_1445_;
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
}
v___jp_1447_:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1429_, v___y_1449_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1472_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1472_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1472_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1457_ = l_Lean_Expr_cleanupAnnotations(v_a_1453_);
v___x_1458_ = l_Lean_Expr_isApp(v___x_1457_);
if (v___x_1458_ == 0)
{
lean_dec_ref(v___x_1457_);
lean_del_object(v___x_1455_);
v___y_1436_ = v___y_1448_;
v___y_1437_ = v___y_1449_;
v___y_1438_ = v___y_1450_;
v___y_1439_ = v___y_1451_;
goto v___jp_1435_;
}
else
{
lean_object* v_arg_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v_arg_1459_ = lean_ctor_get(v___x_1457_, 1);
lean_inc_ref(v_arg_1459_);
v___x_1460_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1457_);
v___x_1461_ = l_Lean_Expr_isApp(v___x_1460_);
if (v___x_1461_ == 0)
{
lean_dec_ref(v___x_1460_);
lean_dec_ref(v_arg_1459_);
lean_del_object(v___x_1455_);
v___y_1436_ = v___y_1448_;
v___y_1437_ = v___y_1449_;
v___y_1438_ = v___y_1450_;
v___y_1439_ = v___y_1451_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1462_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1460_);
v___x_1463_ = l_Lean_Expr_isApp(v___x_1462_);
if (v___x_1463_ == 0)
{
lean_dec_ref(v___x_1462_);
lean_dec_ref(v_arg_1459_);
lean_del_object(v___x_1455_);
v___y_1436_ = v___y_1448_;
v___y_1437_ = v___y_1449_;
v___y_1438_ = v___y_1450_;
v___y_1439_ = v___y_1451_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v___x_1464_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1462_);
v___x_1465_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2));
v___x_1466_ = l_Lean_Expr_isConstOf(v___x_1464_, v___x_1465_);
lean_dec_ref(v___x_1464_);
if (v___x_1466_ == 0)
{
lean_dec_ref(v_arg_1459_);
lean_del_object(v___x_1455_);
v___y_1436_ = v___y_1448_;
v___y_1437_ = v___y_1449_;
v___y_1438_ = v___y_1450_;
v___y_1439_ = v___y_1451_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1467_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7);
v___x_1468_ = l_Lean_Expr_app___override(v___x_1467_, v_arg_1459_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v___x_1468_);
v___x_1470_ = v___x_1455_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
}
}
else
{
return v___x_1452_;
}
}
}
}
else
{
lean_dec_ref(v_e_1429_);
return v___x_1442_;
}
v___jp_1435_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3);
v___x_1441_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0(v___x_1440_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
return v___x_1441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___boxed(lean_object* v_e_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_e_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(lean_object* v_e_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___x_1581_; 
lean_inc_ref(v_e_1575_);
v___x_1581_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_e_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1609_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1609_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1609_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
uint8_t v___x_1586_; 
v___x_1586_ = lean_unbox(v_a_1582_);
lean_dec(v_a_1582_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1589_; 
lean_dec_ref(v_e_1575_);
v___x_1587_ = lean_box(0);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1587_);
v___x_1589_ = v___x_1584_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
else
{
lean_object* v___x_1591_; 
lean_del_object(v___x_1584_);
v___x_1591_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_e_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1600_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1594_ = v___x_1591_;
v_isShared_1595_ = v_isSharedCheck_1600_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1591_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1600_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1596_, 0, v_a_1592_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1596_);
v___x_1598_ = v___x_1594_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_a_1601_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1591_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1591_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec_ref(v_e_1575_);
v_a_1610_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1581_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1581_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg___boxed(lean_object* v_e_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(v_e_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_);
lean_dec(v_a_1622_);
lean_dec_ref(v_a_1621_);
lean_dec(v_a_1620_);
lean_dec_ref(v_a_1619_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f(lean_object* v_e_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(v_e_1625_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___boxed(lean_object* v_e_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f(v_e_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec(v_a_1639_);
return v_res_1650_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1656_ = lean_box(0);
v___x_1657_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1));
v___x_1658_ = l_Lean_mkConst(v___x_1657_, v___x_1656_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(lean_object* v_e_1659_, lean_object* v_x_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1672_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2));
v___x_1673_ = l_Lean_Expr_isAppOf(v_e_1659_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5));
v___x_1675_ = l_Lean_Expr_isAppOf(v_e_1659_, v___x_1674_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; 
lean_inc_ref(v_e_1659_);
v___x_1676_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(v_e_1659_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1700_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1679_ = v___x_1676_;
v_isShared_1680_ = v_isSharedCheck_1700_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1676_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1700_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
if (lean_obj_tag(v_a_1677_) == 1)
{
lean_object* v_val_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1695_; 
lean_del_object(v___x_1679_);
v_val_1681_ = lean_ctor_get(v_a_1677_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_a_1677_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1683_ = v_a_1677_;
v_isShared_1684_ = v_isSharedCheck_1695_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_val_1681_);
lean_dec(v_a_1677_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1695_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1685_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2);
v___x_1686_ = l_Lean_mkAppB(v___x_1685_, v_e_1659_, v_val_1681_);
v___x_1687_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6);
v___x_1688_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8);
v___x_1689_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1687_);
lean_ctor_set(v___x_1689_, 1, v_x_1660_);
lean_ctor_set(v___x_1689_, 2, v___x_1688_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set_tag(v___x_1683_, 4);
lean_ctor_set(v___x_1683_, 0, v___x_1686_);
v___x_1691_ = v___x_1683_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1686_);
v___x_1691_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1689_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
lean_inc(v_a_1670_);
lean_inc_ref(v_a_1669_);
lean_inc(v_a_1668_);
lean_inc_ref(v_a_1667_);
lean_inc(v_a_1666_);
lean_inc_ref(v_a_1665_);
lean_inc(v_a_1664_);
lean_inc_ref(v_a_1663_);
lean_inc(v_a_1662_);
lean_inc(v_a_1661_);
v___x_1693_ = lean_grind_cutsat_assert_le(v___x_1692_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
return v___x_1693_;
}
}
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
lean_dec(v_a_1677_);
lean_dec(v_x_1660_);
lean_dec_ref(v_e_1659_);
v___x_1696_ = lean_box(0);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 0, v___x_1696_);
v___x_1698_ = v___x_1679_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_dec(v_x_1660_);
lean_dec_ref(v_e_1659_);
v_a_1701_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1676_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1676_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_dec(v_x_1660_);
lean_dec_ref(v_e_1659_);
v___x_1709_ = lean_box(0);
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
return v___x_1710_;
}
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_dec(v_x_1660_);
lean_dec_ref(v_e_1659_);
v___x_1711_ = lean_box(0);
v___x_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
return v___x_1712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___boxed(lean_object* v_e_1713_, lean_object* v_x_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(v_e_1713_, v_x_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1721_);
lean_dec(v_a_1720_);
lean_dec_ref(v_a_1719_);
lean_dec(v_a_1718_);
lean_dec_ref(v_a_1717_);
lean_dec(v_a_1716_);
lean_dec(v_a_1715_);
return v_res_1726_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
}
#ifdef __cplusplus
}
#endif
