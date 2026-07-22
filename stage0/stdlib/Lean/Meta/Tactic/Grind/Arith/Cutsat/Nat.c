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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_mkIntNatCast(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0;
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
lean_object* v_ks_5_; lean_object* v_vs_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_32_; 
v_ks_5_ = lean_ctor_get(v_x_1_, 0);
v_vs_6_ = lean_ctor_get(v_x_1_, 1);
v_isSharedCheck_32_ = !lean_is_exclusive(v_x_1_);
if (v_isSharedCheck_32_ == 0)
{
v___x_8_ = v_x_1_;
v_isShared_9_ = v_isSharedCheck_32_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_vs_6_);
lean_inc(v_ks_5_);
lean_dec(v_x_1_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_32_;
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
lean_object* v_k_x27_17_; size_t v___x_18_; size_t v___x_19_; uint8_t v___x_20_; 
v_k_x27_17_ = lean_array_fget_borrowed(v_ks_5_, v_x_2_);
v___x_18_ = lean_ptr_addr(v_x_3_);
v___x_19_ = lean_ptr_addr(v_k_x27_17_);
v___x_20_ = lean_usize_dec_eq(v___x_18_, v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_22_; 
if (v_isShared_9_ == 0)
{
v___x_22_ = v___x_8_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_ks_5_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v_vs_6_);
v___x_22_ = v_reuseFailAlloc_26_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = lean_nat_add(v_x_2_, v___x_23_);
lean_dec(v_x_2_);
v_x_1_ = v___x_22_;
v_x_2_ = v___x_24_;
goto _start;
}
}
else
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_30_; 
v___x_27_ = lean_array_fset(v_ks_5_, v_x_2_, v_x_3_);
v___x_28_ = lean_array_fset(v_vs_6_, v_x_2_, v_x_4_);
lean_dec(v_x_2_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v___x_28_);
lean_ctor_set(v___x_8_, 0, v___x_27_);
v___x_30_ = v___x_8_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___x_27_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v___x_28_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4___redArg(lean_object* v_n_33_, lean_object* v_k_34_, lean_object* v_v_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5___redArg(v_n_33_, v___x_36_, v_k_34_, v_v_35_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(lean_object* v_x_39_, size_t v_x_40_, size_t v_x_41_, lean_object* v_x_42_, lean_object* v_x_43_){
_start:
{
if (lean_obj_tag(v_x_39_) == 0)
{
lean_object* v_es_44_; size_t v___x_45_; size_t v___x_46_; lean_object* v_j_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v_es_44_ = lean_ctor_get(v_x_39_, 0);
v___x_45_ = ((size_t)31ULL);
v___x_46_ = lean_usize_land(v_x_40_, v___x_45_);
v_j_47_ = lean_usize_to_nat(v___x_46_);
v___x_48_ = lean_array_get_size(v_es_44_);
v___x_49_ = lean_nat_dec_lt(v_j_47_, v___x_48_);
if (v___x_49_ == 0)
{
lean_dec(v_j_47_);
lean_dec(v_x_43_);
lean_dec_ref(v_x_42_);
return v_x_39_;
}
else
{
lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_90_; 
lean_inc_ref(v_es_44_);
v_isSharedCheck_90_ = !lean_is_exclusive(v_x_39_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; 
v_unused_91_ = lean_ctor_get(v_x_39_, 0);
lean_dec(v_unused_91_);
v___x_51_ = v_x_39_;
v_isShared_52_ = v_isSharedCheck_90_;
goto v_resetjp_50_;
}
else
{
lean_dec(v_x_39_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_90_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v_v_53_; lean_object* v___x_54_; lean_object* v_xs_x27_55_; lean_object* v___y_57_; 
v_v_53_ = lean_array_fget(v_es_44_, v_j_47_);
v___x_54_ = lean_box(0);
v_xs_x27_55_ = lean_array_fset(v_es_44_, v_j_47_, v___x_54_);
switch(lean_obj_tag(v_v_53_))
{
case 0:
{
lean_object* v_key_62_; lean_object* v_val_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_75_; 
v_key_62_ = lean_ctor_get(v_v_53_, 0);
v_val_63_ = lean_ctor_get(v_v_53_, 1);
v_isSharedCheck_75_ = !lean_is_exclusive(v_v_53_);
if (v_isSharedCheck_75_ == 0)
{
v___x_65_ = v_v_53_;
v_isShared_66_ = v_isSharedCheck_75_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_val_63_);
lean_inc(v_key_62_);
lean_dec(v_v_53_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_75_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
size_t v___x_67_; size_t v___x_68_; uint8_t v___x_69_; 
v___x_67_ = lean_ptr_addr(v_x_42_);
v___x_68_ = lean_ptr_addr(v_key_62_);
v___x_69_ = lean_usize_dec_eq(v___x_67_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_del_object(v___x_65_);
v___x_70_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_62_, v_val_63_, v_x_42_, v_x_43_);
v___x_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
v___y_57_ = v___x_71_;
goto v___jp_56_;
}
else
{
lean_object* v___x_73_; 
lean_dec(v_val_63_);
lean_dec(v_key_62_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v_x_43_);
lean_ctor_set(v___x_65_, 0, v_x_42_);
v___x_73_ = v___x_65_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_x_42_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_x_43_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
v___y_57_ = v___x_73_;
goto v___jp_56_;
}
}
}
}
case 1:
{
lean_object* v_node_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_88_; 
v_node_76_ = lean_ctor_get(v_v_53_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v_v_53_);
if (v_isSharedCheck_88_ == 0)
{
v___x_78_ = v_v_53_;
v_isShared_79_ = v_isSharedCheck_88_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_node_76_);
lean_dec(v_v_53_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_88_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
size_t v___x_80_; size_t v___x_81_; size_t v___x_82_; size_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_80_ = ((size_t)5ULL);
v___x_81_ = lean_usize_shift_right(v_x_40_, v___x_80_);
v___x_82_ = ((size_t)1ULL);
v___x_83_ = lean_usize_add(v_x_41_, v___x_82_);
v___x_84_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_node_76_, v___x_81_, v___x_83_, v_x_42_, v_x_43_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 0, v___x_84_);
v___x_86_ = v___x_78_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_84_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
v___y_57_ = v___x_86_;
goto v___jp_56_;
}
}
}
default: 
{
lean_object* v___x_89_; 
v___x_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_89_, 0, v_x_42_);
lean_ctor_set(v___x_89_, 1, v_x_43_);
v___y_57_ = v___x_89_;
goto v___jp_56_;
}
}
v___jp_56_:
{
lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_58_ = lean_array_fset(v_xs_x27_55_, v_j_47_, v___y_57_);
lean_dec(v_j_47_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 0, v___x_58_);
v___x_60_ = v___x_51_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_58_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
}
}
else
{
lean_object* v_ks_92_; lean_object* v_vs_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_113_; 
v_ks_92_ = lean_ctor_get(v_x_39_, 0);
v_vs_93_ = lean_ctor_get(v_x_39_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_x_39_);
if (v_isSharedCheck_113_ == 0)
{
v___x_95_ = v_x_39_;
v_isShared_96_ = v_isSharedCheck_113_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_vs_93_);
lean_inc(v_ks_92_);
lean_dec(v_x_39_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_113_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_ks_92_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_vs_93_);
v___x_98_ = v_reuseFailAlloc_112_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v_newNode_99_; uint8_t v___y_101_; size_t v___x_107_; uint8_t v___x_108_; 
v_newNode_99_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4___redArg(v___x_98_, v_x_42_, v_x_43_);
v___x_107_ = ((size_t)7ULL);
v___x_108_ = lean_usize_dec_le(v___x_107_, v_x_41_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_109_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_99_);
v___x_110_ = lean_unsigned_to_nat(4u);
v___x_111_ = lean_nat_dec_lt(v___x_109_, v___x_110_);
lean_dec(v___x_109_);
v___y_101_ = v___x_111_;
goto v___jp_100_;
}
else
{
v___y_101_ = v___x_108_;
goto v___jp_100_;
}
v___jp_100_:
{
if (v___y_101_ == 0)
{
lean_object* v_ks_102_; lean_object* v_vs_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v_ks_102_ = lean_ctor_get(v_newNode_99_, 0);
lean_inc_ref(v_ks_102_);
v_vs_103_ = lean_ctor_get(v_newNode_99_, 1);
lean_inc_ref(v_vs_103_);
lean_dec_ref(v_newNode_99_);
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___closed__0);
v___x_106_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(v_x_41_, v_ks_102_, v_vs_103_, v___x_104_, v___x_105_);
lean_dec_ref(v_vs_103_);
lean_dec_ref(v_ks_102_);
return v___x_106_;
}
else
{
return v_newNode_99_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(size_t v_depth_114_, lean_object* v_keys_115_, lean_object* v_vals_116_, lean_object* v_i_117_, lean_object* v_entries_118_){
_start:
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = lean_array_get_size(v_keys_115_);
v___x_120_ = lean_nat_dec_lt(v_i_117_, v___x_119_);
if (v___x_120_ == 0)
{
lean_dec(v_i_117_);
return v_entries_118_;
}
else
{
lean_object* v_k_121_; lean_object* v_v_122_; size_t v___x_123_; size_t v___x_124_; size_t v___x_125_; uint64_t v___x_126_; size_t v_h_127_; size_t v___x_128_; lean_object* v___x_129_; size_t v___x_130_; size_t v___x_131_; size_t v___x_132_; size_t v_h_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_k_121_ = lean_array_fget_borrowed(v_keys_115_, v_i_117_);
v_v_122_ = lean_array_fget_borrowed(v_vals_116_, v_i_117_);
v___x_123_ = lean_ptr_addr(v_k_121_);
v___x_124_ = ((size_t)3ULL);
v___x_125_ = lean_usize_shift_right(v___x_123_, v___x_124_);
v___x_126_ = lean_usize_to_uint64(v___x_125_);
v_h_127_ = lean_uint64_to_usize(v___x_126_);
v___x_128_ = ((size_t)5ULL);
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = ((size_t)1ULL);
v___x_131_ = lean_usize_sub(v_depth_114_, v___x_130_);
v___x_132_ = lean_usize_mul(v___x_128_, v___x_131_);
v_h_133_ = lean_usize_shift_right(v_h_127_, v___x_132_);
v___x_134_ = lean_nat_add(v_i_117_, v___x_129_);
lean_dec(v_i_117_);
lean_inc(v_v_122_);
lean_inc(v_k_121_);
v___x_135_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_entries_118_, v_h_133_, v_depth_114_, v_k_121_, v_v_122_);
v_i_117_ = v___x_134_;
v_entries_118_ = v___x_135_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_137_, lean_object* v_keys_138_, lean_object* v_vals_139_, lean_object* v_i_140_, lean_object* v_entries_141_){
_start:
{
size_t v_depth_boxed_142_; lean_object* v_res_143_; 
v_depth_boxed_142_ = lean_unbox_usize(v_depth_137_);
lean_dec(v_depth_137_);
v_res_143_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(v_depth_boxed_142_, v_keys_138_, v_vals_139_, v_i_140_, v_entries_141_);
lean_dec_ref(v_vals_139_);
lean_dec_ref(v_keys_138_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg___boxed(lean_object* v_x_144_, lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
size_t v_x_6046__boxed_149_; size_t v_x_6047__boxed_150_; lean_object* v_res_151_; 
v_x_6046__boxed_149_ = lean_unbox_usize(v_x_145_);
lean_dec(v_x_145_);
v_x_6047__boxed_150_ = lean_unbox_usize(v_x_146_);
lean_dec(v_x_146_);
v_res_151_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_x_144_, v_x_6046__boxed_149_, v_x_6047__boxed_150_, v_x_147_, v_x_148_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1___redArg(lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
size_t v___x_155_; size_t v___x_156_; size_t v___x_157_; uint64_t v___x_158_; size_t v___x_159_; size_t v___x_160_; lean_object* v___x_161_; 
v___x_155_ = lean_ptr_addr(v_x_153_);
v___x_156_ = ((size_t)3ULL);
v___x_157_ = lean_usize_shift_right(v___x_155_, v___x_156_);
v___x_158_ = lean_usize_to_uint64(v___x_157_);
v___x_159_ = lean_uint64_to_usize(v___x_158_);
v___x_160_ = ((size_t)1ULL);
v___x_161_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_x_152_, v___x_159_, v___x_160_, v_x_153_, v_x_154_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___lam__0(lean_object* v_e_162_, lean_object* v___x_163_, lean_object* v_s_164_){
_start:
{
lean_object* v_vars_165_; lean_object* v_varMap_166_; lean_object* v_vars_x27_167_; lean_object* v_varMap_x27_168_; lean_object* v_natToIntMap_169_; lean_object* v_natDef_170_; lean_object* v_dvds_171_; lean_object* v_lowers_172_; lean_object* v_uppers_173_; lean_object* v_diseqs_174_; lean_object* v_elimEqs_175_; lean_object* v_elimStack_176_; lean_object* v_occurs_177_; lean_object* v_assignment_178_; lean_object* v_nextCnstrId_179_; uint8_t v_caseSplits_180_; lean_object* v_steps_181_; lean_object* v_conflict_x3f_182_; lean_object* v_diseqSplits_183_; lean_object* v_divMod_184_; lean_object* v_toIntIds_185_; lean_object* v_toIntInfos_186_; lean_object* v_toIntTermMap_187_; lean_object* v_toIntVarMap_188_; uint8_t v_usedCommRing_189_; lean_object* v_nonlinearOccs_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_198_; 
v_vars_165_ = lean_ctor_get(v_s_164_, 0);
v_varMap_166_ = lean_ctor_get(v_s_164_, 1);
v_vars_x27_167_ = lean_ctor_get(v_s_164_, 2);
v_varMap_x27_168_ = lean_ctor_get(v_s_164_, 3);
v_natToIntMap_169_ = lean_ctor_get(v_s_164_, 4);
v_natDef_170_ = lean_ctor_get(v_s_164_, 5);
v_dvds_171_ = lean_ctor_get(v_s_164_, 6);
v_lowers_172_ = lean_ctor_get(v_s_164_, 7);
v_uppers_173_ = lean_ctor_get(v_s_164_, 8);
v_diseqs_174_ = lean_ctor_get(v_s_164_, 9);
v_elimEqs_175_ = lean_ctor_get(v_s_164_, 10);
v_elimStack_176_ = lean_ctor_get(v_s_164_, 11);
v_occurs_177_ = lean_ctor_get(v_s_164_, 12);
v_assignment_178_ = lean_ctor_get(v_s_164_, 13);
v_nextCnstrId_179_ = lean_ctor_get(v_s_164_, 14);
v_caseSplits_180_ = lean_ctor_get_uint8(v_s_164_, sizeof(void*)*24);
v_steps_181_ = lean_ctor_get(v_s_164_, 15);
v_conflict_x3f_182_ = lean_ctor_get(v_s_164_, 16);
v_diseqSplits_183_ = lean_ctor_get(v_s_164_, 17);
v_divMod_184_ = lean_ctor_get(v_s_164_, 18);
v_toIntIds_185_ = lean_ctor_get(v_s_164_, 19);
v_toIntInfos_186_ = lean_ctor_get(v_s_164_, 20);
v_toIntTermMap_187_ = lean_ctor_get(v_s_164_, 21);
v_toIntVarMap_188_ = lean_ctor_get(v_s_164_, 22);
v_usedCommRing_189_ = lean_ctor_get_uint8(v_s_164_, sizeof(void*)*24 + 1);
v_nonlinearOccs_190_ = lean_ctor_get(v_s_164_, 23);
v_isSharedCheck_198_ = !lean_is_exclusive(v_s_164_);
if (v_isSharedCheck_198_ == 0)
{
v___x_192_ = v_s_164_;
v_isShared_193_ = v_isSharedCheck_198_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_nonlinearOccs_190_);
lean_inc(v_toIntVarMap_188_);
lean_inc(v_toIntTermMap_187_);
lean_inc(v_toIntInfos_186_);
lean_inc(v_toIntIds_185_);
lean_inc(v_divMod_184_);
lean_inc(v_diseqSplits_183_);
lean_inc(v_conflict_x3f_182_);
lean_inc(v_steps_181_);
lean_inc(v_nextCnstrId_179_);
lean_inc(v_assignment_178_);
lean_inc(v_occurs_177_);
lean_inc(v_elimStack_176_);
lean_inc(v_elimEqs_175_);
lean_inc(v_diseqs_174_);
lean_inc(v_uppers_173_);
lean_inc(v_lowers_172_);
lean_inc(v_dvds_171_);
lean_inc(v_natDef_170_);
lean_inc(v_natToIntMap_169_);
lean_inc(v_varMap_x27_168_);
lean_inc(v_vars_x27_167_);
lean_inc(v_varMap_166_);
lean_inc(v_vars_165_);
lean_dec(v_s_164_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_198_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1___redArg(v_natToIntMap_169_, v_e_162_, v___x_163_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 4, v___x_194_);
v___x_196_ = v___x_192_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 24, 2);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_vars_165_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_varMap_166_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v_vars_x27_167_);
lean_ctor_set(v_reuseFailAlloc_197_, 3, v_varMap_x27_168_);
lean_ctor_set(v_reuseFailAlloc_197_, 4, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_197_, 5, v_natDef_170_);
lean_ctor_set(v_reuseFailAlloc_197_, 6, v_dvds_171_);
lean_ctor_set(v_reuseFailAlloc_197_, 7, v_lowers_172_);
lean_ctor_set(v_reuseFailAlloc_197_, 8, v_uppers_173_);
lean_ctor_set(v_reuseFailAlloc_197_, 9, v_diseqs_174_);
lean_ctor_set(v_reuseFailAlloc_197_, 10, v_elimEqs_175_);
lean_ctor_set(v_reuseFailAlloc_197_, 11, v_elimStack_176_);
lean_ctor_set(v_reuseFailAlloc_197_, 12, v_occurs_177_);
lean_ctor_set(v_reuseFailAlloc_197_, 13, v_assignment_178_);
lean_ctor_set(v_reuseFailAlloc_197_, 14, v_nextCnstrId_179_);
lean_ctor_set(v_reuseFailAlloc_197_, 15, v_steps_181_);
lean_ctor_set(v_reuseFailAlloc_197_, 16, v_conflict_x3f_182_);
lean_ctor_set(v_reuseFailAlloc_197_, 17, v_diseqSplits_183_);
lean_ctor_set(v_reuseFailAlloc_197_, 18, v_divMod_184_);
lean_ctor_set(v_reuseFailAlloc_197_, 19, v_toIntIds_185_);
lean_ctor_set(v_reuseFailAlloc_197_, 20, v_toIntInfos_186_);
lean_ctor_set(v_reuseFailAlloc_197_, 21, v_toIntTermMap_187_);
lean_ctor_set(v_reuseFailAlloc_197_, 22, v_toIntVarMap_188_);
lean_ctor_set(v_reuseFailAlloc_197_, 23, v_nonlinearOccs_190_);
lean_ctor_set_uint8(v_reuseFailAlloc_197_, sizeof(void*)*24, v_caseSplits_180_);
lean_ctor_set_uint8(v_reuseFailAlloc_197_, sizeof(void*)*24 + 1, v_usedCommRing_189_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_199_, lean_object* v_vals_200_, lean_object* v_i_201_, lean_object* v_k_202_){
_start:
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = lean_array_get_size(v_keys_199_);
v___x_204_ = lean_nat_dec_lt(v_i_201_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
lean_dec(v_i_201_);
v___x_205_ = lean_box(0);
return v___x_205_;
}
else
{
lean_object* v_k_x27_206_; size_t v___x_207_; size_t v___x_208_; uint8_t v___x_209_; 
v_k_x27_206_ = lean_array_fget_borrowed(v_keys_199_, v_i_201_);
v___x_207_ = lean_ptr_addr(v_k_202_);
v___x_208_ = lean_ptr_addr(v_k_x27_206_);
v___x_209_ = lean_usize_dec_eq(v___x_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = lean_nat_add(v_i_201_, v___x_210_);
lean_dec(v_i_201_);
v_i_201_ = v___x_211_;
goto _start;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_array_fget_borrowed(v_vals_200_, v_i_201_);
lean_dec(v_i_201_);
lean_inc(v___x_213_);
v___x_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_215_, lean_object* v_vals_216_, lean_object* v_i_217_, lean_object* v_k_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(v_keys_215_, v_vals_216_, v_i_217_, v_k_218_);
lean_dec_ref(v_k_218_);
lean_dec_ref(v_vals_216_);
lean_dec_ref(v_keys_215_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(lean_object* v_x_220_, size_t v_x_221_, lean_object* v_x_222_){
_start:
{
if (lean_obj_tag(v_x_220_) == 0)
{
lean_object* v_es_223_; lean_object* v___x_224_; size_t v___x_225_; size_t v___x_226_; lean_object* v_j_227_; lean_object* v___x_228_; 
v_es_223_ = lean_ctor_get(v_x_220_, 0);
v___x_224_ = lean_box(2);
v___x_225_ = ((size_t)31ULL);
v___x_226_ = lean_usize_land(v_x_221_, v___x_225_);
v_j_227_ = lean_usize_to_nat(v___x_226_);
v___x_228_ = lean_array_get_borrowed(v___x_224_, v_es_223_, v_j_227_);
lean_dec(v_j_227_);
switch(lean_obj_tag(v___x_228_))
{
case 0:
{
lean_object* v_key_229_; lean_object* v_val_230_; size_t v___x_231_; size_t v___x_232_; uint8_t v___x_233_; 
v_key_229_ = lean_ctor_get(v___x_228_, 0);
v_val_230_ = lean_ctor_get(v___x_228_, 1);
v___x_231_ = lean_ptr_addr(v_x_222_);
v___x_232_ = lean_ptr_addr(v_key_229_);
v___x_233_ = lean_usize_dec_eq(v___x_231_, v___x_232_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; 
v___x_234_ = lean_box(0);
return v___x_234_;
}
else
{
lean_object* v___x_235_; 
lean_inc(v_val_230_);
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v_val_230_);
return v___x_235_;
}
}
case 1:
{
lean_object* v_node_236_; size_t v___x_237_; size_t v___x_238_; 
v_node_236_ = lean_ctor_get(v___x_228_, 0);
v___x_237_ = ((size_t)5ULL);
v___x_238_ = lean_usize_shift_right(v_x_221_, v___x_237_);
v_x_220_ = v_node_236_;
v_x_221_ = v___x_238_;
goto _start;
}
default: 
{
lean_object* v___x_240_; 
v___x_240_ = lean_box(0);
return v___x_240_;
}
}
}
else
{
lean_object* v_ks_241_; lean_object* v_vs_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_ks_241_ = lean_ctor_get(v_x_220_, 0);
v_vs_242_ = lean_ctor_get(v_x_220_, 1);
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(v_ks_241_, v_vs_242_, v___x_243_, v_x_222_);
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg___boxed(lean_object* v_x_245_, lean_object* v_x_246_, lean_object* v_x_247_){
_start:
{
size_t v_x_6269__boxed_248_; lean_object* v_res_249_; 
v_x_6269__boxed_248_ = lean_unbox_usize(v_x_246_);
lean_dec(v_x_246_);
v_res_249_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(v_x_245_, v_x_6269__boxed_248_, v_x_247_);
lean_dec_ref(v_x_247_);
lean_dec_ref(v_x_245_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; uint64_t v___x_255_; size_t v___x_256_; lean_object* v___x_257_; 
v___x_252_ = lean_ptr_addr(v_x_251_);
v___x_253_ = ((size_t)3ULL);
v___x_254_ = lean_usize_shift_right(v___x_252_, v___x_253_);
v___x_255_ = lean_usize_to_uint64(v___x_254_);
v___x_256_ = lean_uint64_to_usize(v___x_255_);
v___x_257_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(v_x_250_, v___x_256_, v_x_251_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg___boxed(lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(v_x_258_, v_x_259_);
lean_dec_ref(v_x_259_);
lean_dec_ref(v_x_258_);
return v_res_260_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = l_Lean_Level_ofNat(v___x_266_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_box(0);
v___x_269_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__3);
v___x_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_268_);
return v___x_270_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4);
v___x_272_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__2));
v___x_273_ = l_Lean_mkConst(v___x_272_, v___x_271_);
return v___x_273_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = l_Lean_Int_mkType;
v___x_275_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__5);
v___x_276_ = l_Lean_Expr_app___override(v___x_275_, v___x_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(lean_object* v_e_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_278_, v_a_286_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_342_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_342_ == 0)
{
v___x_292_ = v___x_289_;
v_isShared_293_ = v_isSharedCheck_342_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_342_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v_natToIntMap_294_; lean_object* v___x_295_; 
v_natToIntMap_294_ = lean_ctor_get(v_a_290_, 4);
lean_inc_ref(v_natToIntMap_294_);
lean_dec(v_a_290_);
v___x_295_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(v_natToIntMap_294_, v_e_277_);
lean_dec_ref(v_natToIntMap_294_);
if (lean_obj_tag(v___x_295_) == 1)
{
lean_object* v_val_296_; lean_object* v___x_298_; 
lean_dec_ref(v_e_277_);
v_val_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_val_296_);
lean_dec_ref_known(v___x_295_, 1);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v_val_296_);
v___x_298_ = v___x_292_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_val_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v___x_295_);
lean_del_object(v___x_292_);
lean_inc_ref(v_e_277_);
v___x_300_ = l_Lean_mkIntNatCast(v_e_277_);
v___x_301_ = l_Lean_Meta_Sym_shareCommon(v___x_300_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___f_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc_n(v_a_302_, 2);
lean_dec_ref_known(v___x_301_, 1);
v___x_303_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__6);
v___x_304_ = l_Lean_Expr_app___override(v___x_303_, v_a_302_);
v___x_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_305_, 0, v_a_302_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
lean_inc_ref(v___x_305_);
lean_inc_ref(v_e_277_);
v___f_306_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___lam__0), 3, 2);
lean_closure_set(v___f_306_, 0, v_e_277_);
lean_closure_set(v___f_306_, 1, v___x_305_);
v___x_307_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_308_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_307_, v___f_306_, v_a_278_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v___x_309_; 
lean_dec_ref_known(v___x_308_, 1);
v___x_309_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_307_, v_e_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_316_ == 0)
{
lean_object* v_unused_317_; 
v_unused_317_ = lean_ctor_get(v___x_309_, 0);
lean_dec(v_unused_317_);
v___x_311_ = v___x_309_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_dec(v___x_309_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_305_);
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_305_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec_ref_known(v___x_305_, 2);
v_a_318_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_309_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_309_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec_ref_known(v___x_305_, 2);
lean_dec_ref(v_e_277_);
v_a_326_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_308_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_308_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
lean_dec_ref(v_e_277_);
v_a_334_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_301_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_301_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec_ref(v_e_277_);
v_a_343_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_289_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_289_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___boxed(lean_object* v_e_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec(v_a_352_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0(lean_object* v_00_u03b2_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___redArg(v_x_365_, v_x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0___boxed(lean_object* v_00_u03b2_368_, lean_object* v_x_369_, lean_object* v_x_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0(v_00_u03b2_368_, v_x_369_, v_x_370_);
lean_dec_ref(v_x_370_);
lean_dec_ref(v_x_369_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1(lean_object* v_00_u03b2_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1___redArg(v_x_373_, v_x_374_, v_x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0(lean_object* v_00_u03b2_377_, lean_object* v_x_378_, size_t v_x_379_, lean_object* v_x_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___redArg(v_x_378_, v_x_379_, v_x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_382_, lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
size_t v_x_6529__boxed_386_; lean_object* v_res_387_; 
v_x_6529__boxed_386_ = lean_unbox_usize(v_x_384_);
lean_dec(v_x_384_);
v_res_387_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0(v_00_u03b2_382_, v_x_383_, v_x_6529__boxed_386_, v_x_385_);
lean_dec_ref(v_x_385_);
lean_dec_ref(v_x_383_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2(lean_object* v_00_u03b2_388_, lean_object* v_x_389_, size_t v_x_390_, size_t v_x_391_, lean_object* v_x_392_, lean_object* v_x_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___redArg(v_x_389_, v_x_390_, v_x_391_, v_x_392_, v_x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_395_, lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_, lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
size_t v_x_6540__boxed_401_; size_t v_x_6541__boxed_402_; lean_object* v_res_403_; 
v_x_6540__boxed_401_ = lean_unbox_usize(v_x_397_);
lean_dec(v_x_397_);
v_x_6541__boxed_402_ = lean_unbox_usize(v_x_398_);
lean_dec(v_x_398_);
v_res_403_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2(v_00_u03b2_395_, v_x_396_, v_x_6540__boxed_401_, v_x_6541__boxed_402_, v_x_399_, v_x_400_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_404_, lean_object* v_keys_405_, lean_object* v_vals_406_, lean_object* v_heq_407_, lean_object* v_i_408_, lean_object* v_k_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___redArg(v_keys_405_, v_vals_406_, v_i_408_, v_k_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_411_, lean_object* v_keys_412_, lean_object* v_vals_413_, lean_object* v_heq_414_, lean_object* v_i_415_, lean_object* v_k_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__0_spec__0_spec__1(v_00_u03b2_411_, v_keys_412_, v_vals_413_, v_heq_414_, v_i_415_, v_k_416_);
lean_dec_ref(v_k_416_);
lean_dec_ref(v_vals_413_);
lean_dec_ref(v_keys_412_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_418_, lean_object* v_n_419_, lean_object* v_k_420_, lean_object* v_v_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4___redArg(v_n_419_, v_k_420_, v_v_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_423_, size_t v_depth_424_, lean_object* v_keys_425_, lean_object* v_vals_426_, lean_object* v_heq_427_, lean_object* v_i_428_, lean_object* v_entries_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___redArg(v_depth_424_, v_keys_425_, v_vals_426_, v_i_428_, v_entries_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_431_, lean_object* v_depth_432_, lean_object* v_keys_433_, lean_object* v_vals_434_, lean_object* v_heq_435_, lean_object* v_i_436_, lean_object* v_entries_437_){
_start:
{
size_t v_depth_boxed_438_; lean_object* v_res_439_; 
v_depth_boxed_438_ = lean_unbox_usize(v_depth_432_);
lean_dec(v_depth_432_);
v_res_439_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__5(v_00_u03b2_431_, v_depth_boxed_438_, v_keys_433_, v_vals_434_, v_heq_435_, v_i_436_, v_entries_437_);
lean_dec_ref(v_vals_434_);
lean_dec_ref(v_keys_433_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_440_, lean_object* v_x_441_, lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkNatVar_spec__1_spec__2_spec__4_spec__5___redArg(v_x_441_, v_x_442_, v_x_443_, v_x_444_);
return v___x_445_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_449_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar___closed__4);
v___x_450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__1));
v___x_451_ = l_Lean_mkConst(v___x_450_, v___x_449_);
return v___x_451_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = l_Lean_Int_mkType;
v___x_453_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__2);
v___x_454_ = l_Lean_Expr_app___override(v___x_453_, v___x_452_);
return v___x_454_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte(void){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_intIte___closed__3);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__0(lean_object* v_a_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = lean_nat_to_int(v_a_456_);
return v___x_457_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(lean_object* v_keys_458_, lean_object* v_i_459_, lean_object* v_k_460_){
_start:
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_array_get_size(v_keys_458_);
v___x_462_ = lean_nat_dec_lt(v_i_459_, v___x_461_);
if (v___x_462_ == 0)
{
lean_dec(v_i_459_);
return v___x_462_;
}
else
{
lean_object* v_k_x27_463_; size_t v___x_464_; size_t v___x_465_; uint8_t v___x_466_; 
v_k_x27_463_ = lean_array_fget_borrowed(v_keys_458_, v_i_459_);
v___x_464_ = lean_ptr_addr(v_k_460_);
v___x_465_ = lean_ptr_addr(v_k_x27_463_);
v___x_466_ = lean_usize_dec_eq(v___x_464_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_unsigned_to_nat(1u);
v___x_468_ = lean_nat_add(v_i_459_, v___x_467_);
lean_dec(v_i_459_);
v_i_459_ = v___x_468_;
goto _start;
}
else
{
lean_dec(v_i_459_);
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_keys_470_, lean_object* v_i_471_, lean_object* v_k_472_){
_start:
{
uint8_t v_res_473_; lean_object* v_r_474_; 
v_res_473_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(v_keys_470_, v_i_471_, v_k_472_);
lean_dec_ref(v_k_472_);
lean_dec_ref(v_keys_470_);
v_r_474_ = lean_box(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(lean_object* v_x_475_, size_t v_x_476_, lean_object* v_x_477_){
_start:
{
if (lean_obj_tag(v_x_475_) == 0)
{
lean_object* v_es_478_; lean_object* v___x_479_; size_t v___x_480_; size_t v___x_481_; lean_object* v_j_482_; lean_object* v___x_483_; 
v_es_478_ = lean_ctor_get(v_x_475_, 0);
v___x_479_ = lean_box(2);
v___x_480_ = ((size_t)31ULL);
v___x_481_ = lean_usize_land(v_x_476_, v___x_480_);
v_j_482_ = lean_usize_to_nat(v___x_481_);
v___x_483_ = lean_array_get_borrowed(v___x_479_, v_es_478_, v_j_482_);
lean_dec(v_j_482_);
switch(lean_obj_tag(v___x_483_))
{
case 0:
{
lean_object* v_key_484_; size_t v___x_485_; size_t v___x_486_; uint8_t v___x_487_; 
v_key_484_ = lean_ctor_get(v___x_483_, 0);
v___x_485_ = lean_ptr_addr(v_x_477_);
v___x_486_ = lean_ptr_addr(v_key_484_);
v___x_487_ = lean_usize_dec_eq(v___x_485_, v___x_486_);
return v___x_487_;
}
case 1:
{
lean_object* v_node_488_; size_t v___x_489_; size_t v___x_490_; 
v_node_488_ = lean_ctor_get(v___x_483_, 0);
v___x_489_ = ((size_t)5ULL);
v___x_490_ = lean_usize_shift_right(v_x_476_, v___x_489_);
v_x_475_ = v_node_488_;
v_x_476_ = v___x_490_;
goto _start;
}
default: 
{
uint8_t v___x_492_; 
v___x_492_ = 0;
return v___x_492_;
}
}
}
else
{
lean_object* v_ks_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v_ks_493_ = lean_ctor_get(v_x_475_, 0);
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(v_ks_493_, v___x_494_, v_x_477_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg___boxed(lean_object* v_x_496_, lean_object* v_x_497_, lean_object* v_x_498_){
_start:
{
size_t v_x_62043__boxed_499_; uint8_t v_res_500_; lean_object* v_r_501_; 
v_x_62043__boxed_499_ = lean_unbox_usize(v_x_497_);
lean_dec(v_x_497_);
v_res_500_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(v_x_496_, v_x_62043__boxed_499_, v_x_498_);
lean_dec_ref(v_x_498_);
lean_dec_ref(v_x_496_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(lean_object* v_x_502_, lean_object* v_x_503_){
_start:
{
size_t v___x_504_; size_t v___x_505_; size_t v___x_506_; uint64_t v___x_507_; size_t v___x_508_; uint8_t v___x_509_; 
v___x_504_ = lean_ptr_addr(v_x_503_);
v___x_505_ = ((size_t)3ULL);
v___x_506_ = lean_usize_shift_right(v___x_504_, v___x_505_);
v___x_507_ = lean_usize_to_uint64(v___x_506_);
v___x_508_ = lean_uint64_to_usize(v___x_507_);
v___x_509_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(v_x_502_, v___x_508_, v_x_503_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg___boxed(lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
uint8_t v_res_512_; lean_object* v_r_513_; 
v_res_512_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_x_510_, v_x_511_);
lean_dec_ref(v_x_511_);
lean_dec_ref(v_x_510_);
v_r_513_ = lean_box(v_res_512_);
return v_r_513_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_box(0);
v___x_557_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__24));
v___x_558_ = l_Lean_mkConst(v___x_557_, v___x_556_);
return v___x_558_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_564_ = lean_box(0);
v___x_565_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__27));
v___x_566_ = l_Lean_mkConst(v___x_565_, v___x_564_);
return v___x_566_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = lean_box(0);
v___x_573_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__30));
v___x_574_ = l_Lean_mkConst(v___x_573_, v___x_572_);
return v___x_574_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = lean_box(0);
v___x_581_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__33));
v___x_582_ = l_Lean_mkConst(v___x_581_, v___x_580_);
return v___x_582_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_box(0);
v___x_589_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__36));
v___x_590_ = l_Lean_mkConst(v___x_589_, v___x_588_);
return v___x_590_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_box(0);
v___x_597_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__39));
v___x_598_ = l_Lean_mkConst(v___x_597_, v___x_596_);
return v___x_598_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = lean_box(0);
v___x_602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__41));
v___x_603_ = l_Lean_mkConst(v___x_602_, v___x_601_);
return v___x_603_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_609_ = lean_box(0);
v___x_610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__44));
v___x_611_ = l_Lean_mkConst(v___x_610_, v___x_609_);
return v___x_611_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_616_ = lean_box(0);
v___x_617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__47));
v___x_618_ = l_Lean_mkConst(v___x_617_, v___x_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(lean_object* v_e_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v___x_631_; 
lean_inc_ref(v_e_619_);
v___x_631_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_619_, v_a_627_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_631_, 1);
v___x_633_ = l_Lean_Expr_cleanupAnnotations(v_a_632_);
v___x_634_ = l_Lean_Expr_isApp(v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
lean_dec_ref(v___x_633_);
v___x_635_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v___x_635_;
}
else
{
lean_object* v_arg_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_arg_636_ = lean_ctor_get(v___x_633_, 1);
lean_inc_ref(v_arg_636_);
v___x_637_ = l_Lean_Expr_appFnCleanup___redArg(v___x_633_);
v___x_638_ = l_Lean_Expr_isApp(v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
lean_dec_ref(v___x_637_);
lean_dec_ref(v_arg_636_);
v___x_639_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v___x_639_;
}
else
{
lean_object* v_arg_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_arg_640_ = lean_ctor_get(v___x_637_, 1);
lean_inc_ref(v_arg_640_);
v___x_641_ = l_Lean_Expr_appFnCleanup___redArg(v___x_637_);
v___x_642_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__2));
v___x_643_ = l_Lean_Expr_isConstOf(v___x_641_, v___x_642_);
if (v___x_643_ == 0)
{
uint8_t v___x_644_; 
v___x_644_ = l_Lean_Expr_isApp(v___x_641_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
lean_dec_ref(v___x_641_);
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
v___x_645_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v___x_645_;
}
else
{
lean_object* v_arg_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_arg_646_ = lean_ctor_get(v___x_641_, 1);
lean_inc_ref(v_arg_646_);
v___x_647_ = l_Lean_Expr_appFnCleanup___redArg(v___x_641_);
v___x_648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5));
v___x_649_ = l_Lean_Expr_isConstOf(v___x_647_, v___x_648_);
if (v___x_649_ == 0)
{
uint8_t v___x_650_; 
v___x_650_ = l_Lean_Expr_isApp(v___x_647_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
lean_dec_ref(v___x_647_);
lean_dec_ref(v_arg_646_);
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
v___x_651_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v___x_651_;
}
else
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = l_Lean_Expr_appFnCleanup___redArg(v___x_647_);
v___x_653_ = l_Lean_Expr_isApp(v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec_ref(v___x_652_);
lean_dec_ref(v_arg_646_);
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
v___x_654_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v___x_654_;
}
else
{
lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_655_ = l_Lean_Expr_appFnCleanup___redArg(v___x_652_);
v___x_656_ = l_Lean_Expr_isApp(v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
lean_dec_ref(v___x_655_);
lean_dec_ref(v_arg_646_);
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
v___x_657_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_658_ = l_Lean_Expr_appFnCleanup___redArg(v___x_655_);
v___x_659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8));
v___x_660_ = l_Lean_Expr_isConstOf(v___x_658_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11));
v___x_662_ = l_Lean_Expr_isConstOf(v___x_658_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14));
v___x_664_ = l_Lean_Expr_isConstOf(v___x_658_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17));
v___x_666_ = l_Lean_Expr_isConstOf(v___x_658_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_667_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20));
v___x_668_ = l_Lean_Expr_isConstOf(v___x_658_, v___x_667_);
lean_dec_ref(v___x_658_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
lean_dec_ref(v_arg_646_);
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
v___x_669_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v___x_669_;
}
else
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_646_, v_a_627_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; uint8_t v___x_672_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = lean_unbox(v_a_671_);
lean_dec(v_a_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
v___x_673_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v___x_673_;
}
else
{
lean_object* v___x_674_; 
lean_dec_ref(v_e_619_);
lean_inc_ref(v_arg_640_);
v___x_674_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_640_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v_fst_676_; lean_object* v_snd_677_; lean_object* v___x_678_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_674_, 1);
v_fst_676_ = lean_ctor_get(v_a_675_, 0);
lean_inc(v_fst_676_);
v_snd_677_ = lean_ctor_get(v_a_675_, 1);
lean_inc(v_snd_677_);
lean_dec(v_a_675_);
lean_inc_ref(v_arg_636_);
v___x_678_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_636_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_698_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_698_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_698_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_698_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_fst_683_; lean_object* v_snd_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_697_; 
v_fst_683_ = lean_ctor_get(v_a_679_, 0);
v_snd_684_ = lean_ctor_get(v_a_679_, 1);
v_isSharedCheck_697_ = !lean_is_exclusive(v_a_679_);
if (v_isSharedCheck_697_ == 0)
{
v___x_686_ = v_a_679_;
v_isShared_687_ = v_isSharedCheck_697_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_snd_684_);
lean_inc(v_fst_683_);
lean_dec(v_a_679_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_697_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_688_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__25);
lean_inc(v_fst_683_);
lean_inc(v_fst_676_);
v___x_689_ = l_Lean_mkApp6(v___x_688_, v_arg_640_, v_arg_636_, v_fst_676_, v_fst_683_, v_snd_677_, v_snd_684_);
v___x_690_ = l_Lean_mkIntAdd(v_fst_676_, v_fst_683_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v___x_689_);
lean_ctor_set(v___x_686_, 0, v___x_690_);
v___x_692_ = v___x_686_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v___x_689_);
v___x_692_ = v_reuseFailAlloc_696_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_694_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_692_);
v___x_694_ = v___x_681_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
else
{
lean_dec(v_snd_677_);
lean_dec(v_fst_676_);
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
return v___x_678_;
}
}
else
{
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
return v___x_674_;
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_e_619_);
v_a_699_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_670_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_670_);
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
else
{
lean_object* v___x_707_; 
lean_dec_ref(v___x_658_);
v___x_707_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_646_, v_a_627_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; uint8_t v___x_709_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_707_, 1);
v___x_709_ = lean_unbox(v_a_708_);
lean_dec(v_a_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; 
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
v___x_710_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v___x_710_;
}
else
{
lean_object* v___x_711_; 
lean_dec_ref(v_e_619_);
lean_inc_ref(v_arg_640_);
v___x_711_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_640_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v_fst_713_; lean_object* v_snd_714_; lean_object* v___x_715_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
v_fst_713_ = lean_ctor_get(v_a_712_, 0);
lean_inc(v_fst_713_);
v_snd_714_ = lean_ctor_get(v_a_712_, 1);
lean_inc(v_snd_714_);
lean_dec(v_a_712_);
lean_inc_ref(v_arg_636_);
v___x_715_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_636_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_735_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_735_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_735_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_735_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_fst_720_; lean_object* v_snd_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_734_; 
v_fst_720_ = lean_ctor_get(v_a_716_, 0);
v_snd_721_ = lean_ctor_get(v_a_716_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v_a_716_);
if (v_isSharedCheck_734_ == 0)
{
v___x_723_ = v_a_716_;
v_isShared_724_ = v_isSharedCheck_734_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_snd_721_);
lean_inc(v_fst_720_);
lean_dec(v_a_716_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_734_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_725_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__28);
lean_inc(v_fst_720_);
lean_inc(v_fst_713_);
v___x_726_ = l_Lean_mkApp6(v___x_725_, v_arg_640_, v_arg_636_, v_fst_713_, v_fst_720_, v_snd_714_, v_snd_721_);
v___x_727_ = l_Lean_mkIntMul(v_fst_713_, v_fst_720_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___x_726_);
lean_ctor_set(v___x_723_, 0, v___x_727_);
v___x_729_ = v___x_723_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_726_);
v___x_729_ = v_reuseFailAlloc_733_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_731_; 
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_729_);
v___x_731_ = v___x_718_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
else
{
lean_dec(v_snd_714_);
lean_dec(v_fst_713_);
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
return v___x_715_;
}
}
else
{
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
return v___x_711_;
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_e_619_);
v_a_736_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_707_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_707_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
else
{
lean_object* v___x_744_; 
lean_dec_ref(v___x_658_);
v___x_744_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_646_, v_a_627_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; uint8_t v___x_746_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
v___x_746_ = lean_unbox(v_a_745_);
lean_dec(v_a_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; 
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
v___x_747_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v___x_747_;
}
else
{
lean_object* v___x_748_; 
lean_dec_ref(v_e_619_);
lean_inc_ref(v_arg_640_);
v___x_748_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_640_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v_fst_750_; lean_object* v_snd_751_; lean_object* v___x_752_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
v_fst_750_ = lean_ctor_get(v_a_749_, 0);
lean_inc(v_fst_750_);
v_snd_751_ = lean_ctor_get(v_a_749_, 1);
lean_inc(v_snd_751_);
lean_dec(v_a_749_);
lean_inc_ref(v_arg_636_);
v___x_752_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_636_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_772_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_772_ == 0)
{
v___x_755_ = v___x_752_;
v_isShared_756_ = v_isSharedCheck_772_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_752_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_772_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_fst_757_; lean_object* v_snd_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_771_; 
v_fst_757_ = lean_ctor_get(v_a_753_, 0);
v_snd_758_ = lean_ctor_get(v_a_753_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v_a_753_);
if (v_isSharedCheck_771_ == 0)
{
v___x_760_ = v_a_753_;
v_isShared_761_ = v_isSharedCheck_771_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_snd_758_);
lean_inc(v_fst_757_);
lean_dec(v_a_753_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_771_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_762_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__31);
lean_inc(v_fst_757_);
lean_inc(v_fst_750_);
v___x_763_ = l_Lean_mkApp6(v___x_762_, v_arg_640_, v_arg_636_, v_fst_750_, v_fst_757_, v_snd_751_, v_snd_758_);
v___x_764_ = l_Lean_mkIntDiv(v_fst_750_, v_fst_757_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 1, v___x_763_);
lean_ctor_set(v___x_760_, 0, v___x_764_);
v___x_766_ = v___x_760_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v___x_763_);
v___x_766_ = v_reuseFailAlloc_770_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_768_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_766_);
v___x_768_ = v___x_755_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
else
{
lean_dec(v_snd_751_);
lean_dec(v_fst_750_);
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
return v___x_752_;
}
}
else
{
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
return v___x_748_;
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_e_619_);
v_a_773_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_744_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_744_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
else
{
lean_object* v___x_781_; 
lean_dec_ref(v___x_658_);
v___x_781_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_646_, v_a_627_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; uint8_t v___x_783_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
v___x_783_ = lean_unbox(v_a_782_);
lean_dec(v_a_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; 
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
v___x_784_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v___x_784_;
}
else
{
lean_object* v___x_785_; 
lean_dec_ref(v_e_619_);
lean_inc_ref(v_arg_640_);
v___x_785_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_640_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v_fst_787_; lean_object* v_snd_788_; lean_object* v___x_789_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
v_fst_787_ = lean_ctor_get(v_a_786_, 0);
lean_inc(v_fst_787_);
v_snd_788_ = lean_ctor_get(v_a_786_, 1);
lean_inc(v_snd_788_);
lean_dec(v_a_786_);
lean_inc_ref(v_arg_636_);
v___x_789_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_636_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_809_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_809_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_809_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_809_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v_fst_794_; lean_object* v_snd_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_808_; 
v_fst_794_ = lean_ctor_get(v_a_790_, 0);
v_snd_795_ = lean_ctor_get(v_a_790_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v_a_790_);
if (v_isSharedCheck_808_ == 0)
{
v___x_797_ = v_a_790_;
v_isShared_798_ = v_isSharedCheck_808_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_snd_795_);
lean_inc(v_fst_794_);
lean_dec(v_a_790_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_808_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_799_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__34);
lean_inc(v_fst_794_);
lean_inc(v_fst_787_);
v___x_800_ = l_Lean_mkApp6(v___x_799_, v_arg_640_, v_arg_636_, v_fst_787_, v_fst_794_, v_snd_788_, v_snd_795_);
v___x_801_ = l_Lean_mkIntMod(v_fst_787_, v_fst_794_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v___x_800_);
lean_ctor_set(v___x_797_, 0, v___x_801_);
v___x_803_ = v___x_797_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v___x_800_);
v___x_803_ = v_reuseFailAlloc_807_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_805_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_803_);
v___x_805_ = v___x_792_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
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
else
{
lean_dec(v_snd_788_);
lean_dec(v_fst_787_);
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
return v___x_789_;
}
}
else
{
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
return v___x_785_;
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_e_619_);
v_a_810_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_781_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_781_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
else
{
lean_object* v___x_818_; 
lean_dec_ref(v___x_658_);
v___x_818_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_646_, v_a_627_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; uint8_t v___x_820_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
v___x_820_ = lean_unbox(v_a_819_);
lean_dec(v_a_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; 
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
v___x_821_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v___x_821_;
}
else
{
lean_object* v___x_822_; 
lean_dec_ref(v_e_619_);
lean_inc_ref(v_arg_640_);
v___x_822_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_arg_640_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_842_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_842_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_842_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_842_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_fst_827_; lean_object* v_snd_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_841_; 
v_fst_827_ = lean_ctor_get(v_a_823_, 0);
v_snd_828_ = lean_ctor_get(v_a_823_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v_a_823_);
if (v_isSharedCheck_841_ == 0)
{
v___x_830_ = v_a_823_;
v_isShared_831_ = v_isSharedCheck_841_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_snd_828_);
lean_inc(v_fst_827_);
lean_dec(v_a_823_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_841_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_832_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__37);
lean_inc(v_fst_827_);
lean_inc_ref(v_arg_636_);
v___x_833_ = l_Lean_mkApp4(v___x_832_, v_arg_640_, v_arg_636_, v_fst_827_, v_snd_828_);
v___x_834_ = l_Lean_mkIntPowNat(v_fst_827_, v_arg_636_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 1, v___x_833_);
lean_ctor_set(v___x_830_, 0, v___x_834_);
v___x_836_ = v___x_830_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v___x_833_);
v___x_836_ = v_reuseFailAlloc_840_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_838_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_836_);
v___x_838_ = v___x_825_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
return v___x_822_;
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_e_619_);
v_a_843_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_818_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_818_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
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
lean_object* v___x_851_; 
lean_dec_ref(v___x_647_);
lean_dec_ref(v_arg_646_);
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
v___x_851_ = l_Lean_Meta_getNatValue_x3f(v_e_619_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_866_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_866_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_866_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_866_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
if (lean_obj_tag(v_a_852_) == 1)
{
lean_object* v_val_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v_val_856_ = lean_ctor_get(v_a_852_, 0);
lean_inc(v_val_856_);
lean_dec_ref_known(v_a_852_, 1);
v___x_857_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__40);
v___x_858_ = l_Lean_Expr_app___override(v___x_857_, v_e_619_);
v___x_859_ = lean_nat_to_int(v_val_856_);
v___x_860_ = l_Lean_mkIntLit(v___x_859_);
lean_dec(v___x_859_);
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v___x_858_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_861_);
v___x_863_ = v___x_854_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
else
{
lean_object* v___x_865_; 
lean_del_object(v___x_854_);
lean_dec(v_a_852_);
v___x_865_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
return v___x_865_;
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec_ref(v_e_619_);
v_a_867_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_851_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_851_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
}
else
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
lean_dec_ref(v___x_641_);
v___x_875_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__42);
lean_inc_ref(v_arg_640_);
v___x_876_ = l_Lean_Expr_app___override(v___x_875_, v_arg_640_);
v___x_877_ = l_Lean_Meta_Sym_shareCommon(v___x_876_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_879_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_877_, 1);
lean_inc_ref(v_arg_636_);
v___x_879_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt_x3f(v_arg_636_, v_a_878_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_933_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_933_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_933_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_933_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
if (lean_obj_tag(v_a_880_) == 1)
{
lean_object* v_val_884_; lean_object* v_fst_885_; lean_object* v_snd_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_898_; 
lean_dec_ref(v_e_619_);
v_val_884_ = lean_ctor_get(v_a_880_, 0);
lean_inc(v_val_884_);
lean_dec_ref_known(v_a_880_, 1);
v_fst_885_ = lean_ctor_get(v_val_884_, 0);
v_snd_886_ = lean_ctor_get(v_val_884_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v_val_884_);
if (v_isSharedCheck_898_ == 0)
{
v___x_888_ = v_val_884_;
v_isShared_889_ = v_isSharedCheck_898_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_snd_886_);
lean_inc(v_fst_885_);
lean_dec(v_val_884_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_898_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_890_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__45);
lean_inc(v_fst_885_);
v___x_891_ = l_Lean_mkApp4(v___x_890_, v_arg_640_, v_arg_636_, v_fst_885_, v_snd_886_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v___x_891_);
v___x_893_ = v___x_888_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_fst_885_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v___x_891_);
v___x_893_ = v_reuseFailAlloc_897_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_895_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_893_);
v___x_895_ = v___x_882_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_object* v___x_899_; 
lean_del_object(v___x_882_);
lean_dec(v_a_880_);
v___x_899_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_620_, v_a_628_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_901_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
lean_inc_ref(v_e_619_);
v___x_901_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_e_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v_natToIntMap_903_; uint8_t v___x_904_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
v_natToIntMap_903_ = lean_ctor_get(v_a_900_, 4);
lean_inc_ref(v_natToIntMap_903_);
lean_dec(v_a_900_);
v___x_904_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_natToIntMap_903_, v_e_619_);
lean_dec_ref(v_e_619_);
lean_dec_ref(v_natToIntMap_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
lean_dec_ref_known(v___x_901_, 1);
v___x_905_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__48);
v___x_906_ = l_Lean_mkAppB(v___x_905_, v_arg_640_, v_arg_636_);
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = l_Lean_Meta_Grind_pushNewFact(v___x_906_, v___x_907_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; 
v_unused_916_ = lean_ctor_get(v___x_908_, 0);
lean_dec(v_unused_916_);
v___x_910_ = v___x_908_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_dec(v___x_908_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v_a_902_);
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_902_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v_a_902_);
v_a_917_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_908_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_908_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_dec(v_a_902_);
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
return v___x_901_;
}
}
else
{
lean_dec(v_a_900_);
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_e_619_);
return v___x_901_;
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_e_619_);
v_a_925_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_899_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_899_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
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
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_e_619_);
v_a_934_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_879_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_879_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec_ref(v_arg_640_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_e_619_);
v_a_942_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_877_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_877_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v_e_619_);
v_a_950_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_631_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_631_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___boxed(lean_object* v_e_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_e_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec(v_a_959_);
return v_res_970_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1(lean_object* v_00_u03b2_971_, lean_object* v_x_972_, lean_object* v_x_973_){
_start:
{
uint8_t v___x_974_; 
v___x_974_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_x_972_, v_x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___boxed(lean_object* v_00_u03b2_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
uint8_t v_res_978_; lean_object* v_r_979_; 
v_res_978_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1(v_00_u03b2_975_, v_x_976_, v_x_977_);
lean_dec_ref(v_x_977_);
lean_dec_ref(v_x_976_);
v_r_979_ = lean_box(v_res_978_);
return v_r_979_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1(lean_object* v_00_u03b2_980_, lean_object* v_x_981_, size_t v_x_982_, lean_object* v_x_983_){
_start:
{
uint8_t v___x_984_; 
v___x_984_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___redArg(v_x_981_, v_x_982_, v_x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1___boxed(lean_object* v_00_u03b2_985_, lean_object* v_x_986_, lean_object* v_x_987_, lean_object* v_x_988_){
_start:
{
size_t v_x_63110__boxed_989_; uint8_t v_res_990_; lean_object* v_r_991_; 
v_x_63110__boxed_989_ = lean_unbox_usize(v_x_987_);
lean_dec(v_x_987_);
v_res_990_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1(v_00_u03b2_985_, v_x_986_, v_x_63110__boxed_989_, v_x_988_);
lean_dec_ref(v_x_988_);
lean_dec_ref(v_x_986_);
v_r_991_ = lean_box(v_res_990_);
return v_r_991_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_992_, lean_object* v_keys_993_, lean_object* v_vals_994_, lean_object* v_heq_995_, lean_object* v_i_996_, lean_object* v_k_997_){
_start:
{
uint8_t v___x_998_; 
v___x_998_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___redArg(v_keys_993_, v_i_996_, v_k_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_999_, lean_object* v_keys_1000_, lean_object* v_vals_1001_, lean_object* v_heq_1002_, lean_object* v_i_1003_, lean_object* v_k_1004_){
_start:
{
uint8_t v_res_1005_; lean_object* v_r_1006_; 
v_res_1005_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1_spec__1_spec__2(v_00_u03b2_999_, v_keys_1000_, v_vals_1001_, v_heq_1002_, v_i_1003_, v_k_1004_);
lean_dec_ref(v_k_1004_);
lean_dec_ref(v_vals_1001_);
lean_dec_ref(v_keys_1000_);
v_r_1006_ = lean_box(v_res_1005_);
return v_r_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27(v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v_fst_1021_; lean_object* v_snd_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1046_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v_fst_1021_ = lean_ctor_get(v_a_1020_, 0);
v_snd_1022_ = lean_ctor_get(v_a_1020_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_a_1020_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1024_ = v_a_1020_;
v_isShared_1025_ = v_isSharedCheck_1046_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_snd_1022_);
lean_inc(v_fst_1021_);
lean_dec(v_a_1020_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1046_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_Meta_Sym_shareCommon(v_fst_1021_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1037_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1037_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1037_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v_a_1027_);
v___x_1032_ = v___x_1024_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1027_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_snd_1022_);
v___x_1032_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1034_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1032_);
v___x_1034_ = v___x_1029_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_del_object(v___x_1024_);
lean_dec(v_snd_1022_);
v_a_1038_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1026_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1026_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
else
{
return v___x_1019_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt___boxed(lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec(v_a_1048_);
return v_res_1059_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_unsigned_to_nat(1u);
v___x_1069_ = lean_nat_to_int(v___x_1068_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__5);
v___x_1071_ = lean_int_neg(v___x_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = lean_nat_to_int(v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7);
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(lean_object* v_e_1076_, lean_object* v_x_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = l_Lean_Expr_cleanupAnnotations(v_e_1076_);
v___x_1093_ = l_Lean_Expr_isApp(v___x_1092_);
if (v___x_1093_ == 0)
{
lean_dec_ref(v___x_1092_);
lean_dec(v_x_1077_);
goto v___jp_1089_;
}
else
{
lean_object* v_arg_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v_arg_1094_ = lean_ctor_get(v___x_1092_, 1);
lean_inc_ref(v_arg_1094_);
v___x_1095_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1092_);
v___x_1096_ = l_Lean_Expr_isApp(v___x_1095_);
if (v___x_1096_ == 0)
{
lean_dec_ref(v___x_1095_);
lean_dec_ref(v_arg_1094_);
lean_dec(v_x_1077_);
goto v___jp_1089_;
}
else
{
lean_object* v_arg_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v_arg_1097_ = lean_ctor_get(v___x_1095_, 1);
lean_inc_ref(v_arg_1097_);
v___x_1098_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1095_);
v___x_1099_ = l_Lean_Expr_isApp(v___x_1098_);
if (v___x_1099_ == 0)
{
lean_dec_ref(v___x_1098_);
lean_dec_ref(v_arg_1097_);
lean_dec_ref(v_arg_1094_);
lean_dec(v_x_1077_);
goto v___jp_1089_;
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1100_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1098_);
v___x_1101_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2));
v___x_1102_ = l_Lean_Expr_isConstOf(v___x_1100_, v___x_1101_);
lean_dec_ref(v___x_1100_);
if (v___x_1102_ == 0)
{
lean_dec_ref(v_arg_1097_);
lean_dec_ref(v_arg_1094_);
lean_dec(v_x_1077_);
goto v___jp_1089_;
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1103_ = l_Lean_Expr_cleanupAnnotations(v_arg_1097_);
v___x_1104_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4));
v___x_1105_ = l_Lean_Expr_isConstOf(v___x_1103_, v___x_1104_);
lean_dec_ref(v___x_1103_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_dec_ref(v_arg_1094_);
lean_dec(v_x_1077_);
v___x_1106_ = lean_box(0);
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
return v___x_1107_;
}
else
{
lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5));
v___x_1109_ = l_Lean_Expr_isAppOf(v_arg_1094_, v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1078_, v_a_1086_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1136_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1136_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1136_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v_natDef_1115_; uint8_t v___x_1116_; 
v_natDef_1115_ = lean_ctor_get(v_a_1111_, 5);
lean_inc_ref(v_natDef_1115_);
lean_dec(v_a_1111_);
v___x_1116_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_natDef_1115_, v_arg_1094_);
lean_dec_ref(v_natDef_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
lean_del_object(v___x_1113_);
lean_inc_ref(v_arg_1094_);
v___x_1117_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_arg_1094_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec_ref_known(v___x_1117_, 1);
v___x_1118_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6);
v___x_1119_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8);
v___x_1120_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v_x_1077_);
lean_ctor_set(v___x_1120_, 2, v___x_1119_);
v___x_1121_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1121_, 0, v_arg_1094_);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
lean_inc(v_a_1087_);
lean_inc_ref(v_a_1086_);
lean_inc(v_a_1085_);
lean_inc_ref(v_a_1084_);
lean_inc(v_a_1083_);
lean_inc_ref(v_a_1082_);
lean_inc(v_a_1081_);
lean_inc_ref(v_a_1080_);
lean_inc(v_a_1079_);
lean_inc(v_a_1078_);
v___x_1123_ = lean_grind_cutsat_assert_le(v___x_1122_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
return v___x_1123_;
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec_ref(v_arg_1094_);
lean_dec(v_x_1077_);
v_a_1124_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1117_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1117_);
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
lean_object* v___x_1132_; lean_object* v___x_1134_; 
lean_dec_ref(v_arg_1094_);
lean_dec(v_x_1077_);
v___x_1132_ = lean_box(0);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1132_);
v___x_1134_ = v___x_1113_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec_ref(v_arg_1094_);
lean_dec(v_x_1077_);
v_a_1137_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1110_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1110_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec_ref(v_arg_1094_);
lean_dec(v_x_1077_);
v___x_1145_ = lean_box(0);
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
}
}
}
}
}
v___jp_1089_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_box(0);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___boxed(lean_object* v_e_1147_, lean_object* v_x_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(v_e_1147_, v_x_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec(v_a_1149_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(lean_object* v_e_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1162_, v_a_1163_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1176_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1176_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1176_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_natToIntMap_1170_; uint8_t v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v_natToIntMap_1170_ = lean_ctor_get(v_a_1166_, 4);
lean_inc_ref(v_natToIntMap_1170_);
lean_dec(v_a_1166_);
v___x_1171_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27_spec__1___redArg(v_natToIntMap_1170_, v_e_1161_);
lean_dec_ref(v_natToIntMap_1170_);
v___x_1172_ = lean_box(v___x_1171_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1172_);
v___x_1174_ = v___x_1168_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
v_a_1177_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1165_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1165_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg___boxed(lean_object* v_e_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(v_e_1185_, v_a_1186_, v_a_1187_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec_ref(v_e_1185_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm(lean_object* v_e_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(v_e_1190_, v_a_1191_, v_a_1199_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___boxed(lean_object* v_e_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm(v_e_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_e_1203_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(lean_object* v_e_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v___x_1226_; 
lean_inc_ref(v_e_1216_);
v___x_1226_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1216_, v_a_1218_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v___y_1229_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1226_, 1);
v___x_1261_ = l_Lean_Expr_cleanupAnnotations(v_a_1227_);
v___x_1262_ = l_Lean_Expr_isApp(v___x_1261_);
if (v___x_1262_ == 0)
{
lean_dec_ref(v___x_1261_);
v___y_1229_ = v_a_1218_;
goto v___jp_1228_;
}
else
{
lean_object* v_arg_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_arg_1263_ = lean_ctor_get(v___x_1261_, 1);
lean_inc_ref(v_arg_1263_);
v___x_1264_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1261_);
v___x_1265_ = l_Lean_Expr_isApp(v___x_1264_);
if (v___x_1265_ == 0)
{
lean_dec_ref(v___x_1264_);
lean_dec_ref(v_arg_1263_);
v___y_1229_ = v_a_1218_;
goto v___jp_1228_;
}
else
{
lean_object* v_arg_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v_arg_1266_ = lean_ctor_get(v___x_1264_, 1);
lean_inc_ref(v_arg_1266_);
v___x_1267_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1264_);
v___x_1268_ = l_Lean_Expr_isApp(v___x_1267_);
if (v___x_1268_ == 0)
{
lean_dec_ref(v___x_1267_);
lean_dec_ref(v_arg_1266_);
lean_dec_ref(v_arg_1263_);
v___y_1229_ = v_a_1218_;
goto v___jp_1228_;
}
else
{
lean_object* v_arg_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v_arg_1269_ = lean_ctor_get(v___x_1267_, 1);
lean_inc_ref(v_arg_1269_);
v___x_1270_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1267_);
v___x_1271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5));
v___x_1272_ = l_Lean_Expr_isConstOf(v___x_1270_, v___x_1271_);
if (v___x_1272_ == 0)
{
uint8_t v___x_1273_; 
v___x_1273_ = l_Lean_Expr_isApp(v___x_1270_);
if (v___x_1273_ == 0)
{
lean_dec_ref(v___x_1270_);
lean_dec_ref(v_arg_1269_);
lean_dec_ref(v_arg_1266_);
lean_dec_ref(v_arg_1263_);
v___y_1229_ = v_a_1218_;
goto v___jp_1228_;
}
else
{
lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1274_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1270_);
v___x_1275_ = l_Lean_Expr_isApp(v___x_1274_);
if (v___x_1275_ == 0)
{
lean_dec_ref(v___x_1274_);
lean_dec_ref(v_arg_1269_);
lean_dec_ref(v_arg_1266_);
lean_dec_ref(v_arg_1263_);
v___y_1229_ = v_a_1218_;
goto v___jp_1228_;
}
else
{
lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1276_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1274_);
v___x_1277_ = l_Lean_Expr_isApp(v___x_1276_);
if (v___x_1277_ == 0)
{
lean_dec_ref(v___x_1276_);
lean_dec_ref(v_arg_1269_);
lean_dec_ref(v_arg_1266_);
lean_dec_ref(v_arg_1263_);
v___y_1229_ = v_a_1218_;
goto v___jp_1228_;
}
else
{
lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1278_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1276_);
v___x_1279_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8));
v___x_1280_ = l_Lean_Expr_isConstOf(v___x_1278_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11));
v___x_1282_ = l_Lean_Expr_isConstOf(v___x_1278_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1283_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14));
v___x_1284_ = l_Lean_Expr_isConstOf(v___x_1278_, v___x_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17));
v___x_1286_ = l_Lean_Expr_isConstOf(v___x_1278_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20));
v___x_1288_ = l_Lean_Expr_isConstOf(v___x_1278_, v___x_1287_);
lean_dec_ref(v___x_1278_);
if (v___x_1288_ == 0)
{
lean_dec_ref(v_arg_1269_);
lean_dec_ref(v_arg_1266_);
lean_dec_ref(v_arg_1263_);
v___y_1229_ = v_a_1218_;
goto v___jp_1228_;
}
else
{
lean_object* v___x_1289_; 
lean_dec_ref(v_e_1216_);
v___x_1289_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1269_, v_a_1218_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; uint8_t v___x_1291_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
v___x_1291_ = lean_unbox(v_a_1290_);
lean_dec(v_a_1290_);
if (v___x_1291_ == 0)
{
lean_dec_ref(v_arg_1266_);
lean_dec_ref(v_arg_1263_);
return v___x_1289_;
}
else
{
lean_object* v___x_1292_; 
lean_dec_ref_known(v___x_1289_, 1);
v___x_1292_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_arg_1266_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; uint8_t v___x_1294_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
v___x_1294_ = lean_unbox(v_a_1293_);
lean_dec(v_a_1293_);
if (v___x_1294_ == 0)
{
lean_dec_ref(v_arg_1263_);
return v___x_1292_;
}
else
{
lean_dec_ref_known(v___x_1292_, 1);
v_e_1216_ = v_arg_1263_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1263_);
return v___x_1292_;
}
}
}
else
{
lean_dec_ref(v_arg_1266_);
lean_dec_ref(v_arg_1263_);
return v___x_1289_;
}
}
}
else
{
lean_object* v___x_1296_; 
lean_dec_ref(v___x_1278_);
lean_dec_ref(v_e_1216_);
v___x_1296_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1269_, v_a_1218_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; uint8_t v___x_1298_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
v___x_1298_ = lean_unbox(v_a_1297_);
lean_dec(v_a_1297_);
if (v___x_1298_ == 0)
{
lean_dec_ref(v_arg_1266_);
lean_dec_ref(v_arg_1263_);
return v___x_1296_;
}
else
{
lean_object* v___x_1299_; 
lean_dec_ref_known(v___x_1296_, 1);
v___x_1299_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_arg_1266_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; uint8_t v___x_1301_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
v___x_1301_ = lean_unbox(v_a_1300_);
lean_dec(v_a_1300_);
if (v___x_1301_ == 0)
{
lean_dec_ref(v_arg_1263_);
return v___x_1299_;
}
else
{
lean_dec_ref_known(v___x_1299_, 1);
v_e_1216_ = v_arg_1263_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1263_);
return v___x_1299_;
}
}
}
else
{
lean_dec_ref(v_arg_1266_);
lean_dec_ref(v_arg_1263_);
return v___x_1296_;
}
}
}
else
{
lean_object* v___x_1303_; 
lean_dec_ref(v___x_1278_);
lean_dec_ref(v_e_1216_);
v___x_1303_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_1269_, v_a_1218_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; uint8_t v___x_1305_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
v___x_1305_ = lean_unbox(v_a_1304_);
lean_dec(v_a_1304_);
if (v___x_1305_ == 0)
{
lean_dec_ref(v_arg_1266_);
lean_dec_ref(v_arg_1263_);
return v___x_1303_;
}
else
{
lean_object* v___x_1306_; 
lean_dec_ref_known(v___x_1303_, 1);
v___x_1306_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_arg_1266_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; uint8_t v___x_1308_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
v___x_1308_ = lean_unbox(v_a_1307_);
lean_dec(v_a_1307_);
if (v___x_1308_ == 0)
{
lean_dec_ref(v_arg_1263_);
return v___x_1306_;
}
else
{
lean_dec_ref_known(v___x_1306_, 1);
v_e_1216_ = v_arg_1263_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1263_);
return v___x_1306_;
}
}
}
else
{
lean_dec_ref(v_arg_1266_);
lean_dec_ref(v_arg_1263_);
return v___x_1303_;
}
}
}
else
{
lean_object* v___x_1310_; 
lean_dec_ref(v___x_1278_);
lean_dec_ref(v_arg_1263_);
lean_dec_ref(v_e_1216_);
v___x_1310_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_1269_, v_a_1218_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; uint8_t v___x_1312_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
v___x_1312_ = lean_unbox(v_a_1311_);
lean_dec(v_a_1311_);
if (v___x_1312_ == 0)
{
lean_dec_ref(v_arg_1266_);
return v___x_1310_;
}
else
{
lean_dec_ref_known(v___x_1310_, 1);
v_e_1216_ = v_arg_1266_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1266_);
return v___x_1310_;
}
}
}
else
{
lean_object* v___x_1314_; 
lean_dec_ref(v___x_1278_);
lean_dec_ref(v_arg_1263_);
lean_dec_ref(v_e_1216_);
v___x_1314_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_1269_, v_a_1218_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; uint8_t v___x_1316_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc(v_a_1315_);
v___x_1316_ = lean_unbox(v_a_1315_);
lean_dec(v_a_1315_);
if (v___x_1316_ == 0)
{
lean_dec_ref(v_arg_1266_);
return v___x_1314_;
}
else
{
lean_dec_ref_known(v___x_1314_, 1);
v_e_1216_ = v_arg_1266_;
goto _start;
}
}
else
{
lean_dec_ref(v_arg_1266_);
return v___x_1314_;
}
}
}
}
}
}
else
{
lean_object* v___x_1318_; 
lean_dec_ref(v___x_1270_);
lean_dec_ref(v_arg_1269_);
lean_dec_ref(v_arg_1266_);
lean_dec_ref(v_arg_1263_);
v___x_1318_ = l_Lean_Meta_getIntValue_x3f(v_e_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1335_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1335_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1335_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
if (lean_obj_tag(v_a_1319_) == 1)
{
lean_object* v_val_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
v_val_1323_ = lean_ctor_get(v_a_1319_, 0);
lean_inc(v_val_1323_);
lean_dec_ref_known(v_a_1319_, 1);
v___x_1324_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__7);
v___x_1325_ = lean_int_dec_le(v___x_1324_, v_val_1323_);
lean_dec(v_val_1323_);
v___x_1326_ = lean_box(v___x_1325_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1326_);
v___x_1328_ = v___x_1321_;
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
else
{
uint8_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
lean_dec(v_a_1319_);
v___x_1330_ = 0;
v___x_1331_ = lean_box(v___x_1330_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1331_);
v___x_1333_ = v___x_1321_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
v_a_1336_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1318_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1318_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
}
}
}
v___jp_1228_:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1216_, v___y_1229_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1252_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1252_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1252_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = l_Lean_Expr_cleanupAnnotations(v_a_1231_);
v___x_1236_ = l_Lean_Expr_isApp(v___x_1235_);
if (v___x_1236_ == 0)
{
lean_dec_ref(v___x_1235_);
lean_del_object(v___x_1233_);
goto v___jp_1222_;
}
else
{
lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1237_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1235_);
v___x_1238_ = l_Lean_Expr_isApp(v___x_1237_);
if (v___x_1238_ == 0)
{
lean_dec_ref(v___x_1237_);
lean_del_object(v___x_1233_);
goto v___jp_1222_;
}
else
{
lean_object* v_arg_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v_arg_1239_ = lean_ctor_get(v___x_1237_, 1);
lean_inc_ref(v_arg_1239_);
v___x_1240_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1237_);
v___x_1241_ = l_Lean_Expr_isApp(v___x_1240_);
if (v___x_1241_ == 0)
{
lean_dec_ref(v___x_1240_);
lean_dec_ref(v_arg_1239_);
lean_del_object(v___x_1233_);
goto v___jp_1222_;
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1242_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1240_);
v___x_1243_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2));
v___x_1244_ = l_Lean_Expr_isConstOf(v___x_1242_, v___x_1243_);
lean_dec_ref(v___x_1242_);
if (v___x_1244_ == 0)
{
lean_dec_ref(v_arg_1239_);
lean_del_object(v___x_1233_);
goto v___jp_1222_;
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1245_ = l_Lean_Expr_cleanupAnnotations(v_arg_1239_);
v___x_1246_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__4));
v___x_1247_ = l_Lean_Expr_isConstOf(v___x_1245_, v___x_1246_);
lean_dec_ref(v___x_1245_);
v___x_1248_ = lean_box(v___x_1247_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1248_);
v___x_1250_ = v___x_1233_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
v_a_1253_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1230_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1230_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref(v_e_1216_);
v_a_1344_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1226_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1226_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
v___jp_1222_:
{
uint8_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = 0;
v___x_1224_ = lean_box(v___x_1223_);
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
return v___x_1225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg___boxed(lean_object* v_e_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_e_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0(lean_object* v_msg_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___f_1366_; lean_object* v___x_5805__overap_1367_; lean_object* v___x_1368_; 
v___f_1366_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___closed__0));
v___x_5805__overap_1367_ = lean_panic_fn_borrowed(v___f_1366_, v_msg_1360_);
lean_inc(v___y_1364_);
lean_inc_ref(v___y_1363_);
lean_inc(v___y_1362_);
lean_inc_ref(v___y_1361_);
v___x_1368_ = lean_apply_5(v___x_5805__overap_1367_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, lean_box(0));
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0___boxed(lean_object* v_msg_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0(v_msg_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
return v_res_1375_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3(void){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__2));
v___x_1380_ = lean_unsigned_to_nat(43u);
v___x_1381_ = lean_unsigned_to_nat(154u);
v___x_1382_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__1));
v___x_1383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__0));
v___x_1384_ = l_mkPanicMessageWithDecl(v___x_1383_, v___x_1382_, v___x_1381_, v___x_1380_, v___x_1379_);
return v___x_1384_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7(void){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1391_ = lean_box(0);
v___x_1392_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__6));
v___x_1393_ = l_Lean_mkConst(v___x_1392_, v___x_1391_);
return v___x_1393_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = lean_box(0);
v___x_1400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__9));
v___x_1401_ = l_Lean_mkConst(v___x_1400_, v___x_1399_);
return v___x_1401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13(void){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1407_ = lean_box(0);
v___x_1408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__12));
v___x_1409_ = l_Lean_mkConst(v___x_1408_, v___x_1407_);
return v___x_1409_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16(void){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1415_ = lean_box(0);
v___x_1416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__15));
v___x_1417_ = l_Lean_mkConst(v___x_1416_, v___x_1415_);
return v___x_1417_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = lean_box(0);
v___x_1424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__18));
v___x_1425_ = l_Lean_mkConst(v___x_1424_, v___x_1423_);
return v___x_1425_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = lean_box(0);
v___x_1432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__21));
v___x_1433_ = l_Lean_mkConst(v___x_1432_, v___x_1431_);
return v___x_1433_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25(void){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1439_ = lean_box(0);
v___x_1440_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__24));
v___x_1441_ = l_Lean_mkConst(v___x_1440_, v___x_1439_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(lean_object* v_e_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___x_1455_; 
lean_inc_ref(v_e_1442_);
v___x_1455_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1442_, v_a_1444_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1580_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1458_ = v___x_1455_;
v_isShared_1459_ = v_isSharedCheck_1580_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1455_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1580_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v___x_1486_ = l_Lean_Expr_cleanupAnnotations(v_a_1456_);
v___x_1487_ = l_Lean_Expr_isApp(v___x_1486_);
if (v___x_1487_ == 0)
{
lean_dec_ref(v___x_1486_);
lean_del_object(v___x_1458_);
v___y_1461_ = v_a_1443_;
v___y_1462_ = v_a_1444_;
v___y_1463_ = v_a_1445_;
v___y_1464_ = v_a_1446_;
goto v___jp_1460_;
}
else
{
lean_object* v_arg_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
v_arg_1488_ = lean_ctor_get(v___x_1486_, 1);
lean_inc_ref(v_arg_1488_);
v___x_1489_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1486_);
v___x_1490_ = l_Lean_Expr_isApp(v___x_1489_);
if (v___x_1490_ == 0)
{
lean_dec_ref(v___x_1489_);
lean_dec_ref(v_arg_1488_);
lean_del_object(v___x_1458_);
v___y_1461_ = v_a_1443_;
v___y_1462_ = v_a_1444_;
v___y_1463_ = v_a_1445_;
v___y_1464_ = v_a_1446_;
goto v___jp_1460_;
}
else
{
lean_object* v_arg_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; 
v_arg_1491_ = lean_ctor_get(v___x_1489_, 1);
lean_inc_ref(v_arg_1491_);
v___x_1492_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1489_);
v___x_1493_ = l_Lean_Expr_isApp(v___x_1492_);
if (v___x_1493_ == 0)
{
lean_dec_ref(v___x_1492_);
lean_dec_ref(v_arg_1491_);
lean_dec_ref(v_arg_1488_);
lean_del_object(v___x_1458_);
v___y_1461_ = v_a_1443_;
v___y_1462_ = v_a_1444_;
v___y_1463_ = v_a_1445_;
v___y_1464_ = v_a_1446_;
goto v___jp_1460_;
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1494_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1492_);
v___x_1495_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5));
v___x_1496_ = l_Lean_Expr_isConstOf(v___x_1494_, v___x_1495_);
if (v___x_1496_ == 0)
{
uint8_t v___x_1497_; 
lean_del_object(v___x_1458_);
v___x_1497_ = l_Lean_Expr_isApp(v___x_1494_);
if (v___x_1497_ == 0)
{
lean_dec_ref(v___x_1494_);
lean_dec_ref(v_arg_1491_);
lean_dec_ref(v_arg_1488_);
v___y_1461_ = v_a_1443_;
v___y_1462_ = v_a_1444_;
v___y_1463_ = v_a_1445_;
v___y_1464_ = v_a_1446_;
goto v___jp_1460_;
}
else
{
lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___x_1498_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1494_);
v___x_1499_ = l_Lean_Expr_isApp(v___x_1498_);
if (v___x_1499_ == 0)
{
lean_dec_ref(v___x_1498_);
lean_dec_ref(v_arg_1491_);
lean_dec_ref(v_arg_1488_);
v___y_1461_ = v_a_1443_;
v___y_1462_ = v_a_1444_;
v___y_1463_ = v_a_1445_;
v___y_1464_ = v_a_1446_;
goto v___jp_1460_;
}
else
{
lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1500_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1498_);
v___x_1501_ = l_Lean_Expr_isApp(v___x_1500_);
if (v___x_1501_ == 0)
{
lean_dec_ref(v___x_1500_);
lean_dec_ref(v_arg_1491_);
lean_dec_ref(v_arg_1488_);
v___y_1461_ = v_a_1443_;
v___y_1462_ = v_a_1444_;
v___y_1463_ = v_a_1445_;
v___y_1464_ = v_a_1446_;
goto v___jp_1460_;
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1502_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1500_);
v___x_1503_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__8));
v___x_1504_ = l_Lean_Expr_isConstOf(v___x_1502_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__11));
v___x_1506_ = l_Lean_Expr_isConstOf(v___x_1502_, v___x_1505_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1507_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__14));
v___x_1508_ = l_Lean_Expr_isConstOf(v___x_1502_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__17));
v___x_1510_ = l_Lean_Expr_isConstOf(v___x_1502_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__20));
v___x_1512_ = l_Lean_Expr_isConstOf(v___x_1502_, v___x_1511_);
lean_dec_ref(v___x_1502_);
if (v___x_1512_ == 0)
{
lean_dec_ref(v_arg_1491_);
lean_dec_ref(v_arg_1488_);
v___y_1461_ = v_a_1443_;
v___y_1462_ = v_a_1444_;
v___y_1463_ = v_a_1445_;
v___y_1464_ = v_a_1446_;
goto v___jp_1460_;
}
else
{
lean_object* v___x_1513_; 
lean_dec_ref(v_e_1442_);
lean_inc_ref(v_arg_1491_);
v___x_1513_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1491_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1515_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1513_, 1);
lean_inc_ref(v_arg_1488_);
v___x_1515_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1488_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
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
v___x_1520_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__10);
v___x_1521_ = l_Lean_mkApp4(v___x_1520_, v_arg_1491_, v_arg_1488_, v_a_1514_, v_a_1516_);
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
lean_dec_ref(v_arg_1491_);
lean_dec_ref(v_arg_1488_);
return v___x_1515_;
}
}
else
{
lean_dec_ref(v_arg_1491_);
lean_dec_ref(v_arg_1488_);
return v___x_1513_;
}
}
}
else
{
lean_object* v___x_1526_; 
lean_dec_ref(v___x_1502_);
lean_dec_ref(v_e_1442_);
lean_inc_ref(v_arg_1491_);
v___x_1526_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1491_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1528_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
lean_inc_ref(v_arg_1488_);
v___x_1528_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1488_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
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
v___x_1533_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__13);
v___x_1534_ = l_Lean_mkApp4(v___x_1533_, v_arg_1491_, v_arg_1488_, v_a_1527_, v_a_1529_);
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
lean_dec_ref(v_arg_1491_);
lean_dec_ref(v_arg_1488_);
return v___x_1528_;
}
}
else
{
lean_dec_ref(v_arg_1491_);
lean_dec_ref(v_arg_1488_);
return v___x_1526_;
}
}
}
else
{
lean_object* v___x_1539_; 
lean_dec_ref(v___x_1502_);
lean_dec_ref(v_e_1442_);
lean_inc_ref(v_arg_1491_);
v___x_1539_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1491_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1541_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1539_, 1);
lean_inc_ref(v_arg_1488_);
v___x_1541_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1488_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1551_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1551_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1551_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1546_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__16);
v___x_1547_ = l_Lean_mkApp4(v___x_1546_, v_arg_1491_, v_arg_1488_, v_a_1540_, v_a_1542_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1547_);
v___x_1549_ = v___x_1544_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
else
{
lean_dec(v_a_1540_);
lean_dec_ref(v_arg_1491_);
lean_dec_ref(v_arg_1488_);
return v___x_1541_;
}
}
else
{
lean_dec_ref(v_arg_1491_);
lean_dec_ref(v_arg_1488_);
return v___x_1539_;
}
}
}
else
{
lean_object* v___x_1552_; 
lean_dec_ref(v___x_1502_);
lean_dec_ref(v_e_1442_);
lean_inc_ref(v_arg_1491_);
v___x_1552_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1491_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1562_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1562_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1562_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1557_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__19);
v___x_1558_ = l_Lean_mkApp3(v___x_1557_, v_arg_1491_, v_arg_1488_, v_a_1553_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1558_);
v___x_1560_ = v___x_1555_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
else
{
lean_dec_ref(v_arg_1491_);
lean_dec_ref(v_arg_1488_);
return v___x_1552_;
}
}
}
else
{
lean_object* v___x_1563_; 
lean_dec_ref(v___x_1502_);
lean_dec_ref(v_e_1442_);
lean_inc_ref(v_arg_1491_);
v___x_1563_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_arg_1491_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1573_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1573_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1573_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1568_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__22);
v___x_1569_ = l_Lean_mkApp3(v___x_1568_, v_arg_1491_, v_arg_1488_, v_a_1564_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1569_);
v___x_1571_ = v___x_1566_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
else
{
lean_dec_ref(v_arg_1491_);
lean_dec_ref(v_arg_1488_);
return v___x_1563_;
}
}
}
}
}
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
lean_dec_ref(v___x_1494_);
lean_dec_ref(v_arg_1491_);
lean_dec_ref(v_arg_1488_);
v___x_1574_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__25);
v___x_1575_ = l_Lean_eagerReflBoolTrue;
v___x_1576_ = l_Lean_mkAppB(v___x_1574_, v_e_1442_, v___x_1575_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1576_);
v___x_1578_ = v___x_1458_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
v___jp_1460_:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1442_, v___y_1462_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1485_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1485_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1485_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1470_ = l_Lean_Expr_cleanupAnnotations(v_a_1466_);
v___x_1471_ = l_Lean_Expr_isApp(v___x_1470_);
if (v___x_1471_ == 0)
{
lean_dec_ref(v___x_1470_);
lean_del_object(v___x_1468_);
v___y_1449_ = v___y_1461_;
v___y_1450_ = v___y_1462_;
v___y_1451_ = v___y_1463_;
v___y_1452_ = v___y_1464_;
goto v___jp_1448_;
}
else
{
lean_object* v_arg_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
v_arg_1472_ = lean_ctor_get(v___x_1470_, 1);
lean_inc_ref(v_arg_1472_);
v___x_1473_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1470_);
v___x_1474_ = l_Lean_Expr_isApp(v___x_1473_);
if (v___x_1474_ == 0)
{
lean_dec_ref(v___x_1473_);
lean_dec_ref(v_arg_1472_);
lean_del_object(v___x_1468_);
v___y_1449_ = v___y_1461_;
v___y_1450_ = v___y_1462_;
v___y_1451_ = v___y_1463_;
v___y_1452_ = v___y_1464_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1475_; uint8_t v___x_1476_; 
v___x_1475_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1473_);
v___x_1476_ = l_Lean_Expr_isApp(v___x_1475_);
if (v___x_1476_ == 0)
{
lean_dec_ref(v___x_1475_);
lean_dec_ref(v_arg_1472_);
lean_del_object(v___x_1468_);
v___y_1449_ = v___y_1461_;
v___y_1450_ = v___y_1462_;
v___y_1451_ = v___y_1463_;
v___y_1452_ = v___y_1464_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1477_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1475_);
v___x_1478_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2));
v___x_1479_ = l_Lean_Expr_isConstOf(v___x_1477_, v___x_1478_);
lean_dec_ref(v___x_1477_);
if (v___x_1479_ == 0)
{
lean_dec_ref(v_arg_1472_);
lean_del_object(v___x_1468_);
v___y_1449_ = v___y_1461_;
v___y_1450_ = v___y_1462_;
v___y_1451_ = v___y_1463_;
v___y_1452_ = v___y_1464_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___x_1480_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__7);
v___x_1481_ = l_Lean_Expr_app___override(v___x_1480_, v_arg_1472_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1481_);
v___x_1483_ = v___x_1468_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
}
}
else
{
return v___x_1465_;
}
}
}
}
else
{
lean_dec_ref(v_e_1442_);
return v___x_1455_;
}
v___jp_1448_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___closed__3);
v___x_1454_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go_spec__0(v___x_1453_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
return v___x_1454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go___boxed(lean_object* v_e_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_e_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(lean_object* v_e_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v___x_1594_; 
lean_inc_ref(v_e_1588_);
v___x_1594_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_isNonneg(v_e_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1622_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1622_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1622_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
uint8_t v___x_1599_; 
v___x_1599_ = lean_unbox(v_a_1595_);
lean_dec(v_a_1595_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1602_; 
lean_dec_ref(v_e_1588_);
v___x_1600_ = lean_box(0);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v___x_1600_);
v___x_1602_ = v___x_1597_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
else
{
lean_object* v___x_1604_; 
lean_del_object(v___x_1597_);
v___x_1604_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f_go(v_e_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1613_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1607_ = v___x_1604_;
v_isShared_1608_ = v_isSharedCheck_1613_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1613_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1609_, 0, v_a_1605_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v___x_1609_);
v___x_1611_ = v___x_1607_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
v_a_1614_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1604_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1604_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec_ref(v_e_1588_);
v_a_1623_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1594_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1594_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg___boxed(lean_object* v_e_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(v_e_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f(lean_object* v_e_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(v_e_1638_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___boxed(lean_object* v_e_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f(v_e_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec(v_a_1652_);
return v_res_1663_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = lean_box(0);
v___x_1670_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__1));
v___x_1671_ = l_Lean_mkConst(v___x_1670_, v___x_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(lean_object* v_e_1672_, lean_object* v_x_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2));
v___x_1686_ = l_Lean_Expr_isAppOf(v_e_1672_, v___x_1685_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; uint8_t v___x_1688_; 
v___x_1687_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat_0__Lean_Meta_Grind_Arith_Cutsat_natToInt_x27___closed__5));
v___x_1688_ = l_Lean_Expr_isAppOf(v_e_1672_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; 
lean_inc_ref(v_e_1672_);
v___x_1689_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNonnegThm_x3f___redArg(v_e_1672_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1713_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1713_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1713_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
if (lean_obj_tag(v_a_1690_) == 1)
{
lean_object* v_val_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1708_; 
lean_del_object(v___x_1692_);
v_val_1694_ = lean_ctor_get(v_a_1690_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_a_1690_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1696_ = v_a_1690_;
v_isShared_1697_ = v_isSharedCheck_1708_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_val_1694_);
lean_dec(v_a_1690_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1708_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1698_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___closed__2);
v___x_1699_ = l_Lean_mkAppB(v___x_1698_, v_e_1672_, v_val_1694_);
v___x_1700_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__6);
v___x_1701_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__8);
v___x_1702_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1700_);
lean_ctor_set(v___x_1702_, 1, v_x_1673_);
lean_ctor_set(v___x_1702_, 2, v___x_1701_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set_tag(v___x_1696_, 4);
lean_ctor_set(v___x_1696_, 0, v___x_1699_);
v___x_1704_ = v___x_1696_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1699_);
v___x_1704_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1702_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
lean_inc(v_a_1683_);
lean_inc_ref(v_a_1682_);
lean_inc(v_a_1681_);
lean_inc_ref(v_a_1680_);
lean_inc(v_a_1679_);
lean_inc_ref(v_a_1678_);
lean_inc(v_a_1677_);
lean_inc_ref(v_a_1676_);
lean_inc(v_a_1675_);
lean_inc(v_a_1674_);
v___x_1706_ = lean_grind_cutsat_assert_le(v___x_1705_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
return v___x_1706_;
}
}
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1711_; 
lean_dec(v_a_1690_);
lean_dec(v_x_1673_);
lean_dec_ref(v_e_1672_);
v___x_1709_ = lean_box(0);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1709_);
v___x_1711_ = v___x_1692_;
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
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec(v_x_1673_);
lean_dec_ref(v_e_1672_);
v_a_1714_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1689_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1689_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
else
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_dec(v_x_1673_);
lean_dec_ref(v_e_1672_);
v___x_1722_ = lean_box(0);
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
return v___x_1723_;
}
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
lean_dec(v_x_1673_);
lean_dec_ref(v_e_1672_);
v___x_1724_ = lean_box(0);
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
return v___x_1725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg___boxed(lean_object* v_e_1726_, lean_object* v_x_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(v_e_1726_, v_x_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_);
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
