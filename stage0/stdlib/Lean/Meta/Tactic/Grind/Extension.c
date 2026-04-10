// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Extension
// Imports: public import Lean.Meta.Tactic.Grind.Theorems
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Origin_key(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
extern lean_object* l_Lean_Meta_Grind_instInhabitedOrigin_default;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedCasesTypes_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedCasesTypes;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_insert(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_insert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedSymbolPriorities;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SymbolPriorities_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instBEqEMatchTheoremKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremKind___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instBEqEMatchTheoremKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremKind = (const lean_object*)&l_Lean_Meta_Grind_instBEqEMatchTheoremKind___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Meta.Grind.EMatchTheoremKind.rightLeft"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean.Meta.Grind.EMatchTheoremKind.leftRight"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__2_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Grind.EMatchTheoremKind.eqBwd"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__4_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Meta.Grind.EMatchTheoremKind.fwd"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__6_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Meta.Grind.EMatchTheoremKind.user"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__8_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Grind.EMatchTheoremKind.eqLhs"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__10_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__11_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13;
static lean_once_cell_t l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Grind.EMatchTheoremKind.eqRhs"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__15_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__16_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Meta.Grind.EMatchTheoremKind.eqBoth"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__18_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__19_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__20_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Meta.Grind.EMatchTheoremKind.bwd"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__21_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__22_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__23_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Lean.Meta.Grind.EMatchTheoremKind.default"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__24_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__25_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__26_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instReprEMatchTheoremKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremKind___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4;
static lean_once_cell_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5;
static lean_once_cell_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6;
static lean_once_cell_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7;
static lean_once_cell_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8;
static lean_once_cell_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9;
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instHashableEMatchTheoremKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremKind___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instHashableEMatchTheoremKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremKind = (const lean_object*)&l_Lean_Meta_Grind_instHashableEMatchTheoremKind___closed__0_value;
static const lean_array_object l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__1_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedCnstrRHS_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedCnstrRHS;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqCnstrRHS_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqCnstrRHS_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instBEqCnstrRHS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instBEqCnstrRHS_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instBEqCnstrRHS___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instBEqCnstrRHS___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instBEqCnstrRHS = (const lean_object*)&l_Lean_Meta_Grind_instBEqCnstrRHS___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__9 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__10 = (const lean_object*)&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "levelNames"};
static const lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7;
static const lean_string_object l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "numMVars"};
static const lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10;
static const lean_string_object l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "expr"};
static const lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13;
static const lean_string_object l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15;
static lean_once_cell_t l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16;
static const lean_ctor_object l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__18_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instReprCnstrRHS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instReprCnstrRHS_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instReprCnstrRHS___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instReprCnstrRHS = (const lean_object*)&l_Lean_Meta_Grind_instReprCnstrRHS___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Lean.Meta.Grind.EMatchTheoremConstraint.notDefEq"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Lean.Meta.Grind.EMatchTheoremConstraint.defEq"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__3_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Lean.Meta.Grind.EMatchTheoremConstraint.sizeLt"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__6_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Lean.Meta.Grind.EMatchTheoremConstraint.depthLt"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__9_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Lean.Meta.Grind.EMatchTheoremConstraint.genLt"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__12_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__14_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Lean.Meta.Grind.EMatchTheoremConstraint.isGround"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__15_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__16_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Lean.Meta.Grind.EMatchTheoremConstraint.isValue"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__18_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__19_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__20_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Lean.Meta.Grind.EMatchTheoremConstraint.maxInsts"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__21_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__22_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__23_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Lean.Meta.Grind.EMatchTheoremConstraint.guard"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__24_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__25_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__25_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__26_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Lean.Meta.Grind.EMatchTheoremConstraint.check"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__27_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__27_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__28_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__29_value;
static const lean_string_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "Lean.Meta.Grind.EMatchTheoremConstraint.notValue"};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__30_value)}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__31_value;
static const lean_ctor_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__31_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__32 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__32_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instReprEMatchTheoremConstraint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint = (const lean_object*)&l_Lean_Meta_Grind_instReprEMatchTheoremConstraint___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint = (const lean_object*)&l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedEMatchTheorem;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__1_value),((lean_object*)&l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__2_value),((lean_object*)&l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__3_value),((lean_object*)&l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__4_value)}};
static const lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem = (const lean_object*)&l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedInjectiveTheorem;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__1_value),((lean_object*)&l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__2_value),((lean_object*)&l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__3_value),((lean_object*)&l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__4_value)}};
static const lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem = (const lean_object*)&l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ext_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ext_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_funCC_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_funCC_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_cases_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_cases_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ematch_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ematch_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_inj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_inj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_instInhabitedEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_instInhabitedEntry_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedEntry_default = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instInhabitedEntry = (const lean_object*)&l_Lean_Meta_Grind_instInhabitedEntry_default___closed__0_value;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5 = (const lean_object*)&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6 = (const lean_object*)&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6_value;
static lean_once_cell_t l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Tactic.Grind.Theorems"};
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Grind.Theorems.insert"};
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionState_addEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__4_value;
static const lean_array_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkExtension___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__12;
static lean_once_cell_t l_Lean_Meta_Grind_mkExtension___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__13;
static const lean_string_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__14_value;
static const lean_string_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__16_value;
static const lean_string_object l_Lean_Meta_Grind_mkExtension___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___auto__1___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkExtension___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__18;
static lean_once_cell_t l_Lean_Meta_Grind_mkExtension___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__19;
static lean_once_cell_t l_Lean_Meta_Grind_mkExtension___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__20;
static lean_once_cell_t l_Lean_Meta_Grind_mkExtension___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__21;
static lean_once_cell_t l_Lean_Meta_Grind_mkExtension___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__22;
static lean_once_cell_t l_Lean_Meta_Grind_mkExtension___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__23;
static lean_once_cell_t l_Lean_Meta_Grind_mkExtension___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__24;
static lean_once_cell_t l_Lean_Meta_Grind_mkExtension___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__25;
static lean_once_cell_t l_Lean_Meta_Grind_mkExtension___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__26;
static lean_once_cell_t l_Lean_Meta_Grind_mkExtension___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__27;
static lean_once_cell_t l_Lean_Meta_Grind_mkExtension___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkExtension___auto__1___closed__28;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___auto__1;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_mkExtension___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.Tactic.Grind.Extension"};
static const lean_object* l_Lean_Meta_Grind_mkExtension___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_mkExtension___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Meta.Grind.mkExtension"};
static const lean_object* l_Lean_Meta_Grind_mkExtension___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_mkExtension___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkExtension___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_mkExtension___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkExtension___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkExtension___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_mkExtension___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_mkExtension___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkExtension___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_mkExtension___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_ExtensionState_addEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_mkExtension___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_mkExtension___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1;
static const lean_string_object l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "` is not marked with the `[grind]` attribute"};
static const lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0, &l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1, &l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCasesTypes(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = l_Lean_Meta_Grind_instInhabitedCasesTypes_default;
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_6_, lean_object* v_x_7_, lean_object* v_x_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_ks_10_; lean_object* v_vs_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_35_; 
v_ks_10_ = lean_ctor_get(v_x_6_, 0);
v_vs_11_ = lean_ctor_get(v_x_6_, 1);
v_isSharedCheck_35_ = !lean_is_exclusive(v_x_6_);
if (v_isSharedCheck_35_ == 0)
{
v___x_13_ = v_x_6_;
v_isShared_14_ = v_isSharedCheck_35_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_vs_11_);
lean_inc(v_ks_10_);
lean_dec(v_x_6_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_35_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_15_ = lean_array_get_size(v_ks_10_);
v___x_16_ = lean_nat_dec_lt(v_x_7_, v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_20_; 
lean_dec(v_x_7_);
v___x_17_ = lean_array_push(v_ks_10_, v_x_8_);
v___x_18_ = lean_array_push(v_vs_11_, v_x_9_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v___x_18_);
lean_ctor_set(v___x_13_, 0, v___x_17_);
v___x_20_ = v___x_13_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
else
{
lean_object* v_k_x27_22_; uint8_t v___x_23_; 
v_k_x27_22_ = lean_array_fget_borrowed(v_ks_10_, v_x_7_);
v___x_23_ = lean_name_eq(v_x_8_, v_k_x27_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_25_; 
if (v_isShared_14_ == 0)
{
v___x_25_ = v___x_13_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_ks_10_);
lean_ctor_set(v_reuseFailAlloc_29_, 1, v_vs_11_);
v___x_25_ = v_reuseFailAlloc_29_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_add(v_x_7_, v___x_26_);
lean_dec(v_x_7_);
v_x_6_ = v___x_25_;
v_x_7_ = v___x_27_;
goto _start;
}
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_33_; 
v___x_30_ = lean_array_fset(v_ks_10_, v_x_7_, v_x_8_);
v___x_31_ = lean_array_fset(v_vs_11_, v_x_7_, v_x_9_);
lean_dec(v_x_7_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v___x_31_);
lean_ctor_set(v___x_13_, 0, v___x_30_);
v___x_33_ = v___x_13_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_n_36_, lean_object* v_k_37_, lean_object* v_v_38_){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_unsigned_to_nat(0u);
v___x_40_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_n_36_, v___x_39_, v_k_37_, v_v_38_);
return v___x_40_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_41_; uint64_t v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(1723u);
v___x_42_ = lean_uint64_of_nat(v___x_41_);
return v___x_42_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_43_; size_t v___x_44_; size_t v___x_45_; 
v___x_43_ = ((size_t)5ULL);
v___x_44_ = ((size_t)1ULL);
v___x_45_ = lean_usize_shift_left(v___x_44_, v___x_43_);
return v___x_45_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_46_; size_t v___x_47_; size_t v___x_48_; 
v___x_46_ = ((size_t)1ULL);
v___x_47_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0);
v___x_48_ = lean_usize_sub(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(lean_object* v_x_50_, size_t v_x_51_, size_t v_x_52_, lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
if (lean_obj_tag(v_x_50_) == 0)
{
lean_object* v_es_55_; size_t v___x_56_; size_t v___x_57_; size_t v___x_58_; size_t v___x_59_; lean_object* v_j_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_es_55_ = lean_ctor_get(v_x_50_, 0);
v___x_56_ = ((size_t)5ULL);
v___x_57_ = ((size_t)1ULL);
v___x_58_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1);
v___x_59_ = lean_usize_land(v_x_51_, v___x_58_);
v_j_60_ = lean_usize_to_nat(v___x_59_);
v___x_61_ = lean_array_get_size(v_es_55_);
v___x_62_ = lean_nat_dec_lt(v_j_60_, v___x_61_);
if (v___x_62_ == 0)
{
lean_dec(v_j_60_);
lean_dec(v_x_54_);
lean_dec(v_x_53_);
return v_x_50_;
}
else
{
lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_99_; 
lean_inc_ref(v_es_55_);
v_isSharedCheck_99_ = !lean_is_exclusive(v_x_50_);
if (v_isSharedCheck_99_ == 0)
{
lean_object* v_unused_100_; 
v_unused_100_ = lean_ctor_get(v_x_50_, 0);
lean_dec(v_unused_100_);
v___x_64_ = v_x_50_;
v_isShared_65_ = v_isSharedCheck_99_;
goto v_resetjp_63_;
}
else
{
lean_dec(v_x_50_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_99_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v_v_66_; lean_object* v___x_67_; lean_object* v_xs_x27_68_; lean_object* v___y_70_; 
v_v_66_ = lean_array_fget(v_es_55_, v_j_60_);
v___x_67_ = lean_box(0);
v_xs_x27_68_ = lean_array_fset(v_es_55_, v_j_60_, v___x_67_);
switch(lean_obj_tag(v_v_66_))
{
case 0:
{
lean_object* v_key_75_; lean_object* v_val_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_86_; 
v_key_75_ = lean_ctor_get(v_v_66_, 0);
v_val_76_ = lean_ctor_get(v_v_66_, 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v_v_66_);
if (v_isSharedCheck_86_ == 0)
{
v___x_78_ = v_v_66_;
v_isShared_79_ = v_isSharedCheck_86_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_val_76_);
lean_inc(v_key_75_);
lean_dec(v_v_66_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_86_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
uint8_t v___x_80_; 
v___x_80_ = lean_name_eq(v_x_53_, v_key_75_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_del_object(v___x_78_);
v___x_81_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_75_, v_val_76_, v_x_53_, v_x_54_);
v___x_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
v___y_70_ = v___x_82_;
goto v___jp_69_;
}
else
{
lean_object* v___x_84_; 
lean_dec(v_val_76_);
lean_dec(v_key_75_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v_x_54_);
lean_ctor_set(v___x_78_, 0, v_x_53_);
v___x_84_ = v___x_78_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_x_53_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_x_54_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
v___y_70_ = v___x_84_;
goto v___jp_69_;
}
}
}
}
case 1:
{
lean_object* v_node_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_97_; 
v_node_87_ = lean_ctor_get(v_v_66_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v_v_66_);
if (v_isSharedCheck_97_ == 0)
{
v___x_89_ = v_v_66_;
v_isShared_90_ = v_isSharedCheck_97_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_node_87_);
lean_dec(v_v_66_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_97_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
size_t v___x_91_; size_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_91_ = lean_usize_shift_right(v_x_51_, v___x_56_);
v___x_92_ = lean_usize_add(v_x_52_, v___x_57_);
v___x_93_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_node_87_, v___x_91_, v___x_92_, v_x_53_, v_x_54_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_93_);
v___x_95_ = v___x_89_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
v___y_70_ = v___x_95_;
goto v___jp_69_;
}
}
}
default: 
{
lean_object* v___x_98_; 
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v_x_53_);
lean_ctor_set(v___x_98_, 1, v_x_54_);
v___y_70_ = v___x_98_;
goto v___jp_69_;
}
}
v___jp_69_:
{
lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_71_ = lean_array_fset(v_xs_x27_68_, v_j_60_, v___y_70_);
lean_dec(v_j_60_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v___x_71_);
v___x_73_ = v___x_64_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
}
else
{
lean_object* v_ks_101_; lean_object* v_vs_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_122_; 
v_ks_101_ = lean_ctor_get(v_x_50_, 0);
v_vs_102_ = lean_ctor_get(v_x_50_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v_x_50_);
if (v_isSharedCheck_122_ == 0)
{
v___x_104_ = v_x_50_;
v_isShared_105_ = v_isSharedCheck_122_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_vs_102_);
lean_inc(v_ks_101_);
lean_dec(v_x_50_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_122_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_ks_101_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_vs_102_);
v___x_107_ = v_reuseFailAlloc_121_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v_newNode_108_; uint8_t v___y_110_; size_t v___x_116_; uint8_t v___x_117_; 
v_newNode_108_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1___redArg(v___x_107_, v_x_53_, v_x_54_);
v___x_116_ = ((size_t)7ULL);
v___x_117_ = lean_usize_dec_le(v___x_116_, v_x_52_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_118_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_108_);
v___x_119_ = lean_unsigned_to_nat(4u);
v___x_120_ = lean_nat_dec_lt(v___x_118_, v___x_119_);
lean_dec(v___x_118_);
v___y_110_ = v___x_120_;
goto v___jp_109_;
}
else
{
v___y_110_ = v___x_117_;
goto v___jp_109_;
}
v___jp_109_:
{
if (v___y_110_ == 0)
{
lean_object* v_ks_111_; lean_object* v_vs_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_ks_111_ = lean_ctor_get(v_newNode_108_, 0);
lean_inc_ref(v_ks_111_);
v_vs_112_ = lean_ctor_get(v_newNode_108_, 1);
lean_inc_ref(v_vs_112_);
lean_dec_ref(v_newNode_108_);
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__2);
v___x_115_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_x_52_, v_ks_111_, v_vs_112_, v___x_113_, v___x_114_);
lean_dec_ref(v_vs_112_);
lean_dec_ref(v_ks_111_);
return v___x_115_;
}
else
{
return v_newNode_108_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(size_t v_depth_123_, lean_object* v_keys_124_, lean_object* v_vals_125_, lean_object* v_i_126_, lean_object* v_entries_127_){
_start:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = lean_array_get_size(v_keys_124_);
v___x_129_ = lean_nat_dec_lt(v_i_126_, v___x_128_);
if (v___x_129_ == 0)
{
lean_dec(v_i_126_);
return v_entries_127_;
}
else
{
lean_object* v_k_130_; lean_object* v_v_131_; uint64_t v___y_133_; 
v_k_130_ = lean_array_fget_borrowed(v_keys_124_, v_i_126_);
v_v_131_ = lean_array_fget_borrowed(v_vals_125_, v_i_126_);
if (lean_obj_tag(v_k_130_) == 0)
{
uint64_t v___x_144_; 
v___x_144_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_133_ = v___x_144_;
goto v___jp_132_;
}
else
{
uint64_t v_hash_145_; 
v_hash_145_ = lean_ctor_get_uint64(v_k_130_, sizeof(void*)*2);
v___y_133_ = v_hash_145_;
goto v___jp_132_;
}
v___jp_132_:
{
size_t v_h_134_; size_t v___x_135_; lean_object* v___x_136_; size_t v___x_137_; size_t v___x_138_; size_t v___x_139_; size_t v_h_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_h_134_ = lean_uint64_to_usize(v___y_133_);
v___x_135_ = ((size_t)5ULL);
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = ((size_t)1ULL);
v___x_138_ = lean_usize_sub(v_depth_123_, v___x_137_);
v___x_139_ = lean_usize_mul(v___x_135_, v___x_138_);
v_h_140_ = lean_usize_shift_right(v_h_134_, v___x_139_);
v___x_141_ = lean_nat_add(v_i_126_, v___x_136_);
lean_dec(v_i_126_);
lean_inc(v_v_131_);
lean_inc(v_k_130_);
v___x_142_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_entries_127_, v_h_140_, v_depth_123_, v_k_130_, v_v_131_);
v_i_126_ = v___x_141_;
v_entries_127_ = v___x_142_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_146_, lean_object* v_keys_147_, lean_object* v_vals_148_, lean_object* v_i_149_, lean_object* v_entries_150_){
_start:
{
size_t v_depth_boxed_151_; lean_object* v_res_152_; 
v_depth_boxed_151_ = lean_unbox_usize(v_depth_146_);
lean_dec(v_depth_146_);
v_res_152_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_151_, v_keys_147_, v_vals_148_, v_i_149_, v_entries_150_);
lean_dec_ref(v_vals_148_);
lean_dec_ref(v_keys_147_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_153_, lean_object* v_x_154_, lean_object* v_x_155_, lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
size_t v_x_371__boxed_158_; size_t v_x_372__boxed_159_; lean_object* v_res_160_; 
v_x_371__boxed_158_ = lean_unbox_usize(v_x_154_);
lean_dec(v_x_154_);
v_x_372__boxed_159_ = lean_unbox_usize(v_x_155_);
lean_dec(v_x_155_);
v_res_160_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_153_, v_x_371__boxed_158_, v_x_372__boxed_159_, v_x_156_, v_x_157_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
uint64_t v___y_165_; 
if (lean_obj_tag(v_x_162_) == 0)
{
uint64_t v___x_169_; 
v___x_169_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_165_ = v___x_169_;
goto v___jp_164_;
}
else
{
uint64_t v_hash_170_; 
v_hash_170_ = lean_ctor_get_uint64(v_x_162_, sizeof(void*)*2);
v___y_165_ = v_hash_170_;
goto v___jp_164_;
}
v___jp_164_:
{
size_t v___x_166_; size_t v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_uint64_to_usize(v___y_165_);
v___x_167_ = ((size_t)1ULL);
v___x_168_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_161_, v___x_166_, v___x_167_, v_x_162_, v_x_163_);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_insert(lean_object* v_s_171_, lean_object* v_declName_172_, uint8_t v_eager_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_box(v_eager_173_);
v___x_175_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_s_171_, v_declName_172_, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_insert___boxed(lean_object* v_s_176_, lean_object* v_declName_177_, lean_object* v_eager_178_){
_start:
{
uint8_t v_eager_boxed_179_; lean_object* v_res_180_; 
v_eager_boxed_179_ = lean_unbox(v_eager_178_);
v_res_180_ = l_Lean_Meta_Grind_CasesTypes_insert(v_s_176_, v_declName_177_, v_eager_boxed_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0(lean_object* v_00_u03b2_181_, lean_object* v_x_182_, lean_object* v_x_183_, lean_object* v_x_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_x_182_, v_x_183_, v_x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0(lean_object* v_00_u03b2_186_, lean_object* v_x_187_, size_t v_x_188_, size_t v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_187_, v_x_188_, v_x_189_, v_x_190_, v_x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_193_, lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
size_t v_x_570__boxed_199_; size_t v_x_571__boxed_200_; lean_object* v_res_201_; 
v_x_570__boxed_199_ = lean_unbox_usize(v_x_195_);
lean_dec(v_x_195_);
v_x_571__boxed_200_ = lean_unbox_usize(v_x_196_);
lean_dec(v_x_196_);
v_res_201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0(v_00_u03b2_193_, v_x_194_, v_x_570__boxed_199_, v_x_571__boxed_200_, v_x_197_, v_x_198_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_202_, lean_object* v_n_203_, lean_object* v_k_204_, lean_object* v_v_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1___redArg(v_n_203_, v_k_204_, v_v_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_207_, size_t v_depth_208_, lean_object* v_keys_209_, lean_object* v_vals_210_, lean_object* v_heq_211_, lean_object* v_i_212_, lean_object* v_entries_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_depth_208_, v_keys_209_, v_vals_210_, v_i_212_, v_entries_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_215_, lean_object* v_depth_216_, lean_object* v_keys_217_, lean_object* v_vals_218_, lean_object* v_heq_219_, lean_object* v_i_220_, lean_object* v_entries_221_){
_start:
{
size_t v_depth_boxed_222_; lean_object* v_res_223_; 
v_depth_boxed_222_ = lean_unbox_usize(v_depth_216_);
lean_dec(v_depth_216_);
v_res_223_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2(v_00_u03b2_215_, v_depth_boxed_222_, v_keys_217_, v_vals_218_, v_heq_219_, v_i_220_, v_entries_221_);
lean_dec_ref(v_vals_218_);
lean_dec_ref(v_keys_217_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_224_, lean_object* v_x_225_, lean_object* v_x_226_, lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_225_, v_x_226_, v_x_227_, v_x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0(void){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_230_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0, &l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default(void){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1, &l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities(void){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default;
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SymbolPriorities_insert(lean_object* v_s_235_, lean_object* v_declName_236_, lean_object* v_prio_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_s_235_, v_declName_236_, v_prio_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(lean_object* v_x_239_){
_start:
{
switch(lean_obj_tag(v_x_239_))
{
case 0:
{
lean_object* v___x_240_; 
v___x_240_ = lean_unsigned_to_nat(0u);
return v___x_240_;
}
case 1:
{
lean_object* v___x_241_; 
v___x_241_ = lean_unsigned_to_nat(1u);
return v___x_241_;
}
case 2:
{
lean_object* v___x_242_; 
v___x_242_ = lean_unsigned_to_nat(2u);
return v___x_242_;
}
case 3:
{
lean_object* v___x_243_; 
v___x_243_ = lean_unsigned_to_nat(3u);
return v___x_243_;
}
case 4:
{
lean_object* v___x_244_; 
v___x_244_ = lean_unsigned_to_nat(4u);
return v___x_244_;
}
case 5:
{
lean_object* v___x_245_; 
v___x_245_ = lean_unsigned_to_nat(5u);
return v___x_245_;
}
case 6:
{
lean_object* v___x_246_; 
v___x_246_ = lean_unsigned_to_nat(6u);
return v___x_246_;
}
case 7:
{
lean_object* v___x_247_; 
v___x_247_ = lean_unsigned_to_nat(7u);
return v___x_247_;
}
case 8:
{
lean_object* v___x_248_; 
v___x_248_ = lean_unsigned_to_nat(8u);
return v___x_248_;
}
default: 
{
lean_object* v___x_249_; 
v___x_249_ = lean_unsigned_to_nat(9u);
return v___x_249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx___boxed(lean_object* v_x_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(v_x_250_);
lean_dec(v_x_250_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(lean_object* v_t_252_, lean_object* v_k_253_){
_start:
{
switch(lean_obj_tag(v_t_252_))
{
case 0:
{
uint8_t v_gen_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_gen_254_ = lean_ctor_get_uint8(v_t_252_, 0);
v___x_255_ = lean_box(v_gen_254_);
v___x_256_ = lean_apply_1(v_k_253_, v___x_255_);
return v___x_256_;
}
case 1:
{
uint8_t v_gen_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_gen_257_ = lean_ctor_get_uint8(v_t_252_, 0);
v___x_258_ = lean_box(v_gen_257_);
v___x_259_ = lean_apply_1(v_k_253_, v___x_258_);
return v___x_259_;
}
case 2:
{
uint8_t v_gen_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_gen_260_ = lean_ctor_get_uint8(v_t_252_, 0);
v___x_261_ = lean_box(v_gen_260_);
v___x_262_ = lean_apply_1(v_k_253_, v___x_261_);
return v___x_262_;
}
case 5:
{
uint8_t v_gen_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_gen_263_ = lean_ctor_get_uint8(v_t_252_, 0);
v___x_264_ = lean_box(v_gen_263_);
v___x_265_ = lean_apply_1(v_k_253_, v___x_264_);
return v___x_265_;
}
case 8:
{
uint8_t v_gen_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_gen_266_ = lean_ctor_get_uint8(v_t_252_, 0);
v___x_267_ = lean_box(v_gen_266_);
v___x_268_ = lean_apply_1(v_k_253_, v___x_267_);
return v___x_268_;
}
default: 
{
return v_k_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg___boxed(lean_object* v_t_269_, lean_object* v_k_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_269_, v_k_270_);
lean_dec(v_t_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim(lean_object* v_motive_272_, lean_object* v_ctorIdx_273_, lean_object* v_t_274_, lean_object* v_h_275_, lean_object* v_k_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_274_, v_k_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___boxed(lean_object* v_motive_278_, lean_object* v_ctorIdx_279_, lean_object* v_t_280_, lean_object* v_h_281_, lean_object* v_k_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim(v_motive_278_, v_ctorIdx_279_, v_t_280_, v_h_281_, v_k_282_);
lean_dec(v_t_280_);
lean_dec(v_ctorIdx_279_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg(lean_object* v_t_284_, lean_object* v_eqLhs_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_284_, v_eqLhs_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg___boxed(lean_object* v_t_287_, lean_object* v_eqLhs_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg(v_t_287_, v_eqLhs_288_);
lean_dec(v_t_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim(lean_object* v_motive_290_, lean_object* v_t_291_, lean_object* v_h_292_, lean_object* v_eqLhs_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_291_, v_eqLhs_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___boxed(lean_object* v_motive_295_, lean_object* v_t_296_, lean_object* v_h_297_, lean_object* v_eqLhs_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim(v_motive_295_, v_t_296_, v_h_297_, v_eqLhs_298_);
lean_dec(v_t_296_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg(lean_object* v_t_300_, lean_object* v_eqRhs_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_300_, v_eqRhs_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg___boxed(lean_object* v_t_303_, lean_object* v_eqRhs_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg(v_t_303_, v_eqRhs_304_);
lean_dec(v_t_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim(lean_object* v_motive_306_, lean_object* v_t_307_, lean_object* v_h_308_, lean_object* v_eqRhs_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_307_, v_eqRhs_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___boxed(lean_object* v_motive_311_, lean_object* v_t_312_, lean_object* v_h_313_, lean_object* v_eqRhs_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim(v_motive_311_, v_t_312_, v_h_313_, v_eqRhs_314_);
lean_dec(v_t_312_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg(lean_object* v_t_316_, lean_object* v_eqBoth_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_316_, v_eqBoth_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg___boxed(lean_object* v_t_319_, lean_object* v_eqBoth_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg(v_t_319_, v_eqBoth_320_);
lean_dec(v_t_319_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim(lean_object* v_motive_322_, lean_object* v_t_323_, lean_object* v_h_324_, lean_object* v_eqBoth_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_323_, v_eqBoth_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___boxed(lean_object* v_motive_327_, lean_object* v_t_328_, lean_object* v_h_329_, lean_object* v_eqBoth_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim(v_motive_327_, v_t_328_, v_h_329_, v_eqBoth_330_);
lean_dec(v_t_328_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg(lean_object* v_t_332_, lean_object* v_eqBwd_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_332_, v_eqBwd_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg___boxed(lean_object* v_t_335_, lean_object* v_eqBwd_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg(v_t_335_, v_eqBwd_336_);
lean_dec(v_t_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim(lean_object* v_motive_338_, lean_object* v_t_339_, lean_object* v_h_340_, lean_object* v_eqBwd_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_339_, v_eqBwd_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___boxed(lean_object* v_motive_343_, lean_object* v_t_344_, lean_object* v_h_345_, lean_object* v_eqBwd_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim(v_motive_343_, v_t_344_, v_h_345_, v_eqBwd_346_);
lean_dec(v_t_344_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg(lean_object* v_t_348_, lean_object* v_fwd_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_348_, v_fwd_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg___boxed(lean_object* v_t_351_, lean_object* v_fwd_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg(v_t_351_, v_fwd_352_);
lean_dec(v_t_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim(lean_object* v_motive_354_, lean_object* v_t_355_, lean_object* v_h_356_, lean_object* v_fwd_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_355_, v_fwd_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___boxed(lean_object* v_motive_359_, lean_object* v_t_360_, lean_object* v_h_361_, lean_object* v_fwd_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim(v_motive_359_, v_t_360_, v_h_361_, v_fwd_362_);
lean_dec(v_t_360_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg(lean_object* v_t_364_, lean_object* v_bwd_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_364_, v_bwd_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg___boxed(lean_object* v_t_367_, lean_object* v_bwd_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg(v_t_367_, v_bwd_368_);
lean_dec(v_t_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim(lean_object* v_motive_370_, lean_object* v_t_371_, lean_object* v_h_372_, lean_object* v_bwd_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_371_, v_bwd_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___boxed(lean_object* v_motive_375_, lean_object* v_t_376_, lean_object* v_h_377_, lean_object* v_bwd_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim(v_motive_375_, v_t_376_, v_h_377_, v_bwd_378_);
lean_dec(v_t_376_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg(lean_object* v_t_380_, lean_object* v_leftRight_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_380_, v_leftRight_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg___boxed(lean_object* v_t_383_, lean_object* v_leftRight_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg(v_t_383_, v_leftRight_384_);
lean_dec(v_t_383_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim(lean_object* v_motive_386_, lean_object* v_t_387_, lean_object* v_h_388_, lean_object* v_leftRight_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_387_, v_leftRight_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___boxed(lean_object* v_motive_391_, lean_object* v_t_392_, lean_object* v_h_393_, lean_object* v_leftRight_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim(v_motive_391_, v_t_392_, v_h_393_, v_leftRight_394_);
lean_dec(v_t_392_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg(lean_object* v_t_396_, lean_object* v_rightLeft_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_396_, v_rightLeft_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg___boxed(lean_object* v_t_399_, lean_object* v_rightLeft_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg(v_t_399_, v_rightLeft_400_);
lean_dec(v_t_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim(lean_object* v_motive_402_, lean_object* v_t_403_, lean_object* v_h_404_, lean_object* v_rightLeft_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_403_, v_rightLeft_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___boxed(lean_object* v_motive_407_, lean_object* v_t_408_, lean_object* v_h_409_, lean_object* v_rightLeft_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim(v_motive_407_, v_t_408_, v_h_409_, v_rightLeft_410_);
lean_dec(v_t_408_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg(lean_object* v_t_412_, lean_object* v_default_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_412_, v_default_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg___boxed(lean_object* v_t_415_, lean_object* v_default_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg(v_t_415_, v_default_416_);
lean_dec(v_t_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim(lean_object* v_motive_418_, lean_object* v_t_419_, lean_object* v_h_420_, lean_object* v_default_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_419_, v_default_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___boxed(lean_object* v_motive_423_, lean_object* v_t_424_, lean_object* v_h_425_, lean_object* v_default_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Meta_Grind_EMatchTheoremKind_default_elim(v_motive_423_, v_t_424_, v_h_425_, v_default_426_);
lean_dec(v_t_424_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg(lean_object* v_t_428_, lean_object* v_user_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_428_, v_user_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg___boxed(lean_object* v_t_431_, lean_object* v_user_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg(v_t_431_, v_user_432_);
lean_dec(v_t_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim(lean_object* v_motive_434_, lean_object* v_t_435_, lean_object* v_h_436_, lean_object* v_user_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_435_, v_user_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___boxed(lean_object* v_motive_439_, lean_object* v_t_440_, lean_object* v_h_441_, lean_object* v_user_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Meta_Grind_EMatchTheoremKind_user_elim(v_motive_439_, v_t_440_, v_h_441_, v_user_442_);
lean_dec(v_t_440_);
return v_res_443_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; uint8_t v_gen_454_; uint8_t v_gen_x27_455_; 
v___x_450_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(v_x_448_);
v___x_451_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(v_x_449_);
v___x_452_ = lean_nat_dec_eq(v___x_450_, v___x_451_);
lean_dec(v___x_451_);
lean_dec(v___x_450_);
if (v___x_452_ == 0)
{
return v___x_452_;
}
else
{
switch(lean_obj_tag(v_x_448_))
{
case 0:
{
uint8_t v_gen_456_; uint8_t v_gen_457_; 
v_gen_456_ = lean_ctor_get_uint8(v_x_448_, 0);
v_gen_457_ = lean_ctor_get_uint8(v_x_449_, 0);
v_gen_454_ = v_gen_456_;
v_gen_x27_455_ = v_gen_457_;
goto v___jp_453_;
}
case 1:
{
uint8_t v_gen_458_; uint8_t v_gen_459_; 
v_gen_458_ = lean_ctor_get_uint8(v_x_448_, 0);
v_gen_459_ = lean_ctor_get_uint8(v_x_449_, 0);
v_gen_454_ = v_gen_458_;
v_gen_x27_455_ = v_gen_459_;
goto v___jp_453_;
}
case 2:
{
uint8_t v_gen_460_; uint8_t v_gen_461_; 
v_gen_460_ = lean_ctor_get_uint8(v_x_448_, 0);
v_gen_461_ = lean_ctor_get_uint8(v_x_449_, 0);
v_gen_454_ = v_gen_460_;
v_gen_x27_455_ = v_gen_461_;
goto v___jp_453_;
}
case 5:
{
uint8_t v_gen_462_; uint8_t v_gen_463_; 
v_gen_462_ = lean_ctor_get_uint8(v_x_448_, 0);
v_gen_463_ = lean_ctor_get_uint8(v_x_449_, 0);
v_gen_454_ = v_gen_462_;
v_gen_x27_455_ = v_gen_463_;
goto v___jp_453_;
}
case 8:
{
uint8_t v_gen_464_; uint8_t v_gen_465_; 
v_gen_464_ = lean_ctor_get_uint8(v_x_448_, 0);
v_gen_465_ = lean_ctor_get_uint8(v_x_449_, 0);
v_gen_454_ = v_gen_464_;
v_gen_x27_455_ = v_gen_465_;
goto v___jp_453_;
}
default: 
{
return v___x_452_;
}
}
}
v___jp_453_:
{
if (v_gen_454_ == 0)
{
if (v_gen_x27_455_ == 0)
{
return v___x_452_;
}
else
{
return v_gen_454_;
}
}
else
{
return v_gen_x27_455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq___boxed(lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
uint8_t v_res_468_; lean_object* v_r_469_; 
v_res_468_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_x_466_, v_x_467_);
lean_dec(v_x_467_);
lean_dec(v_x_466_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_unsigned_to_nat(2u);
v___x_494_ = lean_nat_to_int(v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = lean_nat_to_int(v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr(lean_object* v_x_521_, lean_object* v_prec_522_){
_start:
{
lean_object* v___y_524_; lean_object* v___y_531_; lean_object* v___y_538_; lean_object* v___y_545_; lean_object* v___y_552_; 
switch(lean_obj_tag(v_x_521_))
{
case 0:
{
uint8_t v_gen_558_; lean_object* v___y_560_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_gen_558_ = lean_ctor_get_uint8(v_x_521_, 0);
v___x_568_ = lean_unsigned_to_nat(1024u);
v___x_569_ = lean_nat_dec_le(v___x_568_, v_prec_522_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; 
v___x_570_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_560_ = v___x_570_;
goto v___jp_559_;
}
else
{
lean_object* v___x_571_; 
v___x_571_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_560_ = v___x_571_;
goto v___jp_559_;
}
v___jp_559_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_561_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__12));
v___x_562_ = l_Bool_repr___redArg(v_gen_558_);
v___x_563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
lean_inc(v___y_560_);
v___x_564_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_564_, 0, v___y_560_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = 0;
v___x_566_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set_uint8(v___x_566_, sizeof(void*)*1, v___x_565_);
v___x_567_ = l_Repr_addAppParen(v___x_566_, v_prec_522_);
return v___x_567_;
}
}
case 1:
{
uint8_t v_gen_572_; lean_object* v___y_574_; lean_object* v___x_582_; uint8_t v___x_583_; 
v_gen_572_ = lean_ctor_get_uint8(v_x_521_, 0);
v___x_582_ = lean_unsigned_to_nat(1024u);
v___x_583_ = lean_nat_dec_le(v___x_582_, v_prec_522_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_574_ = v___x_584_;
goto v___jp_573_;
}
else
{
lean_object* v___x_585_; 
v___x_585_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_574_ = v___x_585_;
goto v___jp_573_;
}
v___jp_573_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_575_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__17));
v___x_576_ = l_Bool_repr___redArg(v_gen_572_);
v___x_577_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
lean_inc(v___y_574_);
v___x_578_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_578_, 0, v___y_574_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = 0;
v___x_580_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_580_, 0, v___x_578_);
lean_ctor_set_uint8(v___x_580_, sizeof(void*)*1, v___x_579_);
v___x_581_ = l_Repr_addAppParen(v___x_580_, v_prec_522_);
return v___x_581_;
}
}
case 2:
{
uint8_t v_gen_586_; lean_object* v___y_588_; lean_object* v___x_596_; uint8_t v___x_597_; 
v_gen_586_ = lean_ctor_get_uint8(v_x_521_, 0);
v___x_596_ = lean_unsigned_to_nat(1024u);
v___x_597_ = lean_nat_dec_le(v___x_596_, v_prec_522_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
v___x_598_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_588_ = v___x_598_;
goto v___jp_587_;
}
else
{
lean_object* v___x_599_; 
v___x_599_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_588_ = v___x_599_;
goto v___jp_587_;
}
v___jp_587_:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_589_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__20));
v___x_590_ = l_Bool_repr___redArg(v_gen_586_);
v___x_591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
lean_inc(v___y_588_);
v___x_592_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_592_, 0, v___y_588_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = 0;
v___x_594_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_594_, 0, v___x_592_);
lean_ctor_set_uint8(v___x_594_, sizeof(void*)*1, v___x_593_);
v___x_595_ = l_Repr_addAppParen(v___x_594_, v_prec_522_);
return v___x_595_;
}
}
case 3:
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(1024u);
v___x_601_ = lean_nat_dec_le(v___x_600_, v_prec_522_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
v___x_602_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_538_ = v___x_602_;
goto v___jp_537_;
}
else
{
lean_object* v___x_603_; 
v___x_603_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_538_ = v___x_603_;
goto v___jp_537_;
}
}
case 4:
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_unsigned_to_nat(1024u);
v___x_605_ = lean_nat_dec_le(v___x_604_, v_prec_522_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; 
v___x_606_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_545_ = v___x_606_;
goto v___jp_544_;
}
else
{
lean_object* v___x_607_; 
v___x_607_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_545_ = v___x_607_;
goto v___jp_544_;
}
}
case 5:
{
uint8_t v_gen_608_; lean_object* v___y_610_; lean_object* v___x_618_; uint8_t v___x_619_; 
v_gen_608_ = lean_ctor_get_uint8(v_x_521_, 0);
v___x_618_ = lean_unsigned_to_nat(1024u);
v___x_619_ = lean_nat_dec_le(v___x_618_, v_prec_522_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
v___x_620_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_610_ = v___x_620_;
goto v___jp_609_;
}
else
{
lean_object* v___x_621_; 
v___x_621_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_610_ = v___x_621_;
goto v___jp_609_;
}
v___jp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_611_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__23));
v___x_612_ = l_Bool_repr___redArg(v_gen_608_);
v___x_613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
lean_inc(v___y_610_);
v___x_614_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_614_, 0, v___y_610_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = 0;
v___x_616_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set_uint8(v___x_616_, sizeof(void*)*1, v___x_615_);
v___x_617_ = l_Repr_addAppParen(v___x_616_, v_prec_522_);
return v___x_617_;
}
}
case 6:
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_unsigned_to_nat(1024u);
v___x_623_ = lean_nat_dec_le(v___x_622_, v_prec_522_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; 
v___x_624_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_531_ = v___x_624_;
goto v___jp_530_;
}
else
{
lean_object* v___x_625_; 
v___x_625_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_531_ = v___x_625_;
goto v___jp_530_;
}
}
case 7:
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(1024u);
v___x_627_ = lean_nat_dec_le(v___x_626_, v_prec_522_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
v___x_628_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_524_ = v___x_628_;
goto v___jp_523_;
}
else
{
lean_object* v___x_629_; 
v___x_629_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_524_ = v___x_629_;
goto v___jp_523_;
}
}
case 8:
{
uint8_t v_gen_630_; lean_object* v___y_632_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_gen_630_ = lean_ctor_get_uint8(v_x_521_, 0);
v___x_640_ = lean_unsigned_to_nat(1024u);
v___x_641_ = lean_nat_dec_le(v___x_640_, v_prec_522_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
v___x_642_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_632_ = v___x_642_;
goto v___jp_631_;
}
else
{
lean_object* v___x_643_; 
v___x_643_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_632_ = v___x_643_;
goto v___jp_631_;
}
v___jp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_633_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__26));
v___x_634_ = l_Bool_repr___redArg(v_gen_630_);
v___x_635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
lean_inc(v___y_632_);
v___x_636_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_636_, 0, v___y_632_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = 0;
v___x_638_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set_uint8(v___x_638_, sizeof(void*)*1, v___x_637_);
v___x_639_ = l_Repr_addAppParen(v___x_638_, v_prec_522_);
return v___x_639_;
}
}
default: 
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = lean_unsigned_to_nat(1024u);
v___x_645_ = lean_nat_dec_le(v___x_644_, v_prec_522_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
v___x_646_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_552_ = v___x_646_;
goto v___jp_551_;
}
else
{
lean_object* v___x_647_; 
v___x_647_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_552_ = v___x_647_;
goto v___jp_551_;
}
}
}
v___jp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_525_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__1));
lean_inc(v___y_524_);
v___x_526_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_526_, 0, v___y_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = 0;
v___x_528_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*1, v___x_527_);
v___x_529_ = l_Repr_addAppParen(v___x_528_, v_prec_522_);
return v___x_529_;
}
v___jp_530_:
{
lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_532_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__3));
lean_inc(v___y_531_);
v___x_533_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_533_, 0, v___y_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = 0;
v___x_535_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*1, v___x_534_);
v___x_536_ = l_Repr_addAppParen(v___x_535_, v_prec_522_);
return v___x_536_;
}
v___jp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_539_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__5));
lean_inc(v___y_538_);
v___x_540_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_540_, 0, v___y_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = 0;
v___x_542_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*1, v___x_541_);
v___x_543_ = l_Repr_addAppParen(v___x_542_, v_prec_522_);
return v___x_543_;
}
v___jp_544_:
{
lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_546_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__7));
lean_inc(v___y_545_);
v___x_547_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_547_, 0, v___y_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = 0;
v___x_549_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*1, v___x_548_);
v___x_550_ = l_Repr_addAppParen(v___x_549_, v_prec_522_);
return v___x_550_;
}
v___jp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_553_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__9));
lean_inc(v___y_552_);
v___x_554_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_554_, 0, v___y_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = 0;
v___x_556_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set_uint8(v___x_556_, sizeof(void*)*1, v___x_555_);
v___x_557_ = l_Repr_addAppParen(v___x_556_, v_prec_522_);
return v___x_557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___boxed(lean_object* v_x_648_, lean_object* v_prec_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr(v_x_648_, v_prec_649_);
lean_dec(v_prec_649_);
lean_dec(v_x_648_);
return v_res_650_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0(void){
_start:
{
uint64_t v___x_653_; uint64_t v___x_654_; uint64_t v___x_655_; 
v___x_653_ = 13ULL;
v___x_654_ = 0ULL;
v___x_655_ = lean_uint64_mix_hash(v___x_654_, v___x_653_);
return v___x_655_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1(void){
_start:
{
uint64_t v___x_656_; uint64_t v___x_657_; uint64_t v___x_658_; 
v___x_656_ = 11ULL;
v___x_657_ = 0ULL;
v___x_658_ = lean_uint64_mix_hash(v___x_657_, v___x_656_);
return v___x_658_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2(void){
_start:
{
uint64_t v___x_659_; uint64_t v___x_660_; uint64_t v___x_661_; 
v___x_659_ = 13ULL;
v___x_660_ = 1ULL;
v___x_661_ = lean_uint64_mix_hash(v___x_660_, v___x_659_);
return v___x_661_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3(void){
_start:
{
uint64_t v___x_662_; uint64_t v___x_663_; uint64_t v___x_664_; 
v___x_662_ = 11ULL;
v___x_663_ = 1ULL;
v___x_664_ = lean_uint64_mix_hash(v___x_663_, v___x_662_);
return v___x_664_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4(void){
_start:
{
uint64_t v___x_665_; uint64_t v___x_666_; uint64_t v___x_667_; 
v___x_665_ = 13ULL;
v___x_666_ = 2ULL;
v___x_667_ = lean_uint64_mix_hash(v___x_666_, v___x_665_);
return v___x_667_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5(void){
_start:
{
uint64_t v___x_668_; uint64_t v___x_669_; uint64_t v___x_670_; 
v___x_668_ = 11ULL;
v___x_669_ = 2ULL;
v___x_670_ = lean_uint64_mix_hash(v___x_669_, v___x_668_);
return v___x_670_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6(void){
_start:
{
uint64_t v___x_671_; uint64_t v___x_672_; uint64_t v___x_673_; 
v___x_671_ = 13ULL;
v___x_672_ = 5ULL;
v___x_673_ = lean_uint64_mix_hash(v___x_672_, v___x_671_);
return v___x_673_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7(void){
_start:
{
uint64_t v___x_674_; uint64_t v___x_675_; uint64_t v___x_676_; 
v___x_674_ = 11ULL;
v___x_675_ = 5ULL;
v___x_676_ = lean_uint64_mix_hash(v___x_675_, v___x_674_);
return v___x_676_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8(void){
_start:
{
uint64_t v___x_677_; uint64_t v___x_678_; uint64_t v___x_679_; 
v___x_677_ = 13ULL;
v___x_678_ = 8ULL;
v___x_679_ = lean_uint64_mix_hash(v___x_678_, v___x_677_);
return v___x_679_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9(void){
_start:
{
uint64_t v___x_680_; uint64_t v___x_681_; uint64_t v___x_682_; 
v___x_680_ = 11ULL;
v___x_681_ = 8ULL;
v___x_682_ = lean_uint64_mix_hash(v___x_681_, v___x_680_);
return v___x_682_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(lean_object* v_x_683_){
_start:
{
switch(lean_obj_tag(v_x_683_))
{
case 0:
{
uint8_t v_gen_684_; 
v_gen_684_ = lean_ctor_get_uint8(v_x_683_, 0);
if (v_gen_684_ == 0)
{
uint64_t v___x_685_; 
v___x_685_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0);
return v___x_685_;
}
else
{
uint64_t v___x_686_; 
v___x_686_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1);
return v___x_686_;
}
}
case 1:
{
uint8_t v_gen_687_; 
v_gen_687_ = lean_ctor_get_uint8(v_x_683_, 0);
if (v_gen_687_ == 0)
{
uint64_t v___x_688_; 
v___x_688_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2);
return v___x_688_;
}
else
{
uint64_t v___x_689_; 
v___x_689_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3);
return v___x_689_;
}
}
case 2:
{
uint8_t v_gen_690_; 
v_gen_690_ = lean_ctor_get_uint8(v_x_683_, 0);
if (v_gen_690_ == 0)
{
uint64_t v___x_691_; 
v___x_691_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4);
return v___x_691_;
}
else
{
uint64_t v___x_692_; 
v___x_692_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5);
return v___x_692_;
}
}
case 3:
{
uint64_t v___x_693_; 
v___x_693_ = 3ULL;
return v___x_693_;
}
case 4:
{
uint64_t v___x_694_; 
v___x_694_ = 4ULL;
return v___x_694_;
}
case 5:
{
uint8_t v_gen_695_; 
v_gen_695_ = lean_ctor_get_uint8(v_x_683_, 0);
if (v_gen_695_ == 0)
{
uint64_t v___x_696_; 
v___x_696_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6);
return v___x_696_;
}
else
{
uint64_t v___x_697_; 
v___x_697_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7);
return v___x_697_;
}
}
case 6:
{
uint64_t v___x_698_; 
v___x_698_ = 6ULL;
return v___x_698_;
}
case 7:
{
uint64_t v___x_699_; 
v___x_699_ = 7ULL;
return v___x_699_;
}
case 8:
{
uint8_t v_gen_700_; 
v_gen_700_ = lean_ctor_get_uint8(v_x_683_, 0);
if (v_gen_700_ == 0)
{
uint64_t v___x_701_; 
v___x_701_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8);
return v___x_701_;
}
else
{
uint64_t v___x_702_; 
v___x_702_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9);
return v___x_702_;
}
}
default: 
{
uint64_t v___x_703_; 
v___x_703_ = 9ULL;
return v___x_703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___boxed(lean_object* v_x_704_){
_start:
{
uint64_t v_res_705_; lean_object* v_r_706_; 
v_res_705_ = l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(v_x_704_);
lean_dec(v_x_704_);
v_r_706_ = lean_box_uint64(v_res_705_);
return v_r_706_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = lean_box(0);
v___x_715_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__2));
v___x_716_ = l_Lean_Expr_const___override(v___x_715_, v___x_714_);
return v___x_716_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_717_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___x_718_);
lean_ctor_set(v___x_720_, 2, v___x_717_);
return v___x_720_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default(void){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4);
return v___x_721_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS(void){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default;
return v___x_722_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(lean_object* v_xs_723_, lean_object* v_ys_724_, lean_object* v_x_725_){
_start:
{
lean_object* v_zero_726_; uint8_t v_isZero_727_; 
v_zero_726_ = lean_unsigned_to_nat(0u);
v_isZero_727_ = lean_nat_dec_eq(v_x_725_, v_zero_726_);
if (v_isZero_727_ == 1)
{
lean_dec(v_x_725_);
return v_isZero_727_;
}
else
{
lean_object* v_one_728_; lean_object* v_n_729_; lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v_one_728_ = lean_unsigned_to_nat(1u);
v_n_729_ = lean_nat_sub(v_x_725_, v_one_728_);
lean_dec(v_x_725_);
v___x_730_ = lean_array_fget_borrowed(v_xs_723_, v_n_729_);
v___x_731_ = lean_array_fget_borrowed(v_ys_724_, v_n_729_);
v___x_732_ = lean_name_eq(v___x_730_, v___x_731_);
if (v___x_732_ == 0)
{
lean_dec(v_n_729_);
return v___x_732_;
}
else
{
v_x_725_ = v_n_729_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg___boxed(lean_object* v_xs_734_, lean_object* v_ys_735_, lean_object* v_x_736_){
_start:
{
uint8_t v_res_737_; lean_object* v_r_738_; 
v_res_737_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_xs_734_, v_ys_735_, v_x_736_);
lean_dec_ref(v_ys_735_);
lean_dec_ref(v_xs_734_);
v_r_738_ = lean_box(v_res_737_);
return v_r_738_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqCnstrRHS_beq(lean_object* v_x_739_, lean_object* v_x_740_){
_start:
{
lean_object* v_levelNames_741_; lean_object* v_numMVars_742_; lean_object* v_expr_743_; lean_object* v_levelNames_744_; lean_object* v_numMVars_745_; lean_object* v_expr_746_; lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v_levelNames_741_ = lean_ctor_get(v_x_739_, 0);
v_numMVars_742_ = lean_ctor_get(v_x_739_, 1);
v_expr_743_ = lean_ctor_get(v_x_739_, 2);
v_levelNames_744_ = lean_ctor_get(v_x_740_, 0);
v_numMVars_745_ = lean_ctor_get(v_x_740_, 1);
v_expr_746_ = lean_ctor_get(v_x_740_, 2);
v___x_747_ = lean_array_get_size(v_levelNames_741_);
v___x_748_ = lean_array_get_size(v_levelNames_744_);
v___x_749_ = lean_nat_dec_eq(v___x_747_, v___x_748_);
if (v___x_749_ == 0)
{
return v___x_749_;
}
else
{
uint8_t v___x_750_; 
v___x_750_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_levelNames_741_, v_levelNames_744_, v___x_747_);
if (v___x_750_ == 0)
{
return v___x_750_;
}
else
{
uint8_t v___x_751_; 
v___x_751_ = lean_nat_dec_eq(v_numMVars_742_, v_numMVars_745_);
if (v___x_751_ == 0)
{
return v___x_751_;
}
else
{
uint8_t v___x_752_; 
v___x_752_ = lean_expr_eqv(v_expr_743_, v_expr_746_);
return v___x_752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqCnstrRHS_beq___boxed(lean_object* v_x_753_, lean_object* v_x_754_){
_start:
{
uint8_t v_res_755_; lean_object* v_r_756_; 
v_res_755_ = l_Lean_Meta_Grind_instBEqCnstrRHS_beq(v_x_753_, v_x_754_);
lean_dec_ref(v_x_754_);
lean_dec_ref(v_x_753_);
v_r_756_ = lean_box(v_res_755_);
return v_r_756_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(lean_object* v_xs_757_, lean_object* v_ys_758_, lean_object* v_hsz_759_, lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
uint8_t v___x_762_; 
v___x_762_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_xs_757_, v_ys_758_, v_x_760_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___boxed(lean_object* v_xs_763_, lean_object* v_ys_764_, lean_object* v_hsz_765_, lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
uint8_t v_res_768_; lean_object* v_r_769_; 
v_res_768_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(v_xs_763_, v_ys_764_, v_hsz_765_, v_x_766_, v_x_767_);
lean_dec_ref(v_ys_764_);
lean_dec_ref(v_xs_763_);
v_r_769_ = lean_box(v_res_768_);
return v_r_769_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__1(lean_object* v_a_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = lean_nat_to_int(v_a_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
if (lean_obj_tag(v_x_776_) == 0)
{
lean_dec(v_x_774_);
return v_x_775_;
}
else
{
lean_object* v_head_777_; lean_object* v_tail_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_789_; 
v_head_777_ = lean_ctor_get(v_x_776_, 0);
v_tail_778_ = lean_ctor_get(v_x_776_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_x_776_);
if (v_isSharedCheck_789_ == 0)
{
v___x_780_ = v_x_776_;
v_isShared_781_ = v_isSharedCheck_789_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_tail_778_);
lean_inc(v_head_777_);
lean_dec(v_x_776_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_789_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
lean_inc(v_x_774_);
if (v_isShared_781_ == 0)
{
lean_ctor_set_tag(v___x_780_, 5);
lean_ctor_set(v___x_780_, 1, v_x_774_);
lean_ctor_set(v___x_780_, 0, v_x_775_);
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_x_775_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_x_774_);
v___x_783_ = v_reuseFailAlloc_788_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_784_ = lean_unsigned_to_nat(0u);
v___x_785_ = l_Lean_Name_reprPrec(v_head_777_, v___x_784_);
v___x_786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_783_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v_x_775_ = v___x_786_;
v_x_776_ = v_tail_778_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2(lean_object* v_x_790_, lean_object* v_x_791_, lean_object* v_x_792_){
_start:
{
if (lean_obj_tag(v_x_792_) == 0)
{
lean_dec(v_x_790_);
return v_x_791_;
}
else
{
lean_object* v_head_793_; lean_object* v_tail_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_805_; 
v_head_793_ = lean_ctor_get(v_x_792_, 0);
v_tail_794_ = lean_ctor_get(v_x_792_, 1);
v_isSharedCheck_805_ = !lean_is_exclusive(v_x_792_);
if (v_isSharedCheck_805_ == 0)
{
v___x_796_ = v_x_792_;
v_isShared_797_ = v_isSharedCheck_805_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_tail_794_);
lean_inc(v_head_793_);
lean_dec(v_x_792_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_805_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
lean_inc(v_x_790_);
if (v_isShared_797_ == 0)
{
lean_ctor_set_tag(v___x_796_, 5);
lean_ctor_set(v___x_796_, 1, v_x_790_);
lean_ctor_set(v___x_796_, 0, v_x_791_);
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_x_791_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_x_790_);
v___x_799_ = v_reuseFailAlloc_804_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = l_Lean_Name_reprPrec(v_head_793_, v___x_800_);
v___x_802_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_799_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2_spec__3(v_x_790_, v___x_802_, v_tail_794_);
return v___x_803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(lean_object* v___y_806_){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = l_Lean_Name_reprPrec(v___y_806_, v___x_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0(lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
if (lean_obj_tag(v_x_809_) == 0)
{
lean_object* v___x_811_; 
lean_dec(v_x_810_);
v___x_811_ = lean_box(0);
return v___x_811_;
}
else
{
lean_object* v_tail_812_; 
v_tail_812_ = lean_ctor_get(v_x_809_, 1);
if (lean_obj_tag(v_tail_812_) == 0)
{
lean_object* v_head_813_; lean_object* v___x_814_; 
lean_dec(v_x_810_);
v_head_813_ = lean_ctor_get(v_x_809_, 0);
lean_inc(v_head_813_);
lean_dec_ref(v_x_809_);
v___x_814_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(v_head_813_);
return v___x_814_;
}
else
{
lean_object* v_head_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_inc(v_tail_812_);
v_head_815_ = lean_ctor_get(v_x_809_, 0);
lean_inc(v_head_815_);
lean_dec_ref(v_x_809_);
v___x_816_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(v_head_815_);
v___x_817_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2(v_x_810_, v___x_816_, v_tail_812_);
return v___x_817_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0));
v___x_827_ = lean_string_length(v___x_826_);
return v___x_827_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5);
v___x_829_ = lean_nat_to_int(v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0(lean_object* v_xs_837_){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_838_ = lean_array_get_size(v_xs_837_);
v___x_839_ = lean_unsigned_to_nat(0u);
v___x_840_ = lean_nat_dec_eq(v___x_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_841_ = lean_array_to_list(v_xs_837_);
v___x_842_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__3));
v___x_843_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0(v___x_841_, v___x_842_);
v___x_844_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6);
v___x_845_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__7));
v___x_846_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v___x_843_);
v___x_847_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__8));
v___x_848_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_844_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = l_Std_Format_fill(v___x_849_);
return v___x_850_;
}
else
{
lean_object* v___x_851_; 
lean_dec_ref(v_xs_837_);
v___x_851_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__10));
return v___x_851_;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_unsigned_to_nat(14u);
v___x_866_ = lean_nat_to_int(v___x_865_);
return v___x_866_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_unsigned_to_nat(12u);
v___x_871_ = lean_nat_to_int(v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_unsigned_to_nat(8u);
v___x_876_ = lean_nat_to_int(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0));
v___x_879_ = lean_string_length(v___x_878_);
return v___x_879_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15);
v___x_881_ = lean_nat_to_int(v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(lean_object* v_x_886_){
_start:
{
lean_object* v_levelNames_887_; lean_object* v_numMVars_888_; lean_object* v_expr_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_levelNames_887_ = lean_ctor_get(v_x_886_, 0);
lean_inc_ref(v_levelNames_887_);
v_numMVars_888_ = lean_ctor_get(v_x_886_, 1);
lean_inc(v_numMVars_888_);
v_expr_889_ = lean_ctor_get(v_x_886_, 2);
lean_inc_ref(v_expr_889_);
lean_dec_ref(v_x_886_);
v___x_890_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5));
v___x_891_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__6));
v___x_892_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7);
v___x_893_ = l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0(v_levelNames_887_);
v___x_894_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = 0;
v___x_896_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set_uint8(v___x_896_, sizeof(void*)*1, v___x_895_);
v___x_897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_891_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2));
v___x_899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = lean_box(1);
v___x_901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__9));
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_890_);
v___x_905_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10);
v___x_906_ = l_Nat_reprFast(v_numMVars_888_);
v___x_907_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
v___x_908_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_905_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set_uint8(v___x_909_, sizeof(void*)*1, v___x_895_);
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_904_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v___x_898_);
v___x_912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v___x_900_);
v___x_913_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__12));
v___x_914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_912_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v___x_890_);
v___x_916_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13);
v___x_917_ = lean_unsigned_to_nat(0u);
v___x_918_ = l_Lean_instReprExpr_repr(v_expr_889_, v___x_917_);
v___x_919_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_916_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set_uint8(v___x_920_, sizeof(void*)*1, v___x_895_);
v___x_921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_915_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16);
v___x_923_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__17));
v___x_924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v___x_921_);
v___x_925_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__18));
v___x_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_922_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*1, v___x_895_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr(lean_object* v_x_929_, lean_object* v_prec_930_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_x_929_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___boxed(lean_object* v_x_932_, lean_object* v_prec_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr(v_x_932_, v_prec_933_);
lean_dec(v_prec_933_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(lean_object* v_x_937_){
_start:
{
switch(lean_obj_tag(v_x_937_))
{
case 0:
{
lean_object* v___x_938_; 
v___x_938_ = lean_unsigned_to_nat(0u);
return v___x_938_;
}
case 1:
{
lean_object* v___x_939_; 
v___x_939_ = lean_unsigned_to_nat(1u);
return v___x_939_;
}
case 2:
{
lean_object* v___x_940_; 
v___x_940_ = lean_unsigned_to_nat(2u);
return v___x_940_;
}
case 3:
{
lean_object* v___x_941_; 
v___x_941_ = lean_unsigned_to_nat(3u);
return v___x_941_;
}
case 4:
{
lean_object* v___x_942_; 
v___x_942_ = lean_unsigned_to_nat(4u);
return v___x_942_;
}
case 5:
{
lean_object* v___x_943_; 
v___x_943_ = lean_unsigned_to_nat(5u);
return v___x_943_;
}
case 6:
{
lean_object* v___x_944_; 
v___x_944_ = lean_unsigned_to_nat(6u);
return v___x_944_;
}
case 7:
{
lean_object* v___x_945_; 
v___x_945_ = lean_unsigned_to_nat(7u);
return v___x_945_;
}
case 8:
{
lean_object* v___x_946_; 
v___x_946_ = lean_unsigned_to_nat(8u);
return v___x_946_;
}
case 9:
{
lean_object* v___x_947_; 
v___x_947_ = lean_unsigned_to_nat(9u);
return v___x_947_;
}
default: 
{
lean_object* v___x_948_; 
v___x_948_ = lean_unsigned_to_nat(10u);
return v___x_948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx___boxed(lean_object* v_x_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_949_);
lean_dec_ref(v_x_949_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(lean_object* v_t_951_, lean_object* v_k_952_){
_start:
{
switch(lean_obj_tag(v_t_951_))
{
case 0:
{
lean_object* v_lhs_953_; lean_object* v_rhs_954_; lean_object* v___x_955_; 
v_lhs_953_ = lean_ctor_get(v_t_951_, 0);
lean_inc(v_lhs_953_);
v_rhs_954_ = lean_ctor_get(v_t_951_, 1);
lean_inc_ref(v_rhs_954_);
lean_dec_ref(v_t_951_);
v___x_955_ = lean_apply_2(v_k_952_, v_lhs_953_, v_rhs_954_);
return v___x_955_;
}
case 1:
{
lean_object* v_lhs_956_; lean_object* v_rhs_957_; lean_object* v___x_958_; 
v_lhs_956_ = lean_ctor_get(v_t_951_, 0);
lean_inc(v_lhs_956_);
v_rhs_957_ = lean_ctor_get(v_t_951_, 1);
lean_inc_ref(v_rhs_957_);
lean_dec_ref(v_t_951_);
v___x_958_ = lean_apply_2(v_k_952_, v_lhs_956_, v_rhs_957_);
return v___x_958_;
}
case 2:
{
lean_object* v_lhs_959_; lean_object* v_n_960_; lean_object* v___x_961_; 
v_lhs_959_ = lean_ctor_get(v_t_951_, 0);
lean_inc(v_lhs_959_);
v_n_960_ = lean_ctor_get(v_t_951_, 1);
lean_inc(v_n_960_);
lean_dec_ref(v_t_951_);
v___x_961_ = lean_apply_2(v_k_952_, v_lhs_959_, v_n_960_);
return v___x_961_;
}
case 3:
{
lean_object* v_lhs_962_; lean_object* v_n_963_; lean_object* v___x_964_; 
v_lhs_962_ = lean_ctor_get(v_t_951_, 0);
lean_inc(v_lhs_962_);
v_n_963_ = lean_ctor_get(v_t_951_, 1);
lean_inc(v_n_963_);
lean_dec_ref(v_t_951_);
v___x_964_ = lean_apply_2(v_k_952_, v_lhs_962_, v_n_963_);
return v___x_964_;
}
case 6:
{
lean_object* v_bvarIdx_965_; uint8_t v_strict_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_bvarIdx_965_ = lean_ctor_get(v_t_951_, 0);
lean_inc(v_bvarIdx_965_);
v_strict_966_ = lean_ctor_get_uint8(v_t_951_, sizeof(void*)*1);
lean_dec_ref(v_t_951_);
v___x_967_ = lean_box(v_strict_966_);
v___x_968_ = lean_apply_2(v_k_952_, v_bvarIdx_965_, v___x_967_);
return v___x_968_;
}
case 8:
{
lean_object* v_e_969_; lean_object* v___x_970_; 
v_e_969_ = lean_ctor_get(v_t_951_, 0);
lean_inc_ref(v_e_969_);
lean_dec_ref(v_t_951_);
v___x_970_ = lean_apply_1(v_k_952_, v_e_969_);
return v___x_970_;
}
case 9:
{
lean_object* v_e_971_; lean_object* v___x_972_; 
v_e_971_ = lean_ctor_get(v_t_951_, 0);
lean_inc_ref(v_e_971_);
lean_dec_ref(v_t_951_);
v___x_972_ = lean_apply_1(v_k_952_, v_e_971_);
return v___x_972_;
}
case 10:
{
lean_object* v_bvarIdx_973_; uint8_t v_strict_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_bvarIdx_973_ = lean_ctor_get(v_t_951_, 0);
lean_inc(v_bvarIdx_973_);
v_strict_974_ = lean_ctor_get_uint8(v_t_951_, sizeof(void*)*1);
lean_dec_ref(v_t_951_);
v___x_975_ = lean_box(v_strict_974_);
v___x_976_ = lean_apply_2(v_k_952_, v_bvarIdx_973_, v___x_975_);
return v___x_976_;
}
default: 
{
lean_object* v_n_977_; lean_object* v___x_978_; 
v_n_977_ = lean_ctor_get(v_t_951_, 0);
lean_inc(v_n_977_);
lean_dec_ref(v_t_951_);
v___x_978_ = lean_apply_1(v_k_952_, v_n_977_);
return v___x_978_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim(lean_object* v_motive_979_, lean_object* v_ctorIdx_980_, lean_object* v_t_981_, lean_object* v_h_982_, lean_object* v_k_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_981_, v_k_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___boxed(lean_object* v_motive_985_, lean_object* v_ctorIdx_986_, lean_object* v_t_987_, lean_object* v_h_988_, lean_object* v_k_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim(v_motive_985_, v_ctorIdx_986_, v_t_987_, v_h_988_, v_k_989_);
lean_dec(v_ctorIdx_986_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim___redArg(lean_object* v_t_991_, lean_object* v_notDefEq_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_991_, v_notDefEq_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim(lean_object* v_motive_994_, lean_object* v_t_995_, lean_object* v_h_996_, lean_object* v_notDefEq_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_995_, v_notDefEq_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim___redArg(lean_object* v_t_999_, lean_object* v_defEq_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_999_, v_defEq_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim(lean_object* v_motive_1002_, lean_object* v_t_1003_, lean_object* v_h_1004_, lean_object* v_defEq_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1003_, v_defEq_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim___redArg(lean_object* v_t_1007_, lean_object* v_sizeLt_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1007_, v_sizeLt_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim(lean_object* v_motive_1010_, lean_object* v_t_1011_, lean_object* v_h_1012_, lean_object* v_sizeLt_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1011_, v_sizeLt_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim___redArg(lean_object* v_t_1015_, lean_object* v_depthLt_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1015_, v_depthLt_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim(lean_object* v_motive_1018_, lean_object* v_t_1019_, lean_object* v_h_1020_, lean_object* v_depthLt_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1019_, v_depthLt_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim___redArg(lean_object* v_t_1023_, lean_object* v_genLt_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1023_, v_genLt_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim(lean_object* v_motive_1026_, lean_object* v_t_1027_, lean_object* v_h_1028_, lean_object* v_genLt_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1027_, v_genLt_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim___redArg(lean_object* v_t_1031_, lean_object* v_isGround_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1031_, v_isGround_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim(lean_object* v_motive_1034_, lean_object* v_t_1035_, lean_object* v_h_1036_, lean_object* v_isGround_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1035_, v_isGround_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim___redArg(lean_object* v_t_1039_, lean_object* v_isValue_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1039_, v_isValue_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim(lean_object* v_motive_1042_, lean_object* v_t_1043_, lean_object* v_h_1044_, lean_object* v_isValue_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1043_, v_isValue_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim___redArg(lean_object* v_t_1047_, lean_object* v_maxInsts_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1047_, v_maxInsts_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim(lean_object* v_motive_1050_, lean_object* v_t_1051_, lean_object* v_h_1052_, lean_object* v_maxInsts_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1051_, v_maxInsts_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim___redArg(lean_object* v_t_1055_, lean_object* v_guard_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1055_, v_guard_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim(lean_object* v_motive_1058_, lean_object* v_t_1059_, lean_object* v_h_1060_, lean_object* v_guard_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1059_, v_guard_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim___redArg(lean_object* v_t_1063_, lean_object* v_check_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1063_, v_check_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim(lean_object* v_motive_1066_, lean_object* v_t_1067_, lean_object* v_h_1068_, lean_object* v_check_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1067_, v_check_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim___redArg(lean_object* v_t_1071_, lean_object* v_notValue_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1071_, v_notValue_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim(lean_object* v_motive_1074_, lean_object* v_t_1075_, lean_object* v_h_1076_, lean_object* v_notValue_1077_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1075_, v_notValue_1077_);
return v___x_1078_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1079_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default;
v___x_1080_ = lean_unsigned_to_nat(0u);
v___x_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v___x_1079_);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default(void){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0, &l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0);
return v___x_1082_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint(void){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default;
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr(lean_object* v_x_1150_, lean_object* v_prec_1151_){
_start:
{
switch(lean_obj_tag(v_x_1150_))
{
case 0:
{
lean_object* v_lhs_1152_; lean_object* v_rhs_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1177_; 
v_lhs_1152_ = lean_ctor_get(v_x_1150_, 0);
v_rhs_1153_ = lean_ctor_get(v_x_1150_, 1);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_x_1150_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1155_ = v_x_1150_;
v_isShared_1156_ = v_isSharedCheck_1177_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_rhs_1153_);
lean_inc(v_lhs_1152_);
lean_dec(v_x_1150_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1177_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___y_1158_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = lean_unsigned_to_nat(1024u);
v___x_1174_ = lean_nat_dec_le(v___x_1173_, v_prec_1151_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1158_ = v___x_1175_;
goto v___jp_1157_;
}
else
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1158_ = v___x_1176_;
goto v___jp_1157_;
}
v___jp_1157_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1159_ = lean_box(1);
v___x_1160_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__2));
v___x_1161_ = l_Nat_reprFast(v_lhs_1152_);
v___x_1162_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set_tag(v___x_1155_, 5);
lean_ctor_set(v___x_1155_, 1, v___x_1162_);
lean_ctor_set(v___x_1155_, 0, v___x_1160_);
v___x_1164_ = v___x_1155_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v___x_1159_);
v___x_1166_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_rhs_1153_);
v___x_1167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
lean_inc(v___y_1158_);
v___x_1168_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___y_1158_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = 0;
v___x_1170_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set_uint8(v___x_1170_, sizeof(void*)*1, v___x_1169_);
v___x_1171_ = l_Repr_addAppParen(v___x_1170_, v_prec_1151_);
return v___x_1171_;
}
}
}
}
case 1:
{
lean_object* v_lhs_1178_; lean_object* v_rhs_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1203_; 
v_lhs_1178_ = lean_ctor_get(v_x_1150_, 0);
v_rhs_1179_ = lean_ctor_get(v_x_1150_, 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_x_1150_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1181_ = v_x_1150_;
v_isShared_1182_ = v_isSharedCheck_1203_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_rhs_1179_);
lean_inc(v_lhs_1178_);
lean_dec(v_x_1150_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1203_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___y_1184_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = lean_unsigned_to_nat(1024u);
v___x_1200_ = lean_nat_dec_le(v___x_1199_, v_prec_1151_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1184_ = v___x_1201_;
goto v___jp_1183_;
}
else
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1184_ = v___x_1202_;
goto v___jp_1183_;
}
v___jp_1183_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1185_ = lean_box(1);
v___x_1186_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__5));
v___x_1187_ = l_Nat_reprFast(v_lhs_1178_);
v___x_1188_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set_tag(v___x_1181_, 5);
lean_ctor_set(v___x_1181_, 1, v___x_1188_);
lean_ctor_set(v___x_1181_, 0, v___x_1186_);
v___x_1190_ = v___x_1181_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
lean_ctor_set(v___x_1191_, 1, v___x_1185_);
v___x_1192_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_rhs_1179_);
v___x_1193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
lean_inc(v___y_1184_);
v___x_1194_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___y_1184_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = 0;
v___x_1196_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1196_, 0, v___x_1194_);
lean_ctor_set_uint8(v___x_1196_, sizeof(void*)*1, v___x_1195_);
v___x_1197_ = l_Repr_addAppParen(v___x_1196_, v_prec_1151_);
return v___x_1197_;
}
}
}
}
case 2:
{
lean_object* v_lhs_1204_; lean_object* v_n_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1230_; 
v_lhs_1204_ = lean_ctor_get(v_x_1150_, 0);
v_n_1205_ = lean_ctor_get(v_x_1150_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_x_1150_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1207_ = v_x_1150_;
v_isShared_1208_ = v_isSharedCheck_1230_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_n_1205_);
lean_inc(v_lhs_1204_);
lean_dec(v_x_1150_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1230_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___y_1210_; lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = lean_unsigned_to_nat(1024u);
v___x_1227_ = lean_nat_dec_le(v___x_1226_, v_prec_1151_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1210_ = v___x_1228_;
goto v___jp_1209_;
}
else
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1210_ = v___x_1229_;
goto v___jp_1209_;
}
v___jp_1209_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1211_ = lean_box(1);
v___x_1212_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__8));
v___x_1213_ = l_Nat_reprFast(v_lhs_1204_);
v___x_1214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set_tag(v___x_1207_, 5);
lean_ctor_set(v___x_1207_, 1, v___x_1214_);
lean_ctor_set(v___x_1207_, 0, v___x_1212_);
v___x_1216_ = v___x_1207_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v___x_1211_);
v___x_1218_ = l_Nat_reprFast(v_n_1205_);
v___x_1219_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
v___x_1220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1217_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
lean_inc(v___y_1210_);
v___x_1221_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___y_1210_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = 0;
v___x_1223_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1223_, 0, v___x_1221_);
lean_ctor_set_uint8(v___x_1223_, sizeof(void*)*1, v___x_1222_);
v___x_1224_ = l_Repr_addAppParen(v___x_1223_, v_prec_1151_);
return v___x_1224_;
}
}
}
}
case 3:
{
lean_object* v_lhs_1231_; lean_object* v_n_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1257_; 
v_lhs_1231_ = lean_ctor_get(v_x_1150_, 0);
v_n_1232_ = lean_ctor_get(v_x_1150_, 1);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_x_1150_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1234_ = v_x_1150_;
v_isShared_1235_ = v_isSharedCheck_1257_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_n_1232_);
lean_inc(v_lhs_1231_);
lean_dec(v_x_1150_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1257_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___y_1237_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = lean_unsigned_to_nat(1024u);
v___x_1254_ = lean_nat_dec_le(v___x_1253_, v_prec_1151_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; 
v___x_1255_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1237_ = v___x_1255_;
goto v___jp_1236_;
}
else
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1237_ = v___x_1256_;
goto v___jp_1236_;
}
v___jp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1238_ = lean_box(1);
v___x_1239_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__11));
v___x_1240_ = l_Nat_reprFast(v_lhs_1231_);
v___x_1241_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set_tag(v___x_1234_, 5);
lean_ctor_set(v___x_1234_, 1, v___x_1241_);
lean_ctor_set(v___x_1234_, 0, v___x_1239_);
v___x_1243_ = v___x_1234_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
lean_ctor_set(v___x_1244_, 1, v___x_1238_);
v___x_1245_ = l_Nat_reprFast(v_n_1232_);
v___x_1246_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
v___x_1247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1244_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
lean_inc(v___y_1237_);
v___x_1248_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___y_1237_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = 0;
v___x_1250_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set_uint8(v___x_1250_, sizeof(void*)*1, v___x_1249_);
v___x_1251_ = l_Repr_addAppParen(v___x_1250_, v_prec_1151_);
return v___x_1251_;
}
}
}
}
case 4:
{
lean_object* v_n_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1278_; 
v_n_1258_ = lean_ctor_get(v_x_1150_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_x_1150_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1260_ = v_x_1150_;
v_isShared_1261_ = v_isSharedCheck_1278_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_n_1258_);
lean_dec(v_x_1150_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1278_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___y_1263_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1274_ = lean_unsigned_to_nat(1024u);
v___x_1275_ = lean_nat_dec_le(v___x_1274_, v_prec_1151_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1263_ = v___x_1276_;
goto v___jp_1262_;
}
else
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1263_ = v___x_1277_;
goto v___jp_1262_;
}
v___jp_1262_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1264_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__14));
v___x_1265_ = l_Nat_reprFast(v_n_1258_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set_tag(v___x_1260_, 3);
lean_ctor_set(v___x_1260_, 0, v___x_1265_);
v___x_1267_ = v___x_1260_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1264_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
lean_inc(v___y_1263_);
v___x_1269_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___y_1263_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = 0;
v___x_1271_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1271_, 0, v___x_1269_);
lean_ctor_set_uint8(v___x_1271_, sizeof(void*)*1, v___x_1270_);
v___x_1272_ = l_Repr_addAppParen(v___x_1271_, v_prec_1151_);
return v___x_1272_;
}
}
}
}
case 5:
{
lean_object* v_bvarIdx_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1299_; 
v_bvarIdx_1279_ = lean_ctor_get(v_x_1150_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_x_1150_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1281_ = v_x_1150_;
v_isShared_1282_ = v_isSharedCheck_1299_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_bvarIdx_1279_);
lean_dec(v_x_1150_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1299_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___y_1284_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = lean_unsigned_to_nat(1024u);
v___x_1296_ = lean_nat_dec_le(v___x_1295_, v_prec_1151_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1284_ = v___x_1297_;
goto v___jp_1283_;
}
else
{
lean_object* v___x_1298_; 
v___x_1298_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1284_ = v___x_1298_;
goto v___jp_1283_;
}
v___jp_1283_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1285_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__17));
v___x_1286_ = l_Nat_reprFast(v_bvarIdx_1279_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set_tag(v___x_1281_, 3);
lean_ctor_set(v___x_1281_, 0, v___x_1286_);
v___x_1288_ = v___x_1281_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1285_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
lean_inc(v___y_1284_);
v___x_1290_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___y_1284_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = 0;
v___x_1292_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1292_, 0, v___x_1290_);
lean_ctor_set_uint8(v___x_1292_, sizeof(void*)*1, v___x_1291_);
v___x_1293_ = l_Repr_addAppParen(v___x_1292_, v_prec_1151_);
return v___x_1293_;
}
}
}
}
case 6:
{
lean_object* v_bvarIdx_1300_; uint8_t v_strict_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1325_; 
v_bvarIdx_1300_ = lean_ctor_get(v_x_1150_, 0);
v_strict_1301_ = lean_ctor_get_uint8(v_x_1150_, sizeof(void*)*1);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_x_1150_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1303_ = v_x_1150_;
v_isShared_1304_ = v_isSharedCheck_1325_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_bvarIdx_1300_);
lean_dec(v_x_1150_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1325_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___y_1306_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1321_ = lean_unsigned_to_nat(1024u);
v___x_1322_ = lean_nat_dec_le(v___x_1321_, v_prec_1151_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1306_ = v___x_1323_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1324_; 
v___x_1324_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1306_ = v___x_1324_;
goto v___jp_1305_;
}
v___jp_1305_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; lean_object* v___x_1318_; 
v___x_1307_ = lean_box(1);
v___x_1308_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__20));
v___x_1309_ = l_Nat_reprFast(v_bvarIdx_1300_);
v___x_1310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
v___x_1311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1308_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
v___x_1312_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
lean_ctor_set(v___x_1312_, 1, v___x_1307_);
v___x_1313_ = l_Bool_repr___redArg(v_strict_1301_);
v___x_1314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
lean_inc(v___y_1306_);
v___x_1315_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___y_1306_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = 0;
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1315_);
v___x_1318_ = v___x_1303_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1315_);
v___x_1318_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1319_; 
lean_ctor_set_uint8(v___x_1318_, sizeof(void*)*1, v___x_1316_);
v___x_1319_ = l_Repr_addAppParen(v___x_1318_, v_prec_1151_);
return v___x_1319_;
}
}
}
}
case 7:
{
lean_object* v_n_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1346_; 
v_n_1326_ = lean_ctor_get(v_x_1150_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_x_1150_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1328_ = v_x_1150_;
v_isShared_1329_ = v_isSharedCheck_1346_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_n_1326_);
lean_dec(v_x_1150_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1346_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___y_1331_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1342_ = lean_unsigned_to_nat(1024u);
v___x_1343_ = lean_nat_dec_le(v___x_1342_, v_prec_1151_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1331_ = v___x_1344_;
goto v___jp_1330_;
}
else
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1331_ = v___x_1345_;
goto v___jp_1330_;
}
v___jp_1330_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1332_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__23));
v___x_1333_ = l_Nat_reprFast(v_n_1326_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set_tag(v___x_1328_, 3);
lean_ctor_set(v___x_1328_, 0, v___x_1333_);
v___x_1335_ = v___x_1328_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1332_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
lean_inc(v___y_1331_);
v___x_1337_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___y_1331_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = 0;
v___x_1339_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*1, v___x_1338_);
v___x_1340_ = l_Repr_addAppParen(v___x_1339_, v_prec_1151_);
return v___x_1340_;
}
}
}
}
case 8:
{
lean_object* v_e_1347_; lean_object* v___y_1349_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v_e_1347_ = lean_ctor_get(v_x_1150_, 0);
lean_inc_ref(v_e_1347_);
lean_dec_ref(v_x_1150_);
v___x_1358_ = lean_unsigned_to_nat(1024u);
v___x_1359_ = lean_nat_dec_le(v___x_1358_, v_prec_1151_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1349_ = v___x_1360_;
goto v___jp_1348_;
}
else
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1349_ = v___x_1361_;
goto v___jp_1348_;
}
v___jp_1348_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1350_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__26));
v___x_1351_ = lean_unsigned_to_nat(1024u);
v___x_1352_ = l_Lean_instReprExpr_repr(v_e_1347_, v___x_1351_);
v___x_1353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1350_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
lean_inc(v___y_1349_);
v___x_1354_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___y_1349_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = 0;
v___x_1356_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set_uint8(v___x_1356_, sizeof(void*)*1, v___x_1355_);
v___x_1357_ = l_Repr_addAppParen(v___x_1356_, v_prec_1151_);
return v___x_1357_;
}
}
case 9:
{
lean_object* v_e_1362_; lean_object* v___y_1364_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v_e_1362_ = lean_ctor_get(v_x_1150_, 0);
lean_inc_ref(v_e_1362_);
lean_dec_ref(v_x_1150_);
v___x_1373_ = lean_unsigned_to_nat(1024u);
v___x_1374_ = lean_nat_dec_le(v___x_1373_, v_prec_1151_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1364_ = v___x_1375_;
goto v___jp_1363_;
}
else
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1364_ = v___x_1376_;
goto v___jp_1363_;
}
v___jp_1363_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1365_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__29));
v___x_1366_ = lean_unsigned_to_nat(1024u);
v___x_1367_ = l_Lean_instReprExpr_repr(v_e_1362_, v___x_1366_);
v___x_1368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1365_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
lean_inc(v___y_1364_);
v___x_1369_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___y_1364_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = 0;
v___x_1371_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set_uint8(v___x_1371_, sizeof(void*)*1, v___x_1370_);
v___x_1372_ = l_Repr_addAppParen(v___x_1371_, v_prec_1151_);
return v___x_1372_;
}
}
default: 
{
lean_object* v_bvarIdx_1377_; uint8_t v_strict_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1402_; 
v_bvarIdx_1377_ = lean_ctor_get(v_x_1150_, 0);
v_strict_1378_ = lean_ctor_get_uint8(v_x_1150_, sizeof(void*)*1);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_x_1150_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1380_ = v_x_1150_;
v_isShared_1381_ = v_isSharedCheck_1402_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_bvarIdx_1377_);
lean_dec(v_x_1150_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1402_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___y_1383_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1398_ = lean_unsigned_to_nat(1024u);
v___x_1399_ = lean_nat_dec_le(v___x_1398_, v_prec_1151_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1383_ = v___x_1400_;
goto v___jp_1382_;
}
else
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1383_ = v___x_1401_;
goto v___jp_1382_;
}
v___jp_1382_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; lean_object* v___x_1395_; 
v___x_1384_ = lean_box(1);
v___x_1385_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__32));
v___x_1386_ = l_Nat_reprFast(v_bvarIdx_1377_);
v___x_1387_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
v___x_1388_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1385_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
v___x_1389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
lean_ctor_set(v___x_1389_, 1, v___x_1384_);
v___x_1390_ = l_Bool_repr___redArg(v_strict_1378_);
v___x_1391_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1389_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
lean_inc(v___y_1383_);
v___x_1392_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___y_1383_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = 0;
if (v_isShared_1381_ == 0)
{
lean_ctor_set_tag(v___x_1380_, 6);
lean_ctor_set(v___x_1380_, 0, v___x_1392_);
v___x_1395_ = v___x_1380_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1392_);
v___x_1395_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1396_; 
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*1, v___x_1393_);
v___x_1396_ = l_Repr_addAppParen(v___x_1395_, v_prec_1151_);
return v___x_1396_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___boxed(lean_object* v_x_1403_, lean_object* v_prec_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr(v_x_1403_, v_prec_1404_);
lean_dec(v_prec_1404_);
return v_res_1405_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(lean_object* v_x_1408_, lean_object* v_x_1409_){
_start:
{
lean_object* v_lhs_1411_; lean_object* v_rhs_1412_; lean_object* v_lhs_x27_1413_; lean_object* v_rhs_x27_1414_; lean_object* v_lhs_1418_; lean_object* v_n_1419_; lean_object* v_lhs_x27_1420_; lean_object* v_n_x27_1421_; lean_object* v_bvarIdx_1425_; uint8_t v_strict_1426_; lean_object* v_bvarIdx_x27_1427_; uint8_t v_strict_x27_1428_; lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1430_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_1408_);
v___x_1431_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_1409_);
v___x_1432_ = lean_nat_dec_eq(v___x_1430_, v___x_1431_);
lean_dec(v___x_1431_);
lean_dec(v___x_1430_);
if (v___x_1432_ == 0)
{
return v___x_1432_;
}
else
{
switch(lean_obj_tag(v_x_1408_))
{
case 0:
{
lean_object* v_lhs_1433_; lean_object* v_rhs_1434_; lean_object* v_lhs_1435_; lean_object* v_rhs_1436_; 
v_lhs_1433_ = lean_ctor_get(v_x_1408_, 0);
v_rhs_1434_ = lean_ctor_get(v_x_1408_, 1);
v_lhs_1435_ = lean_ctor_get(v_x_1409_, 0);
v_rhs_1436_ = lean_ctor_get(v_x_1409_, 1);
v_lhs_1411_ = v_lhs_1433_;
v_rhs_1412_ = v_rhs_1434_;
v_lhs_x27_1413_ = v_lhs_1435_;
v_rhs_x27_1414_ = v_rhs_1436_;
goto v___jp_1410_;
}
case 1:
{
lean_object* v_lhs_1437_; lean_object* v_rhs_1438_; lean_object* v_lhs_1439_; lean_object* v_rhs_1440_; 
v_lhs_1437_ = lean_ctor_get(v_x_1408_, 0);
v_rhs_1438_ = lean_ctor_get(v_x_1408_, 1);
v_lhs_1439_ = lean_ctor_get(v_x_1409_, 0);
v_rhs_1440_ = lean_ctor_get(v_x_1409_, 1);
v_lhs_1411_ = v_lhs_1437_;
v_rhs_1412_ = v_rhs_1438_;
v_lhs_x27_1413_ = v_lhs_1439_;
v_rhs_x27_1414_ = v_rhs_1440_;
goto v___jp_1410_;
}
case 2:
{
lean_object* v_lhs_1441_; lean_object* v_n_1442_; lean_object* v_lhs_1443_; lean_object* v_n_1444_; 
v_lhs_1441_ = lean_ctor_get(v_x_1408_, 0);
v_n_1442_ = lean_ctor_get(v_x_1408_, 1);
v_lhs_1443_ = lean_ctor_get(v_x_1409_, 0);
v_n_1444_ = lean_ctor_get(v_x_1409_, 1);
v_lhs_1418_ = v_lhs_1441_;
v_n_1419_ = v_n_1442_;
v_lhs_x27_1420_ = v_lhs_1443_;
v_n_x27_1421_ = v_n_1444_;
goto v___jp_1417_;
}
case 3:
{
lean_object* v_lhs_1445_; lean_object* v_n_1446_; lean_object* v_lhs_1447_; lean_object* v_n_1448_; 
v_lhs_1445_ = lean_ctor_get(v_x_1408_, 0);
v_n_1446_ = lean_ctor_get(v_x_1408_, 1);
v_lhs_1447_ = lean_ctor_get(v_x_1409_, 0);
v_n_1448_ = lean_ctor_get(v_x_1409_, 1);
v_lhs_1418_ = v_lhs_1445_;
v_n_1419_ = v_n_1446_;
v_lhs_x27_1420_ = v_lhs_1447_;
v_n_x27_1421_ = v_n_1448_;
goto v___jp_1417_;
}
case 6:
{
lean_object* v_bvarIdx_1449_; uint8_t v_strict_1450_; lean_object* v_bvarIdx_1451_; uint8_t v_strict_1452_; 
v_bvarIdx_1449_ = lean_ctor_get(v_x_1408_, 0);
v_strict_1450_ = lean_ctor_get_uint8(v_x_1408_, sizeof(void*)*1);
v_bvarIdx_1451_ = lean_ctor_get(v_x_1409_, 0);
v_strict_1452_ = lean_ctor_get_uint8(v_x_1409_, sizeof(void*)*1);
v_bvarIdx_1425_ = v_bvarIdx_1449_;
v_strict_1426_ = v_strict_1450_;
v_bvarIdx_x27_1427_ = v_bvarIdx_1451_;
v_strict_x27_1428_ = v_strict_1452_;
goto v___jp_1424_;
}
case 8:
{
lean_object* v_e_1453_; lean_object* v_e_1454_; uint8_t v___x_1455_; 
v_e_1453_ = lean_ctor_get(v_x_1408_, 0);
v_e_1454_ = lean_ctor_get(v_x_1409_, 0);
v___x_1455_ = lean_expr_eqv(v_e_1453_, v_e_1454_);
return v___x_1455_;
}
case 9:
{
lean_object* v_e_1456_; lean_object* v_e_1457_; uint8_t v___x_1458_; 
v_e_1456_ = lean_ctor_get(v_x_1408_, 0);
v_e_1457_ = lean_ctor_get(v_x_1409_, 0);
v___x_1458_ = lean_expr_eqv(v_e_1456_, v_e_1457_);
return v___x_1458_;
}
case 10:
{
lean_object* v_bvarIdx_1459_; uint8_t v_strict_1460_; lean_object* v_bvarIdx_1461_; uint8_t v_strict_1462_; 
v_bvarIdx_1459_ = lean_ctor_get(v_x_1408_, 0);
v_strict_1460_ = lean_ctor_get_uint8(v_x_1408_, sizeof(void*)*1);
v_bvarIdx_1461_ = lean_ctor_get(v_x_1409_, 0);
v_strict_1462_ = lean_ctor_get_uint8(v_x_1409_, sizeof(void*)*1);
v_bvarIdx_1425_ = v_bvarIdx_1459_;
v_strict_1426_ = v_strict_1460_;
v_bvarIdx_x27_1427_ = v_bvarIdx_1461_;
v_strict_x27_1428_ = v_strict_1462_;
goto v___jp_1424_;
}
default: 
{
lean_object* v_n_1463_; lean_object* v_n_1464_; uint8_t v___x_1465_; 
v_n_1463_ = lean_ctor_get(v_x_1408_, 0);
v_n_1464_ = lean_ctor_get(v_x_1409_, 0);
v___x_1465_ = lean_nat_dec_eq(v_n_1463_, v_n_1464_);
return v___x_1465_;
}
}
}
v___jp_1410_:
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_nat_dec_eq(v_lhs_1411_, v_lhs_x27_1413_);
if (v___x_1415_ == 0)
{
return v___x_1415_;
}
else
{
uint8_t v___x_1416_; 
v___x_1416_ = l_Lean_Meta_Grind_instBEqCnstrRHS_beq(v_rhs_1412_, v_rhs_x27_1414_);
return v___x_1416_;
}
}
v___jp_1417_:
{
uint8_t v___x_1422_; 
v___x_1422_ = lean_nat_dec_eq(v_lhs_1418_, v_lhs_x27_1420_);
if (v___x_1422_ == 0)
{
return v___x_1422_;
}
else
{
uint8_t v___x_1423_; 
v___x_1423_ = lean_nat_dec_eq(v_n_1419_, v_n_x27_1421_);
return v___x_1423_;
}
}
v___jp_1424_:
{
uint8_t v___x_1429_; 
v___x_1429_ = lean_nat_dec_eq(v_bvarIdx_1425_, v_bvarIdx_x27_1427_);
if (v___x_1429_ == 0)
{
return v___x_1429_;
}
else
{
if (v_strict_1426_ == 0)
{
if (v_strict_x27_1428_ == 0)
{
return v___x_1429_;
}
else
{
return v_strict_1426_;
}
}
else
{
return v_strict_x27_1428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq___boxed(lean_object* v_x_1466_, lean_object* v_x_1467_){
_start:
{
uint8_t v_res_1468_; lean_object* v_r_1469_; 
v_res_1468_ = l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(v_x_1466_, v_x_1467_);
lean_dec_ref(v_x_1467_);
lean_dec_ref(v_x_1466_);
v_r_1469_ = lean_box(v_res_1468_);
return v_r_1469_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0(void){
_start:
{
uint8_t v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1472_ = 0;
v___x_1473_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default));
v___x_1474_ = l_Lean_Meta_Grind_instInhabitedOrigin_default;
v___x_1475_ = lean_box(0);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_1478_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_1479_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v___x_1477_);
lean_ctor_set(v___x_1479_, 2, v___x_1476_);
lean_ctor_set(v___x_1479_, 3, v___x_1475_);
lean_ctor_set(v___x_1479_, 4, v___x_1475_);
lean_ctor_set(v___x_1479_, 5, v___x_1474_);
lean_ctor_set(v___x_1479_, 6, v___x_1473_);
lean_ctor_set(v___x_1479_, 7, v___x_1475_);
lean_ctor_set_uint8(v___x_1479_, sizeof(void*)*8, v___x_1472_);
return v___x_1479_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default(void){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0, &l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0);
return v___x_1480_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem(void){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default;
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0(lean_object* v_thm_1482_){
_start:
{
lean_object* v_symbols_1483_; 
v_symbols_1483_ = lean_ctor_get(v_thm_1482_, 4);
lean_inc(v_symbols_1483_);
return v_symbols_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0___boxed(lean_object* v_thm_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0(v_thm_1484_);
lean_dec_ref(v_thm_1484_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__1(lean_object* v_thm_1486_, lean_object* v_symbols_1487_){
_start:
{
lean_object* v_levelParams_1488_; lean_object* v_proof_1489_; lean_object* v_numParams_1490_; lean_object* v_patterns_1491_; lean_object* v_origin_1492_; lean_object* v_kind_1493_; uint8_t v_minIndexable_1494_; lean_object* v_cnstrs_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
v_levelParams_1488_ = lean_ctor_get(v_thm_1486_, 0);
v_proof_1489_ = lean_ctor_get(v_thm_1486_, 1);
v_numParams_1490_ = lean_ctor_get(v_thm_1486_, 2);
v_patterns_1491_ = lean_ctor_get(v_thm_1486_, 3);
v_origin_1492_ = lean_ctor_get(v_thm_1486_, 5);
v_kind_1493_ = lean_ctor_get(v_thm_1486_, 6);
v_minIndexable_1494_ = lean_ctor_get_uint8(v_thm_1486_, sizeof(void*)*8);
v_cnstrs_1495_ = lean_ctor_get(v_thm_1486_, 7);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_thm_1486_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; 
v_unused_1503_ = lean_ctor_get(v_thm_1486_, 4);
lean_dec(v_unused_1503_);
v___x_1497_ = v_thm_1486_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_cnstrs_1495_);
lean_inc(v_kind_1493_);
lean_inc(v_origin_1492_);
lean_inc(v_patterns_1491_);
lean_inc(v_numParams_1490_);
lean_inc(v_proof_1489_);
lean_inc(v_levelParams_1488_);
lean_dec(v_thm_1486_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 4, v_symbols_1487_);
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_levelParams_1488_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_proof_1489_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_numParams_1490_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_patterns_1491_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v_symbols_1487_);
lean_ctor_set(v_reuseFailAlloc_1501_, 5, v_origin_1492_);
lean_ctor_set(v_reuseFailAlloc_1501_, 6, v_kind_1493_);
lean_ctor_set(v_reuseFailAlloc_1501_, 7, v_cnstrs_1495_);
lean_ctor_set_uint8(v_reuseFailAlloc_1501_, sizeof(void*)*8, v_minIndexable_1494_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2(lean_object* v_thm_1504_){
_start:
{
lean_object* v_origin_1505_; 
v_origin_1505_ = lean_ctor_get(v_thm_1504_, 5);
lean_inc_ref(v_origin_1505_);
return v_origin_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2___boxed(lean_object* v_thm_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2(v_thm_1506_);
lean_dec_ref(v_thm_1506_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3(lean_object* v_thm_1508_){
_start:
{
lean_object* v_proof_1509_; 
v_proof_1509_ = lean_ctor_get(v_thm_1508_, 1);
lean_inc_ref(v_proof_1509_);
return v_proof_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3___boxed(lean_object* v_thm_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3(v_thm_1510_);
lean_dec_ref(v_thm_1510_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4(lean_object* v_thm_1512_){
_start:
{
lean_object* v_levelParams_1513_; 
v_levelParams_1513_ = lean_ctor_get(v_thm_1512_, 0);
lean_inc_ref(v_levelParams_1513_);
return v_levelParams_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4___boxed(lean_object* v_thm_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4(v_thm_1514_);
lean_dec_ref(v_thm_1514_);
return v_res_1515_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1528_ = l_Lean_Meta_Grind_instInhabitedOrigin_default;
v___x_1529_ = lean_box(0);
v___x_1530_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_1531_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_1532_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v___x_1530_);
lean_ctor_set(v___x_1532_, 2, v___x_1529_);
lean_ctor_set(v___x_1532_, 3, v___x_1528_);
return v___x_1532_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default(void){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0, &l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0);
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem(void){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default;
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0(lean_object* v_thm_1535_){
_start:
{
lean_object* v_symbols_1536_; 
v_symbols_1536_ = lean_ctor_get(v_thm_1535_, 2);
lean_inc(v_symbols_1536_);
return v_symbols_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0___boxed(lean_object* v_thm_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0(v_thm_1537_);
lean_dec_ref(v_thm_1537_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__1(lean_object* v_thm_1539_, lean_object* v_symbols_1540_){
_start:
{
lean_object* v_levelParams_1541_; lean_object* v_proof_1542_; lean_object* v_origin_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
v_levelParams_1541_ = lean_ctor_get(v_thm_1539_, 0);
v_proof_1542_ = lean_ctor_get(v_thm_1539_, 1);
v_origin_1543_ = lean_ctor_get(v_thm_1539_, 3);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_thm_1539_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v_thm_1539_, 2);
lean_dec(v_unused_1551_);
v___x_1545_ = v_thm_1539_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_origin_1543_);
lean_inc(v_proof_1542_);
lean_inc(v_levelParams_1541_);
lean_dec(v_thm_1539_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 2, v_symbols_1540_);
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_levelParams_1541_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_proof_1542_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_symbols_1540_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v_origin_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2(lean_object* v_thm_1552_){
_start:
{
lean_object* v_origin_1553_; 
v_origin_1553_ = lean_ctor_get(v_thm_1552_, 3);
lean_inc_ref(v_origin_1553_);
return v_origin_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2___boxed(lean_object* v_thm_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2(v_thm_1554_);
lean_dec_ref(v_thm_1554_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3(lean_object* v_thm_1556_){
_start:
{
lean_object* v_proof_1557_; 
v_proof_1557_ = lean_ctor_get(v_thm_1556_, 1);
lean_inc_ref(v_proof_1557_);
return v_proof_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3___boxed(lean_object* v_thm_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3(v_thm_1558_);
lean_dec_ref(v_thm_1558_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4(lean_object* v_thm_1560_){
_start:
{
lean_object* v_levelParams_1561_; 
v_levelParams_1561_ = lean_ctor_get(v_thm_1560_, 0);
lean_inc_ref(v_levelParams_1561_);
return v_levelParams_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4___boxed(lean_object* v_thm_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4(v_thm_1562_);
lean_dec_ref(v_thm_1562_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorIdx(lean_object* v_x_1576_){
_start:
{
switch(lean_obj_tag(v_x_1576_))
{
case 0:
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_unsigned_to_nat(0u);
return v___x_1577_;
}
case 1:
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_unsigned_to_nat(1u);
return v___x_1578_;
}
case 2:
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_unsigned_to_nat(2u);
return v___x_1579_;
}
case 3:
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_unsigned_to_nat(3u);
return v___x_1580_;
}
default: 
{
lean_object* v___x_1581_; 
v___x_1581_ = lean_unsigned_to_nat(4u);
return v___x_1581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorIdx___boxed(lean_object* v_x_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Meta_Grind_Entry_ctorIdx(v_x_1582_);
lean_dec_ref(v_x_1582_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim___redArg(lean_object* v_t_1584_, lean_object* v_k_1585_){
_start:
{
switch(lean_obj_tag(v_t_1584_))
{
case 2:
{
lean_object* v_declName_1586_; uint8_t v_eager_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v_declName_1586_ = lean_ctor_get(v_t_1584_, 0);
lean_inc(v_declName_1586_);
v_eager_1587_ = lean_ctor_get_uint8(v_t_1584_, sizeof(void*)*1);
lean_dec_ref(v_t_1584_);
v___x_1588_ = lean_box(v_eager_1587_);
v___x_1589_ = lean_apply_2(v_k_1585_, v_declName_1586_, v___x_1588_);
return v___x_1589_;
}
case 3:
{
lean_object* v_thm_1590_; lean_object* v___x_1591_; 
v_thm_1590_ = lean_ctor_get(v_t_1584_, 0);
lean_inc_ref(v_thm_1590_);
lean_dec_ref(v_t_1584_);
v___x_1591_ = lean_apply_1(v_k_1585_, v_thm_1590_);
return v___x_1591_;
}
case 4:
{
lean_object* v_thm_1592_; lean_object* v___x_1593_; 
v_thm_1592_ = lean_ctor_get(v_t_1584_, 0);
lean_inc_ref(v_thm_1592_);
lean_dec_ref(v_t_1584_);
v___x_1593_ = lean_apply_1(v_k_1585_, v_thm_1592_);
return v___x_1593_;
}
default: 
{
lean_object* v_declName_1594_; lean_object* v___x_1595_; 
v_declName_1594_ = lean_ctor_get(v_t_1584_, 0);
lean_inc(v_declName_1594_);
lean_dec_ref(v_t_1584_);
v___x_1595_ = lean_apply_1(v_k_1585_, v_declName_1594_);
return v___x_1595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim(lean_object* v_motive_1596_, lean_object* v_ctorIdx_1597_, lean_object* v_t_1598_, lean_object* v_h_1599_, lean_object* v_k_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1598_, v_k_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim___boxed(lean_object* v_motive_1602_, lean_object* v_ctorIdx_1603_, lean_object* v_t_1604_, lean_object* v_h_1605_, lean_object* v_k_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_Meta_Grind_Entry_ctorElim(v_motive_1602_, v_ctorIdx_1603_, v_t_1604_, v_h_1605_, v_k_1606_);
lean_dec(v_ctorIdx_1603_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ext_elim___redArg(lean_object* v_t_1608_, lean_object* v_ext_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1608_, v_ext_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ext_elim(lean_object* v_motive_1611_, lean_object* v_t_1612_, lean_object* v_h_1613_, lean_object* v_ext_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1612_, v_ext_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_funCC_elim___redArg(lean_object* v_t_1616_, lean_object* v_funCC_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1616_, v_funCC_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_funCC_elim(lean_object* v_motive_1619_, lean_object* v_t_1620_, lean_object* v_h_1621_, lean_object* v_funCC_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1620_, v_funCC_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_cases_elim___redArg(lean_object* v_t_1624_, lean_object* v_cases_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1624_, v_cases_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_cases_elim(lean_object* v_motive_1627_, lean_object* v_t_1628_, lean_object* v_h_1629_, lean_object* v_cases_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1628_, v_cases_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ematch_elim___redArg(lean_object* v_t_1632_, lean_object* v_ematch_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1632_, v_ematch_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ematch_elim(lean_object* v_motive_1635_, lean_object* v_t_1636_, lean_object* v_h_1637_, lean_object* v_ematch_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1636_, v_ematch_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_inj_elim___redArg(lean_object* v_t_1640_, lean_object* v_inj_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1640_, v_inj_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_inj_elim(lean_object* v_motive_1643_, lean_object* v_t_1644_, lean_object* v_h_1645_, lean_object* v_inj_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1644_, v_inj_1646_);
return v___x_1647_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0);
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0(lean_object* v_00_u03b2_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1);
return v___x_1656_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0(lean_box(0));
return v___x_1657_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1(void){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_Meta_Grind_Theorems_mkEmpty(lean_box(0));
return v___x_1658_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1659_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1);
v___x_1660_ = l_Lean_NameSet_empty;
v___x_1661_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0);
v___x_1662_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1, &l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1);
v___x_1663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
lean_ctor_set(v___x_1663_, 1, v___x_1661_);
lean_ctor_set(v___x_1663_, 2, v___x_1660_);
lean_ctor_set(v___x_1663_, 3, v___x_1659_);
lean_ctor_set(v___x_1663_, 4, v___x_1659_);
return v___x_1663_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default(void){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2);
return v___x_1664_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState(void){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_x_1666_, lean_object* v_x_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_){
_start:
{
lean_object* v_ks_1670_; lean_object* v_vs_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1697_; 
v_ks_1670_ = lean_ctor_get(v_x_1666_, 0);
v_vs_1671_ = lean_ctor_get(v_x_1666_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_x_1666_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1673_ = v_x_1666_;
v_isShared_1674_ = v_isSharedCheck_1697_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_vs_1671_);
lean_inc(v_ks_1670_);
lean_dec(v_x_1666_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1697_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1675_ = lean_array_get_size(v_ks_1670_);
v___x_1676_ = lean_nat_dec_lt(v_x_1667_, v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1680_; 
lean_dec(v_x_1667_);
v___x_1677_ = lean_array_push(v_ks_1670_, v_x_1668_);
v___x_1678_ = lean_array_push(v_vs_1671_, v_x_1669_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 1, v___x_1678_);
lean_ctor_set(v___x_1673_, 0, v___x_1677_);
v___x_1680_ = v___x_1673_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
else
{
lean_object* v_k_x27_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; 
v_k_x27_1682_ = lean_array_fget_borrowed(v_ks_1670_, v_x_1667_);
v___x_1683_ = l_Lean_Meta_Grind_Origin_key(v_x_1668_);
v___x_1684_ = l_Lean_Meta_Grind_Origin_key(v_k_x27_1682_);
v___x_1685_ = lean_name_eq(v___x_1683_, v___x_1684_);
lean_dec(v___x_1684_);
lean_dec(v___x_1683_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1687_; 
if (v_isShared_1674_ == 0)
{
v___x_1687_ = v___x_1673_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_ks_1670_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_vs_1671_);
v___x_1687_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = lean_unsigned_to_nat(1u);
v___x_1689_ = lean_nat_add(v_x_1667_, v___x_1688_);
lean_dec(v_x_1667_);
v_x_1666_ = v___x_1687_;
v_x_1667_ = v___x_1689_;
goto _start;
}
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1695_; 
v___x_1692_ = lean_array_fset(v_ks_1670_, v_x_1667_, v_x_1668_);
v___x_1693_ = lean_array_fset(v_vs_1671_, v_x_1667_, v_x_1669_);
lean_dec(v_x_1667_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 1, v___x_1693_);
lean_ctor_set(v___x_1673_, 0, v___x_1692_);
v___x_1695_ = v___x_1673_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1692_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_n_1698_, lean_object* v_k_1699_, lean_object* v_v_1700_){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = lean_unsigned_to_nat(0u);
v___x_1702_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(v_n_1698_, v___x_1701_, v_k_1699_, v_v_1700_);
return v___x_1702_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1704_, size_t v_x_1705_, size_t v_x_1706_, lean_object* v_x_1707_, lean_object* v_x_1708_){
_start:
{
if (lean_obj_tag(v_x_1704_) == 0)
{
lean_object* v_es_1709_; size_t v___x_1710_; size_t v___x_1711_; size_t v___x_1712_; size_t v___x_1713_; lean_object* v_j_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v_es_1709_ = lean_ctor_get(v_x_1704_, 0);
v___x_1710_ = ((size_t)5ULL);
v___x_1711_ = ((size_t)1ULL);
v___x_1712_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1);
v___x_1713_ = lean_usize_land(v_x_1705_, v___x_1712_);
v_j_1714_ = lean_usize_to_nat(v___x_1713_);
v___x_1715_ = lean_array_get_size(v_es_1709_);
v___x_1716_ = lean_nat_dec_lt(v_j_1714_, v___x_1715_);
if (v___x_1716_ == 0)
{
lean_dec(v_j_1714_);
lean_dec(v_x_1708_);
lean_dec_ref(v_x_1707_);
return v_x_1704_;
}
else
{
lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1755_; 
lean_inc_ref(v_es_1709_);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_x_1704_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; 
v_unused_1756_ = lean_ctor_get(v_x_1704_, 0);
lean_dec(v_unused_1756_);
v___x_1718_ = v_x_1704_;
v_isShared_1719_ = v_isSharedCheck_1755_;
goto v_resetjp_1717_;
}
else
{
lean_dec(v_x_1704_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1755_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v_v_1720_; lean_object* v___x_1721_; lean_object* v_xs_x27_1722_; lean_object* v___y_1724_; 
v_v_1720_ = lean_array_fget(v_es_1709_, v_j_1714_);
v___x_1721_ = lean_box(0);
v_xs_x27_1722_ = lean_array_fset(v_es_1709_, v_j_1714_, v___x_1721_);
switch(lean_obj_tag(v_v_1720_))
{
case 0:
{
lean_object* v_key_1729_; lean_object* v_val_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1742_; 
v_key_1729_ = lean_ctor_get(v_v_1720_, 0);
v_val_1730_ = lean_ctor_get(v_v_1720_, 1);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_v_1720_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1732_ = v_v_1720_;
v_isShared_1733_ = v_isSharedCheck_1742_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_val_1730_);
lean_inc(v_key_1729_);
lean_dec(v_v_1720_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1742_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1734_ = l_Lean_Meta_Grind_Origin_key(v_x_1707_);
v___x_1735_ = l_Lean_Meta_Grind_Origin_key(v_key_1729_);
v___x_1736_ = lean_name_eq(v___x_1734_, v___x_1735_);
lean_dec(v___x_1735_);
lean_dec(v___x_1734_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_del_object(v___x_1732_);
v___x_1737_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1729_, v_val_1730_, v_x_1707_, v_x_1708_);
v___x_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
v___y_1724_ = v___x_1738_;
goto v___jp_1723_;
}
else
{
lean_object* v___x_1740_; 
lean_dec(v_val_1730_);
lean_dec(v_key_1729_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 1, v_x_1708_);
lean_ctor_set(v___x_1732_, 0, v_x_1707_);
v___x_1740_ = v___x_1732_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_x_1707_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_x_1708_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
v___y_1724_ = v___x_1740_;
goto v___jp_1723_;
}
}
}
}
case 1:
{
lean_object* v_node_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1753_; 
v_node_1743_ = lean_ctor_get(v_v_1720_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_v_1720_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1745_ = v_v_1720_;
v_isShared_1746_ = v_isSharedCheck_1753_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_node_1743_);
lean_dec(v_v_1720_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1753_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
size_t v___x_1747_; size_t v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1747_ = lean_usize_shift_right(v_x_1705_, v___x_1710_);
v___x_1748_ = lean_usize_add(v_x_1706_, v___x_1711_);
v___x_1749_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_node_1743_, v___x_1747_, v___x_1748_, v_x_1707_, v_x_1708_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_1749_);
v___x_1751_ = v___x_1745_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
v___y_1724_ = v___x_1751_;
goto v___jp_1723_;
}
}
}
default: 
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1754_, 0, v_x_1707_);
lean_ctor_set(v___x_1754_, 1, v_x_1708_);
v___y_1724_ = v___x_1754_;
goto v___jp_1723_;
}
}
v___jp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1725_ = lean_array_fset(v_xs_x27_1722_, v_j_1714_, v___y_1724_);
lean_dec(v_j_1714_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1725_);
v___x_1727_ = v___x_1718_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
else
{
lean_object* v_ks_1757_; lean_object* v_vs_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1778_; 
v_ks_1757_ = lean_ctor_get(v_x_1704_, 0);
v_vs_1758_ = lean_ctor_get(v_x_1704_, 1);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_x_1704_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1760_ = v_x_1704_;
v_isShared_1761_ = v_isSharedCheck_1778_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_vs_1758_);
lean_inc(v_ks_1757_);
lean_dec(v_x_1704_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1778_;
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
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_ks_1757_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_vs_1758_);
v___x_1763_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
lean_object* v_newNode_1764_; uint8_t v___y_1766_; size_t v___x_1772_; uint8_t v___x_1773_; 
v_newNode_1764_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(v___x_1763_, v_x_1707_, v_x_1708_);
v___x_1772_ = ((size_t)7ULL);
v___x_1773_ = lean_usize_dec_le(v___x_1772_, v_x_1706_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1774_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1764_);
v___x_1775_ = lean_unsigned_to_nat(4u);
v___x_1776_ = lean_nat_dec_lt(v___x_1774_, v___x_1775_);
lean_dec(v___x_1774_);
v___y_1766_ = v___x_1776_;
goto v___jp_1765_;
}
else
{
v___y_1766_ = v___x_1773_;
goto v___jp_1765_;
}
v___jp_1765_:
{
if (v___y_1766_ == 0)
{
lean_object* v_ks_1767_; lean_object* v_vs_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_ks_1767_ = lean_ctor_get(v_newNode_1764_, 0);
lean_inc_ref(v_ks_1767_);
v_vs_1768_ = lean_ctor_get(v_newNode_1764_, 1);
lean_inc_ref(v_vs_1768_);
lean_dec_ref(v_newNode_1764_);
v___x_1769_ = lean_unsigned_to_nat(0u);
v___x_1770_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0);
v___x_1771_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_x_1706_, v_ks_1767_, v_vs_1768_, v___x_1769_, v___x_1770_);
lean_dec_ref(v_vs_1768_);
lean_dec_ref(v_ks_1767_);
return v___x_1771_;
}
else
{
return v_newNode_1764_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(size_t v_depth_1779_, lean_object* v_keys_1780_, lean_object* v_vals_1781_, lean_object* v_i_1782_, lean_object* v_entries_1783_){
_start:
{
lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1784_ = lean_array_get_size(v_keys_1780_);
v___x_1785_ = lean_nat_dec_lt(v_i_1782_, v___x_1784_);
if (v___x_1785_ == 0)
{
lean_dec(v_i_1782_);
return v_entries_1783_;
}
else
{
lean_object* v_k_1786_; lean_object* v_v_1787_; uint64_t v___y_1789_; lean_object* v___x_1800_; 
v_k_1786_ = lean_array_fget_borrowed(v_keys_1780_, v_i_1782_);
v_v_1787_ = lean_array_fget_borrowed(v_vals_1781_, v_i_1782_);
v___x_1800_ = l_Lean_Meta_Grind_Origin_key(v_k_1786_);
if (lean_obj_tag(v___x_1800_) == 0)
{
uint64_t v___x_1801_; 
v___x_1801_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1789_ = v___x_1801_;
goto v___jp_1788_;
}
else
{
uint64_t v_hash_1802_; 
v_hash_1802_ = lean_ctor_get_uint64(v___x_1800_, sizeof(void*)*2);
lean_dec(v___x_1800_);
v___y_1789_ = v_hash_1802_;
goto v___jp_1788_;
}
v___jp_1788_:
{
size_t v_h_1790_; size_t v___x_1791_; lean_object* v___x_1792_; size_t v___x_1793_; size_t v___x_1794_; size_t v___x_1795_; size_t v_h_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v_h_1790_ = lean_uint64_to_usize(v___y_1789_);
v___x_1791_ = ((size_t)5ULL);
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = ((size_t)1ULL);
v___x_1794_ = lean_usize_sub(v_depth_1779_, v___x_1793_);
v___x_1795_ = lean_usize_mul(v___x_1791_, v___x_1794_);
v_h_1796_ = lean_usize_shift_right(v_h_1790_, v___x_1795_);
v___x_1797_ = lean_nat_add(v_i_1782_, v___x_1792_);
lean_dec(v_i_1782_);
lean_inc(v_v_1787_);
lean_inc(v_k_1786_);
v___x_1798_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_entries_1783_, v_h_1796_, v_depth_1779_, v_k_1786_, v_v_1787_);
v_i_1782_ = v___x_1797_;
v_entries_1783_ = v___x_1798_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_depth_1803_, lean_object* v_keys_1804_, lean_object* v_vals_1805_, lean_object* v_i_1806_, lean_object* v_entries_1807_){
_start:
{
size_t v_depth_boxed_1808_; lean_object* v_res_1809_; 
v_depth_boxed_1808_ = lean_unbox_usize(v_depth_1803_);
lean_dec(v_depth_1803_);
v_res_1809_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_depth_boxed_1808_, v_keys_1804_, v_vals_1805_, v_i_1806_, v_entries_1807_);
lean_dec_ref(v_vals_1805_);
lean_dec_ref(v_keys_1804_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_x_1810_, lean_object* v_x_1811_, lean_object* v_x_1812_, lean_object* v_x_1813_, lean_object* v_x_1814_){
_start:
{
size_t v_x_1264__boxed_1815_; size_t v_x_1265__boxed_1816_; lean_object* v_res_1817_; 
v_x_1264__boxed_1815_ = lean_unbox_usize(v_x_1811_);
lean_dec(v_x_1811_);
v_x_1265__boxed_1816_ = lean_unbox_usize(v_x_1812_);
lean_dec(v_x_1812_);
v_res_1817_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_1810_, v_x_1264__boxed_1815_, v_x_1265__boxed_1816_, v_x_1813_, v_x_1814_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(lean_object* v_x_1818_, lean_object* v_x_1819_, lean_object* v_x_1820_){
_start:
{
uint64_t v___y_1822_; lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_Meta_Grind_Origin_key(v_x_1819_);
if (lean_obj_tag(v___x_1826_) == 0)
{
uint64_t v___x_1827_; 
v___x_1827_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1822_ = v___x_1827_;
goto v___jp_1821_;
}
else
{
uint64_t v_hash_1828_; 
v_hash_1828_ = lean_ctor_get_uint64(v___x_1826_, sizeof(void*)*2);
lean_dec(v___x_1826_);
v___y_1822_ = v_hash_1828_;
goto v___jp_1821_;
}
v___jp_1821_:
{
size_t v___x_1823_; size_t v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = lean_uint64_to_usize(v___y_1822_);
v___x_1824_ = ((size_t)1ULL);
v___x_1825_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_1818_, v___x_1823_, v___x_1824_, v_x_1819_, v_x_1820_);
return v___x_1825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(lean_object* v_keys_1829_, lean_object* v_vals_1830_, lean_object* v_i_1831_, lean_object* v_k_1832_){
_start:
{
lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1833_ = lean_array_get_size(v_keys_1829_);
v___x_1834_ = lean_nat_dec_lt(v_i_1831_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; 
lean_dec(v_i_1831_);
v___x_1835_ = lean_box(0);
return v___x_1835_;
}
else
{
lean_object* v_k_x27_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v_k_x27_1836_ = lean_array_fget_borrowed(v_keys_1829_, v_i_1831_);
v___x_1837_ = l_Lean_Meta_Grind_Origin_key(v_k_1832_);
v___x_1838_ = l_Lean_Meta_Grind_Origin_key(v_k_x27_1836_);
v___x_1839_ = lean_name_eq(v___x_1837_, v___x_1838_);
lean_dec(v___x_1838_);
lean_dec(v___x_1837_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = lean_unsigned_to_nat(1u);
v___x_1841_ = lean_nat_add(v_i_1831_, v___x_1840_);
lean_dec(v_i_1831_);
v_i_1831_ = v___x_1841_;
goto _start;
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = lean_array_fget_borrowed(v_vals_1830_, v_i_1831_);
lean_dec(v_i_1831_);
lean_inc(v___x_1843_);
v___x_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
return v___x_1844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg___boxed(lean_object* v_keys_1845_, lean_object* v_vals_1846_, lean_object* v_i_1847_, lean_object* v_k_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_keys_1845_, v_vals_1846_, v_i_1847_, v_k_1848_);
lean_dec_ref(v_k_1848_);
lean_dec_ref(v_vals_1846_);
lean_dec_ref(v_keys_1845_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(lean_object* v_x_1850_, size_t v_x_1851_, lean_object* v_x_1852_){
_start:
{
if (lean_obj_tag(v_x_1850_) == 0)
{
lean_object* v_es_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1876_; 
v_es_1853_ = lean_ctor_get(v_x_1850_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_x_1850_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1855_ = v_x_1850_;
v_isShared_1856_ = v_isSharedCheck_1876_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_es_1853_);
lean_dec(v_x_1850_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1876_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; size_t v___x_1858_; size_t v___x_1859_; size_t v___x_1860_; lean_object* v_j_1861_; lean_object* v___x_1862_; 
v___x_1857_ = lean_box(2);
v___x_1858_ = ((size_t)5ULL);
v___x_1859_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1);
v___x_1860_ = lean_usize_land(v_x_1851_, v___x_1859_);
v_j_1861_ = lean_usize_to_nat(v___x_1860_);
v___x_1862_ = lean_array_get(v___x_1857_, v_es_1853_, v_j_1861_);
lean_dec(v_j_1861_);
lean_dec_ref(v_es_1853_);
switch(lean_obj_tag(v___x_1862_))
{
case 0:
{
lean_object* v_key_1863_; lean_object* v_val_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v_key_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_key_1863_);
v_val_1864_ = lean_ctor_get(v___x_1862_, 1);
lean_inc(v_val_1864_);
lean_dec_ref(v___x_1862_);
v___x_1865_ = l_Lean_Meta_Grind_Origin_key(v_x_1852_);
v___x_1866_ = l_Lean_Meta_Grind_Origin_key(v_key_1863_);
lean_dec(v_key_1863_);
v___x_1867_ = lean_name_eq(v___x_1865_, v___x_1866_);
lean_dec(v___x_1866_);
lean_dec(v___x_1865_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; 
lean_dec(v_val_1864_);
lean_del_object(v___x_1855_);
v___x_1868_ = lean_box(0);
return v___x_1868_;
}
else
{
lean_object* v___x_1870_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set_tag(v___x_1855_, 1);
lean_ctor_set(v___x_1855_, 0, v_val_1864_);
v___x_1870_ = v___x_1855_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_val_1864_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
case 1:
{
lean_object* v_node_1872_; size_t v___x_1873_; 
lean_del_object(v___x_1855_);
v_node_1872_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_node_1872_);
lean_dec_ref(v___x_1862_);
v___x_1873_ = lean_usize_shift_right(v_x_1851_, v___x_1858_);
v_x_1850_ = v_node_1872_;
v_x_1851_ = v___x_1873_;
goto _start;
}
default: 
{
lean_object* v___x_1875_; 
lean_del_object(v___x_1855_);
v___x_1875_ = lean_box(0);
return v___x_1875_;
}
}
}
}
else
{
lean_object* v_ks_1877_; lean_object* v_vs_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v_ks_1877_ = lean_ctor_get(v_x_1850_, 0);
lean_inc_ref(v_ks_1877_);
v_vs_1878_ = lean_ctor_get(v_x_1850_, 1);
lean_inc_ref(v_vs_1878_);
lean_dec_ref(v_x_1850_);
v___x_1879_ = lean_unsigned_to_nat(0u);
v___x_1880_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_ks_1877_, v_vs_1878_, v___x_1879_, v_x_1852_);
lean_dec_ref(v_vs_1878_);
lean_dec_ref(v_ks_1877_);
return v___x_1880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_x_1881_, lean_object* v_x_1882_, lean_object* v_x_1883_){
_start:
{
size_t v_x_1478__boxed_1884_; lean_object* v_res_1885_; 
v_x_1478__boxed_1884_ = lean_unbox_usize(v_x_1882_);
lean_dec(v_x_1882_);
v_res_1885_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_1881_, v_x_1478__boxed_1884_, v_x_1883_);
lean_dec_ref(v_x_1883_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(lean_object* v_x_1886_, lean_object* v_x_1887_){
_start:
{
uint64_t v___y_1889_; lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_Meta_Grind_Origin_key(v_x_1887_);
if (lean_obj_tag(v___x_1892_) == 0)
{
uint64_t v___x_1893_; 
v___x_1893_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1889_ = v___x_1893_;
goto v___jp_1888_;
}
else
{
uint64_t v_hash_1894_; 
v_hash_1894_ = lean_ctor_get_uint64(v___x_1892_, sizeof(void*)*2);
lean_dec(v___x_1892_);
v___y_1889_ = v_hash_1894_;
goto v___jp_1888_;
}
v___jp_1888_:
{
size_t v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_uint64_to_usize(v___y_1889_);
v___x_1891_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_1886_, v___x_1890_, v_x_1887_);
return v___x_1891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg___boxed(lean_object* v_x_1895_, lean_object* v_x_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_x_1895_, v_x_1896_);
lean_dec_ref(v_x_1896_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(lean_object* v_keys_1898_, lean_object* v_vals_1899_, lean_object* v_i_1900_, lean_object* v_k_1901_){
_start:
{
lean_object* v___x_1902_; uint8_t v___x_1903_; 
v___x_1902_ = lean_array_get_size(v_keys_1898_);
v___x_1903_ = lean_nat_dec_lt(v_i_1900_, v___x_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; 
lean_dec(v_i_1900_);
v___x_1904_ = lean_box(0);
return v___x_1904_;
}
else
{
lean_object* v_k_x27_1905_; uint8_t v___x_1906_; 
v_k_x27_1905_ = lean_array_fget_borrowed(v_keys_1898_, v_i_1900_);
v___x_1906_ = lean_name_eq(v_k_1901_, v_k_x27_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_unsigned_to_nat(1u);
v___x_1908_ = lean_nat_add(v_i_1900_, v___x_1907_);
lean_dec(v_i_1900_);
v_i_1900_ = v___x_1908_;
goto _start;
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = lean_array_fget_borrowed(v_vals_1899_, v_i_1900_);
lean_dec(v_i_1900_);
lean_inc(v___x_1910_);
v___x_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
return v___x_1911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg___boxed(lean_object* v_keys_1912_, lean_object* v_vals_1913_, lean_object* v_i_1914_, lean_object* v_k_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_keys_1912_, v_vals_1913_, v_i_1914_, v_k_1915_);
lean_dec(v_k_1915_);
lean_dec_ref(v_vals_1913_);
lean_dec_ref(v_keys_1912_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(lean_object* v_x_1917_, size_t v_x_1918_, lean_object* v_x_1919_){
_start:
{
if (lean_obj_tag(v_x_1917_) == 0)
{
lean_object* v_es_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1941_; 
v_es_1920_ = lean_ctor_get(v_x_1917_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_x_1917_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1922_ = v_x_1917_;
v_isShared_1923_ = v_isSharedCheck_1941_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_es_1920_);
lean_dec(v_x_1917_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1941_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; size_t v___x_1925_; size_t v___x_1926_; size_t v___x_1927_; lean_object* v_j_1928_; lean_object* v___x_1929_; 
v___x_1924_ = lean_box(2);
v___x_1925_ = ((size_t)5ULL);
v___x_1926_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1);
v___x_1927_ = lean_usize_land(v_x_1918_, v___x_1926_);
v_j_1928_ = lean_usize_to_nat(v___x_1927_);
v___x_1929_ = lean_array_get(v___x_1924_, v_es_1920_, v_j_1928_);
lean_dec(v_j_1928_);
lean_dec_ref(v_es_1920_);
switch(lean_obj_tag(v___x_1929_))
{
case 0:
{
lean_object* v_key_1930_; lean_object* v_val_1931_; uint8_t v___x_1932_; 
v_key_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_key_1930_);
v_val_1931_ = lean_ctor_get(v___x_1929_, 1);
lean_inc(v_val_1931_);
lean_dec_ref(v___x_1929_);
v___x_1932_ = lean_name_eq(v_x_1919_, v_key_1930_);
lean_dec(v_key_1930_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; 
lean_dec(v_val_1931_);
lean_del_object(v___x_1922_);
v___x_1933_ = lean_box(0);
return v___x_1933_;
}
else
{
lean_object* v___x_1935_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 1);
lean_ctor_set(v___x_1922_, 0, v_val_1931_);
v___x_1935_ = v___x_1922_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_val_1931_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
case 1:
{
lean_object* v_node_1937_; size_t v___x_1938_; 
lean_del_object(v___x_1922_);
v_node_1937_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_node_1937_);
lean_dec_ref(v___x_1929_);
v___x_1938_ = lean_usize_shift_right(v_x_1918_, v___x_1925_);
v_x_1917_ = v_node_1937_;
v_x_1918_ = v___x_1938_;
goto _start;
}
default: 
{
lean_object* v___x_1940_; 
lean_del_object(v___x_1922_);
v___x_1940_ = lean_box(0);
return v___x_1940_;
}
}
}
}
else
{
lean_object* v_ks_1942_; lean_object* v_vs_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v_ks_1942_ = lean_ctor_get(v_x_1917_, 0);
lean_inc_ref(v_ks_1942_);
v_vs_1943_ = lean_ctor_get(v_x_1917_, 1);
lean_inc_ref(v_vs_1943_);
lean_dec_ref(v_x_1917_);
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_ks_1942_, v_vs_1943_, v___x_1944_, v_x_1919_);
lean_dec_ref(v_vs_1943_);
lean_dec_ref(v_ks_1942_);
return v___x_1945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg___boxed(lean_object* v_x_1946_, lean_object* v_x_1947_, lean_object* v_x_1948_){
_start:
{
size_t v_x_1588__boxed_1949_; lean_object* v_res_1950_; 
v_x_1588__boxed_1949_ = lean_unbox_usize(v_x_1947_);
lean_dec(v_x_1947_);
v_res_1950_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_1946_, v_x_1588__boxed_1949_, v_x_1948_);
lean_dec(v_x_1948_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(lean_object* v_x_1951_, lean_object* v_x_1952_){
_start:
{
uint64_t v___y_1954_; 
if (lean_obj_tag(v_x_1952_) == 0)
{
uint64_t v___x_1957_; 
v___x_1957_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1954_ = v___x_1957_;
goto v___jp_1953_;
}
else
{
uint64_t v_hash_1958_; 
v_hash_1958_ = lean_ctor_get_uint64(v_x_1952_, sizeof(void*)*2);
v___y_1954_ = v_hash_1958_;
goto v___jp_1953_;
}
v___jp_1953_:
{
size_t v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_uint64_to_usize(v___y_1954_);
v___x_1956_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_1951_, v___x_1955_, v_x_1952_);
return v___x_1956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg___boxed(lean_object* v_x_1959_, lean_object* v_x_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_x_1959_, v_x_1960_);
lean_dec(v_x_1960_);
return v_res_1961_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_Meta_Grind_instInhabitedTheorems_default(lean_box(0));
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0(lean_object* v_msg_1970_){
_start:
{
lean_object* v___f_1971_; lean_object* v___f_1972_; lean_object* v___f_1973_; lean_object* v___f_1974_; lean_object* v___f_1975_; lean_object* v___f_1976_; lean_object* v___f_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___f_1971_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0));
v___f_1972_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1));
v___f_1973_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2));
v___f_1974_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3));
v___f_1975_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4));
v___f_1976_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5));
v___f_1977_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6));
v___x_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___f_1971_);
lean_ctor_set(v___x_1978_, 1, v___f_1972_);
v___x_1979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
lean_ctor_set(v___x_1979_, 1, v___f_1973_);
lean_ctor_set(v___x_1979_, 2, v___f_1974_);
lean_ctor_set(v___x_1979_, 3, v___f_1975_);
lean_ctor_set(v___x_1979_, 4, v___f_1976_);
v___x_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
lean_ctor_set(v___x_1980_, 1, v___f_1977_);
v___x_1981_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7, &l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once, _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7);
v___x_1982_ = l_instInhabitedOfMonad___redArg(v___x_1980_, v___x_1981_);
v___x_1983_ = lean_panic_fn_borrowed(v___x_1982_, v_msg_1970_);
lean_dec(v___x_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(lean_object* v_xs_1984_, lean_object* v_v_1985_, lean_object* v_i_1986_){
_start:
{
lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = lean_array_get_size(v_xs_1984_);
v___x_1988_ = lean_nat_dec_lt(v_i_1986_, v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; 
lean_dec(v_i_1986_);
v___x_1989_ = lean_box(0);
return v___x_1989_;
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v___x_1990_ = lean_array_fget_borrowed(v_xs_1984_, v_i_1986_);
v___x_1991_ = l_Lean_Meta_Grind_Origin_key(v___x_1990_);
v___x_1992_ = l_Lean_Meta_Grind_Origin_key(v_v_1985_);
v___x_1993_ = lean_name_eq(v___x_1991_, v___x_1992_);
lean_dec(v___x_1992_);
lean_dec(v___x_1991_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = lean_unsigned_to_nat(1u);
v___x_1995_ = lean_nat_add(v_i_1986_, v___x_1994_);
lean_dec(v_i_1986_);
v_i_1986_ = v___x_1995_;
goto _start;
}
else
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1997_, 0, v_i_1986_);
return v___x_1997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13___boxed(lean_object* v_xs_1998_, lean_object* v_v_1999_, lean_object* v_i_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(v_xs_1998_, v_v_1999_, v_i_2000_);
lean_dec_ref(v_v_1999_);
lean_dec_ref(v_xs_1998_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(lean_object* v_xs_2002_, lean_object* v_v_2003_){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = lean_unsigned_to_nat(0u);
v___x_2005_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(v_xs_2002_, v_v_2003_, v___x_2004_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9___boxed(lean_object* v_xs_2006_, lean_object* v_v_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(v_xs_2006_, v_v_2007_);
lean_dec_ref(v_v_2007_);
lean_dec_ref(v_xs_2006_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(lean_object* v_x_2009_, size_t v_x_2010_, lean_object* v_x_2011_){
_start:
{
if (lean_obj_tag(v_x_2009_) == 0)
{
lean_object* v_es_2012_; lean_object* v___x_2013_; size_t v___x_2014_; size_t v___x_2015_; size_t v___x_2016_; lean_object* v_j_2017_; lean_object* v_entry_2018_; 
v_es_2012_ = lean_ctor_get(v_x_2009_, 0);
v___x_2013_ = lean_box(2);
v___x_2014_ = ((size_t)5ULL);
v___x_2015_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__1);
v___x_2016_ = lean_usize_land(v_x_2010_, v___x_2015_);
v_j_2017_ = lean_usize_to_nat(v___x_2016_);
v_entry_2018_ = lean_array_get(v___x_2013_, v_es_2012_, v_j_2017_);
switch(lean_obj_tag(v_entry_2018_))
{
case 0:
{
lean_object* v_key_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v_key_2019_ = lean_ctor_get(v_entry_2018_, 0);
lean_inc(v_key_2019_);
lean_dec_ref(v_entry_2018_);
v___x_2020_ = l_Lean_Meta_Grind_Origin_key(v_x_2011_);
v___x_2021_ = l_Lean_Meta_Grind_Origin_key(v_key_2019_);
lean_dec(v_key_2019_);
v___x_2022_ = lean_name_eq(v___x_2020_, v___x_2021_);
lean_dec(v___x_2021_);
lean_dec(v___x_2020_);
if (v___x_2022_ == 0)
{
lean_dec(v_j_2017_);
return v_x_2009_;
}
else
{
lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2030_; 
lean_inc_ref(v_es_2012_);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_x_2009_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v_x_2009_, 0);
lean_dec(v_unused_2031_);
v___x_2024_ = v_x_2009_;
v_isShared_2025_ = v_isSharedCheck_2030_;
goto v_resetjp_2023_;
}
else
{
lean_dec(v_x_2009_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2030_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2026_ = lean_array_set(v_es_2012_, v_j_2017_, v___x_2013_);
lean_dec(v_j_2017_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2026_);
v___x_2028_ = v___x_2024_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
case 1:
{
lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2065_; 
lean_inc_ref(v_es_2012_);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_x_2009_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; 
v_unused_2066_ = lean_ctor_get(v_x_2009_, 0);
lean_dec(v_unused_2066_);
v___x_2033_ = v_x_2009_;
v_isShared_2034_ = v_isSharedCheck_2065_;
goto v_resetjp_2032_;
}
else
{
lean_dec(v_x_2009_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2065_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v_node_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2064_; 
v_node_2035_ = lean_ctor_get(v_entry_2018_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_entry_2018_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2037_ = v_entry_2018_;
v_isShared_2038_ = v_isSharedCheck_2064_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_node_2035_);
lean_dec(v_entry_2018_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2064_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v_entries_2039_; size_t v___x_2040_; lean_object* v_newNode_2041_; lean_object* v___x_2042_; 
v_entries_2039_ = lean_array_set(v_es_2012_, v_j_2017_, v___x_2013_);
v___x_2040_ = lean_usize_shift_right(v_x_2010_, v___x_2014_);
v_newNode_2041_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_node_2035_, v___x_2040_, v_x_2011_);
lean_inc_ref(v_newNode_2041_);
v___x_2042_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2041_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v___x_2044_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v_newNode_2041_);
v___x_2044_ = v___x_2037_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_newNode_2041_);
v___x_2044_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2045_ = lean_array_set(v_entries_2039_, v_j_2017_, v___x_2044_);
lean_dec(v_j_2017_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2045_);
v___x_2047_ = v___x_2033_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
else
{
lean_object* v_val_2050_; lean_object* v_fst_2051_; lean_object* v_snd_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2063_; 
lean_dec_ref(v_newNode_2041_);
lean_del_object(v___x_2037_);
v_val_2050_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_val_2050_);
lean_dec_ref(v___x_2042_);
v_fst_2051_ = lean_ctor_get(v_val_2050_, 0);
v_snd_2052_ = lean_ctor_get(v_val_2050_, 1);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_val_2050_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2054_ = v_val_2050_;
v_isShared_2055_ = v_isSharedCheck_2063_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_snd_2052_);
lean_inc(v_fst_2051_);
lean_dec(v_val_2050_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2063_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_fst_2051_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_snd_2052_);
v___x_2057_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2058_ = lean_array_set(v_entries_2039_, v_j_2017_, v___x_2057_);
lean_dec(v_j_2017_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2058_);
v___x_2060_ = v___x_2033_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
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
}
}
}
default: 
{
lean_dec(v_j_2017_);
return v_x_2009_;
}
}
}
else
{
lean_object* v_ks_2067_; lean_object* v_vs_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2082_; 
v_ks_2067_ = lean_ctor_get(v_x_2009_, 0);
v_vs_2068_ = lean_ctor_get(v_x_2009_, 1);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_x_2009_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2070_ = v_x_2009_;
v_isShared_2071_ = v_isSharedCheck_2082_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_vs_2068_);
lean_inc(v_ks_2067_);
lean_dec(v_x_2009_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2082_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(v_ks_2067_, v_x_2011_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v___x_2074_; 
if (v_isShared_2071_ == 0)
{
v___x_2074_ = v___x_2070_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_ks_2067_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_vs_2068_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
else
{
lean_object* v_val_2076_; lean_object* v_keys_x27_2077_; lean_object* v_vals_x27_2078_; lean_object* v___x_2080_; 
v_val_2076_ = lean_ctor_get(v___x_2072_, 0);
lean_inc_n(v_val_2076_, 2);
lean_dec_ref(v___x_2072_);
v_keys_x27_2077_ = l_Array_eraseIdx___redArg(v_ks_2067_, v_val_2076_);
v_vals_x27_2078_ = l_Array_eraseIdx___redArg(v_vs_2068_, v_val_2076_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v_vals_x27_2078_);
lean_ctor_set(v___x_2070_, 0, v_keys_x27_2077_);
v___x_2080_ = v___x_2070_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_keys_x27_2077_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_vals_x27_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2083_, lean_object* v_x_2084_, lean_object* v_x_2085_){
_start:
{
size_t v_x_1750__boxed_2086_; lean_object* v_res_2087_; 
v_x_1750__boxed_2086_ = lean_unbox_usize(v_x_2084_);
lean_dec(v_x_2084_);
v_res_2087_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2083_, v_x_1750__boxed_2086_, v_x_2085_);
lean_dec_ref(v_x_2085_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(lean_object* v_x_2088_, lean_object* v_x_2089_){
_start:
{
uint64_t v___y_2091_; lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_Meta_Grind_Origin_key(v_x_2089_);
if (lean_obj_tag(v___x_2094_) == 0)
{
uint64_t v___x_2095_; 
v___x_2095_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_2091_ = v___x_2095_;
goto v___jp_2090_;
}
else
{
uint64_t v_hash_2096_; 
v_hash_2096_ = lean_ctor_get_uint64(v___x_2094_, sizeof(void*)*2);
lean_dec(v___x_2094_);
v___y_2091_ = v_hash_2096_;
goto v___jp_2090_;
}
v___jp_2090_:
{
size_t v_h_2092_; lean_object* v___x_2093_; 
v_h_2092_ = lean_uint64_to_usize(v___y_2091_);
v___x_2093_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2088_, v_h_2092_, v_x_2089_);
return v___x_2093_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg___boxed(lean_object* v_x_2097_, lean_object* v_x_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_x_2097_, v_x_2098_);
lean_dec_ref(v_x_2098_);
return v_res_2099_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2103_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2));
v___x_2104_ = lean_unsigned_to_nat(6u);
v___x_2105_ = lean_unsigned_to_nat(82u);
v___x_2106_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__1));
v___x_2107_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__0));
v___x_2108_ = l_mkPanicMessageWithDecl(v___x_2107_, v___x_2106_, v___x_2105_, v___x_2104_, v___x_2103_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0(lean_object* v_s_2109_, lean_object* v_thm_2110_){
_start:
{
lean_object* v_symbols_2114_; 
v_symbols_2114_ = lean_ctor_get(v_thm_2110_, 4);
lean_inc(v_symbols_2114_);
if (lean_obj_tag(v_symbols_2114_) == 1)
{
lean_object* v_head_2115_; 
v_head_2115_ = lean_ctor_get(v_symbols_2114_, 0);
lean_inc(v_head_2115_);
if (lean_obj_tag(v_head_2115_) == 2)
{
lean_object* v_levelParams_2116_; lean_object* v_proof_2117_; lean_object* v_numParams_2118_; lean_object* v_patterns_2119_; lean_object* v_origin_2120_; lean_object* v_kind_2121_; uint8_t v_minIndexable_2122_; lean_object* v_cnstrs_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2174_; 
v_levelParams_2116_ = lean_ctor_get(v_thm_2110_, 0);
v_proof_2117_ = lean_ctor_get(v_thm_2110_, 1);
v_numParams_2118_ = lean_ctor_get(v_thm_2110_, 2);
v_patterns_2119_ = lean_ctor_get(v_thm_2110_, 3);
v_origin_2120_ = lean_ctor_get(v_thm_2110_, 5);
v_kind_2121_ = lean_ctor_get(v_thm_2110_, 6);
v_minIndexable_2122_ = lean_ctor_get_uint8(v_thm_2110_, sizeof(void*)*8);
v_cnstrs_2123_ = lean_ctor_get(v_thm_2110_, 7);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_thm_2110_);
if (v_isSharedCheck_2174_ == 0)
{
lean_object* v_unused_2175_; 
v_unused_2175_ = lean_ctor_get(v_thm_2110_, 4);
lean_dec(v_unused_2175_);
v___x_2125_ = v_thm_2110_;
v_isShared_2126_ = v_isSharedCheck_2174_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_cnstrs_2123_);
lean_inc(v_kind_2121_);
lean_inc(v_origin_2120_);
lean_inc(v_patterns_2119_);
lean_inc(v_numParams_2118_);
lean_inc(v_proof_2117_);
lean_inc(v_levelParams_2116_);
lean_dec(v_thm_2110_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2174_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v_tail_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2172_; 
v_tail_2127_ = lean_ctor_get(v_symbols_2114_, 1);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_symbols_2114_);
if (v_isSharedCheck_2172_ == 0)
{
lean_object* v_unused_2173_; 
v_unused_2173_ = lean_ctor_get(v_symbols_2114_, 0);
lean_dec(v_unused_2173_);
v___x_2129_ = v_symbols_2114_;
v_isShared_2130_ = v_isSharedCheck_2172_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_tail_2127_);
lean_dec(v_symbols_2114_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2172_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_constName_2131_; lean_object* v_smap_2132_; lean_object* v_origins_2133_; lean_object* v_erased_2134_; lean_object* v_omap_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2171_; 
v_constName_2131_ = lean_ctor_get(v_head_2115_, 0);
lean_inc(v_constName_2131_);
lean_dec_ref(v_head_2115_);
v_smap_2132_ = lean_ctor_get(v_s_2109_, 0);
v_origins_2133_ = lean_ctor_get(v_s_2109_, 1);
v_erased_2134_ = lean_ctor_get(v_s_2109_, 2);
v_omap_2135_ = lean_ctor_get(v_s_2109_, 3);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_s_2109_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2137_ = v_s_2109_;
v_isShared_2138_ = v_isSharedCheck_2171_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_omap_2135_);
lean_inc(v_erased_2134_);
lean_inc(v_origins_2133_);
lean_inc(v_smap_2132_);
lean_dec(v_s_2109_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2171_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v_thm_2140_; 
lean_inc_ref(v_origin_2120_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 4, v_tail_2127_);
v_thm_2140_ = v___x_2125_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_levelParams_2116_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_proof_2117_);
lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_numParams_2118_);
lean_ctor_set(v_reuseFailAlloc_2170_, 3, v_patterns_2119_);
lean_ctor_set(v_reuseFailAlloc_2170_, 4, v_tail_2127_);
lean_ctor_set(v_reuseFailAlloc_2170_, 5, v_origin_2120_);
lean_ctor_set(v_reuseFailAlloc_2170_, 6, v_kind_2121_);
lean_ctor_set(v_reuseFailAlloc_2170_, 7, v_cnstrs_2123_);
lean_ctor_set_uint8(v_reuseFailAlloc_2170_, sizeof(void*)*8, v_minIndexable_2122_);
v_thm_2140_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2141_; lean_object* v_origins_2142_; lean_object* v_erased_2143_; lean_object* v___y_2145_; lean_object* v___x_2163_; 
v___x_2141_ = lean_box(0);
lean_inc_ref(v_origin_2120_);
v_origins_2142_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_origins_2133_, v_origin_2120_, v___x_2141_);
v_erased_2143_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_erased_2134_, v_origin_2120_);
lean_inc_ref(v_smap_2132_);
v___x_2163_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_smap_2132_, v_constName_2131_);
if (lean_obj_tag(v___x_2163_) == 1)
{
lean_object* v_val_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v_val_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_val_2164_);
lean_dec_ref(v___x_2163_);
lean_inc_ref(v_thm_2140_);
v___x_2165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2165_, 0, v_thm_2140_);
lean_ctor_set(v___x_2165_, 1, v_val_2164_);
v___x_2166_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2132_, v_constName_2131_, v___x_2165_);
v___y_2145_ = v___x_2166_;
goto v___jp_2144_;
}
else
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
lean_dec(v___x_2163_);
v___x_2167_ = lean_box(0);
lean_inc_ref(v_thm_2140_);
v___x_2168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2168_, 0, v_thm_2140_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2132_, v_constName_2131_, v___x_2168_);
v___y_2145_ = v___x_2169_;
goto v___jp_2144_;
}
v___jp_2144_:
{
lean_object* v___x_2146_; 
lean_inc_ref(v_omap_2135_);
v___x_2146_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_omap_2135_, v_origin_2120_);
if (lean_obj_tag(v___x_2146_) == 1)
{
lean_object* v_val_2147_; lean_object* v___x_2149_; 
v_val_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_val_2147_);
lean_dec_ref(v___x_2146_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 1, v_val_2147_);
lean_ctor_set(v___x_2129_, 0, v_thm_2140_);
v___x_2149_ = v___x_2129_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_thm_2140_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_val_2147_);
v___x_2149_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2150_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2135_, v_origin_2120_, v___x_2149_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 3, v___x_2150_);
lean_ctor_set(v___x_2137_, 2, v_erased_2143_);
lean_ctor_set(v___x_2137_, 1, v_origins_2142_);
lean_ctor_set(v___x_2137_, 0, v___y_2145_);
v___x_2152_ = v___x_2137_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___y_2145_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_origins_2142_);
lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_erased_2143_);
lean_ctor_set(v_reuseFailAlloc_2153_, 3, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2157_; 
lean_dec(v___x_2146_);
v___x_2155_ = lean_box(0);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 1, v___x_2155_);
lean_ctor_set(v___x_2129_, 0, v_thm_2140_);
v___x_2157_ = v___x_2129_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_thm_2140_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2158_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2135_, v_origin_2120_, v___x_2157_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 3, v___x_2158_);
lean_ctor_set(v___x_2137_, 2, v_erased_2143_);
lean_ctor_set(v___x_2137_, 1, v_origins_2142_);
lean_ctor_set(v___x_2137_, 0, v___y_2145_);
v___x_2160_ = v___x_2137_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___y_2145_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_origins_2142_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_erased_2143_);
lean_ctor_set(v_reuseFailAlloc_2161_, 3, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
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
lean_dec_ref(v_symbols_2114_);
lean_dec(v_head_2115_);
lean_dec_ref(v_thm_2110_);
lean_dec_ref(v_s_2109_);
goto v___jp_2111_;
}
}
else
{
lean_dec(v_symbols_2114_);
lean_dec_ref(v_thm_2110_);
lean_dec_ref(v_s_2109_);
goto v___jp_2111_;
}
v___jp_2111_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3, &l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3);
v___x_2113_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0(v___x_2112_);
return v___x_2113_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1_spec__6(lean_object* v_msg_2176_){
_start:
{
lean_object* v___f_2177_; lean_object* v___f_2178_; lean_object* v___f_2179_; lean_object* v___f_2180_; lean_object* v___f_2181_; lean_object* v___f_2182_; lean_object* v___f_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___f_2177_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0));
v___f_2178_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1));
v___f_2179_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2));
v___f_2180_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3));
v___f_2181_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4));
v___f_2182_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5));
v___f_2183_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6));
v___x_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___f_2177_);
lean_ctor_set(v___x_2184_, 1, v___f_2178_);
v___x_2185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
lean_ctor_set(v___x_2185_, 1, v___f_2179_);
lean_ctor_set(v___x_2185_, 2, v___f_2180_);
lean_ctor_set(v___x_2185_, 3, v___f_2181_);
lean_ctor_set(v___x_2185_, 4, v___f_2182_);
v___x_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
lean_ctor_set(v___x_2186_, 1, v___f_2183_);
v___x_2187_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7, &l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once, _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7);
v___x_2188_ = l_instInhabitedOfMonad___redArg(v___x_2186_, v___x_2187_);
v___x_2189_ = lean_panic_fn_borrowed(v___x_2188_, v_msg_2176_);
lean_dec(v___x_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1(lean_object* v_s_2190_, lean_object* v_thm_2191_){
_start:
{
lean_object* v_symbols_2195_; 
v_symbols_2195_ = lean_ctor_get(v_thm_2191_, 2);
lean_inc(v_symbols_2195_);
if (lean_obj_tag(v_symbols_2195_) == 1)
{
lean_object* v_head_2196_; 
v_head_2196_ = lean_ctor_get(v_symbols_2195_, 0);
lean_inc(v_head_2196_);
if (lean_obj_tag(v_head_2196_) == 2)
{
lean_object* v_levelParams_2197_; lean_object* v_proof_2198_; lean_object* v_origin_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2250_; 
v_levelParams_2197_ = lean_ctor_get(v_thm_2191_, 0);
v_proof_2198_ = lean_ctor_get(v_thm_2191_, 1);
v_origin_2199_ = lean_ctor_get(v_thm_2191_, 3);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_thm_2191_);
if (v_isSharedCheck_2250_ == 0)
{
lean_object* v_unused_2251_; 
v_unused_2251_ = lean_ctor_get(v_thm_2191_, 2);
lean_dec(v_unused_2251_);
v___x_2201_ = v_thm_2191_;
v_isShared_2202_ = v_isSharedCheck_2250_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_origin_2199_);
lean_inc(v_proof_2198_);
lean_inc(v_levelParams_2197_);
lean_dec(v_thm_2191_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2250_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v_tail_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2248_; 
v_tail_2203_ = lean_ctor_get(v_symbols_2195_, 1);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_symbols_2195_);
if (v_isSharedCheck_2248_ == 0)
{
lean_object* v_unused_2249_; 
v_unused_2249_ = lean_ctor_get(v_symbols_2195_, 0);
lean_dec(v_unused_2249_);
v___x_2205_ = v_symbols_2195_;
v_isShared_2206_ = v_isSharedCheck_2248_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_tail_2203_);
lean_dec(v_symbols_2195_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2248_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v_constName_2207_; lean_object* v_smap_2208_; lean_object* v_origins_2209_; lean_object* v_erased_2210_; lean_object* v_omap_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2247_; 
v_constName_2207_ = lean_ctor_get(v_head_2196_, 0);
lean_inc(v_constName_2207_);
lean_dec_ref(v_head_2196_);
v_smap_2208_ = lean_ctor_get(v_s_2190_, 0);
v_origins_2209_ = lean_ctor_get(v_s_2190_, 1);
v_erased_2210_ = lean_ctor_get(v_s_2190_, 2);
v_omap_2211_ = lean_ctor_get(v_s_2190_, 3);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_s_2190_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2213_ = v_s_2190_;
v_isShared_2214_ = v_isSharedCheck_2247_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_omap_2211_);
lean_inc(v_erased_2210_);
lean_inc(v_origins_2209_);
lean_inc(v_smap_2208_);
lean_dec(v_s_2190_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2247_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v_thm_2216_; 
lean_inc_ref(v_origin_2199_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 2, v_tail_2203_);
v_thm_2216_ = v___x_2201_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_levelParams_2197_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_proof_2198_);
lean_ctor_set(v_reuseFailAlloc_2246_, 2, v_tail_2203_);
lean_ctor_set(v_reuseFailAlloc_2246_, 3, v_origin_2199_);
v_thm_2216_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
lean_object* v___x_2217_; lean_object* v_origins_2218_; lean_object* v_erased_2219_; lean_object* v___y_2221_; lean_object* v___x_2239_; 
v___x_2217_ = lean_box(0);
lean_inc_ref(v_origin_2199_);
v_origins_2218_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_origins_2209_, v_origin_2199_, v___x_2217_);
v_erased_2219_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_erased_2210_, v_origin_2199_);
lean_inc_ref(v_smap_2208_);
v___x_2239_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_smap_2208_, v_constName_2207_);
if (lean_obj_tag(v___x_2239_) == 1)
{
lean_object* v_val_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v_val_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_val_2240_);
lean_dec_ref(v___x_2239_);
lean_inc_ref(v_thm_2216_);
v___x_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2241_, 0, v_thm_2216_);
lean_ctor_set(v___x_2241_, 1, v_val_2240_);
v___x_2242_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2208_, v_constName_2207_, v___x_2241_);
v___y_2221_ = v___x_2242_;
goto v___jp_2220_;
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
lean_dec(v___x_2239_);
v___x_2243_ = lean_box(0);
lean_inc_ref(v_thm_2216_);
v___x_2244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2244_, 0, v_thm_2216_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2208_, v_constName_2207_, v___x_2244_);
v___y_2221_ = v___x_2245_;
goto v___jp_2220_;
}
v___jp_2220_:
{
lean_object* v___x_2222_; 
lean_inc_ref(v_omap_2211_);
v___x_2222_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_omap_2211_, v_origin_2199_);
if (lean_obj_tag(v___x_2222_) == 1)
{
lean_object* v_val_2223_; lean_object* v___x_2225_; 
v_val_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_val_2223_);
lean_dec_ref(v___x_2222_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 1, v_val_2223_);
lean_ctor_set(v___x_2205_, 0, v_thm_2216_);
v___x_2225_ = v___x_2205_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_thm_2216_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_val_2223_);
v___x_2225_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2226_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2211_, v_origin_2199_, v___x_2225_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 3, v___x_2226_);
lean_ctor_set(v___x_2213_, 2, v_erased_2219_);
lean_ctor_set(v___x_2213_, 1, v_origins_2218_);
lean_ctor_set(v___x_2213_, 0, v___y_2221_);
v___x_2228_ = v___x_2213_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___y_2221_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_origins_2218_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_erased_2219_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
lean_dec(v___x_2222_);
v___x_2231_ = lean_box(0);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 1, v___x_2231_);
lean_ctor_set(v___x_2205_, 0, v_thm_2216_);
v___x_2233_ = v___x_2205_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_thm_2216_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2234_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2211_, v_origin_2199_, v___x_2233_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 3, v___x_2234_);
lean_ctor_set(v___x_2213_, 2, v_erased_2219_);
lean_ctor_set(v___x_2213_, 1, v_origins_2218_);
lean_ctor_set(v___x_2213_, 0, v___y_2221_);
v___x_2236_ = v___x_2213_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___y_2221_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_origins_2218_);
lean_ctor_set(v_reuseFailAlloc_2237_, 2, v_erased_2219_);
lean_ctor_set(v_reuseFailAlloc_2237_, 3, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
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
lean_dec_ref(v_symbols_2195_);
lean_dec(v_head_2196_);
lean_dec_ref(v_thm_2191_);
lean_dec_ref(v_s_2190_);
goto v___jp_2192_;
}
}
else
{
lean_dec(v_symbols_2195_);
lean_dec_ref(v_thm_2191_);
lean_dec_ref(v_s_2190_);
goto v___jp_2192_;
}
v___jp_2192_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3, &l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3);
v___x_2194_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1_spec__6(v___x_2193_);
return v___x_2194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionState_addEntry(lean_object* v_s_2252_, lean_object* v_e_2253_){
_start:
{
switch(lean_obj_tag(v_e_2253_))
{
case 0:
{
lean_object* v_declName_2254_; lean_object* v_casesTypes_2255_; lean_object* v_extThms_2256_; lean_object* v_funCC_2257_; lean_object* v_ematch_2258_; lean_object* v_inj_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2268_; 
v_declName_2254_ = lean_ctor_get(v_e_2253_, 0);
lean_inc(v_declName_2254_);
lean_dec_ref(v_e_2253_);
v_casesTypes_2255_ = lean_ctor_get(v_s_2252_, 0);
v_extThms_2256_ = lean_ctor_get(v_s_2252_, 1);
v_funCC_2257_ = lean_ctor_get(v_s_2252_, 2);
v_ematch_2258_ = lean_ctor_get(v_s_2252_, 3);
v_inj_2259_ = lean_ctor_get(v_s_2252_, 4);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_s_2252_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2261_ = v_s_2252_;
v_isShared_2262_ = v_isSharedCheck_2268_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_inj_2259_);
lean_inc(v_ematch_2258_);
lean_inc(v_funCC_2257_);
lean_inc(v_extThms_2256_);
lean_inc(v_casesTypes_2255_);
lean_dec(v_s_2252_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2268_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2263_ = lean_box(0);
v___x_2264_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_extThms_2256_, v_declName_2254_, v___x_2263_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 1, v___x_2264_);
v___x_2266_ = v___x_2261_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_casesTypes_2255_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2264_);
lean_ctor_set(v_reuseFailAlloc_2267_, 2, v_funCC_2257_);
lean_ctor_set(v_reuseFailAlloc_2267_, 3, v_ematch_2258_);
lean_ctor_set(v_reuseFailAlloc_2267_, 4, v_inj_2259_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
case 1:
{
lean_object* v_declName_2269_; lean_object* v_casesTypes_2270_; lean_object* v_extThms_2271_; lean_object* v_funCC_2272_; lean_object* v_ematch_2273_; lean_object* v_inj_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2282_; 
v_declName_2269_ = lean_ctor_get(v_e_2253_, 0);
lean_inc(v_declName_2269_);
lean_dec_ref(v_e_2253_);
v_casesTypes_2270_ = lean_ctor_get(v_s_2252_, 0);
v_extThms_2271_ = lean_ctor_get(v_s_2252_, 1);
v_funCC_2272_ = lean_ctor_get(v_s_2252_, 2);
v_ematch_2273_ = lean_ctor_get(v_s_2252_, 3);
v_inj_2274_ = lean_ctor_get(v_s_2252_, 4);
v_isSharedCheck_2282_ = !lean_is_exclusive(v_s_2252_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2276_ = v_s_2252_;
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_inj_2274_);
lean_inc(v_ematch_2273_);
lean_inc(v_funCC_2272_);
lean_inc(v_extThms_2271_);
lean_inc(v_casesTypes_2270_);
lean_dec(v_s_2252_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2282_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v___x_2280_; 
v___x_2278_ = l_Lean_NameSet_insert(v_funCC_2272_, v_declName_2269_);
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 2, v___x_2278_);
v___x_2280_ = v___x_2276_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_casesTypes_2270_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_extThms_2271_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v___x_2278_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v_ematch_2273_);
lean_ctor_set(v_reuseFailAlloc_2281_, 4, v_inj_2274_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
case 2:
{
lean_object* v_declName_2283_; uint8_t v_eager_2284_; lean_object* v_casesTypes_2285_; lean_object* v_extThms_2286_; lean_object* v_funCC_2287_; lean_object* v_ematch_2288_; lean_object* v_inj_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2298_; 
v_declName_2283_ = lean_ctor_get(v_e_2253_, 0);
lean_inc(v_declName_2283_);
v_eager_2284_ = lean_ctor_get_uint8(v_e_2253_, sizeof(void*)*1);
lean_dec_ref(v_e_2253_);
v_casesTypes_2285_ = lean_ctor_get(v_s_2252_, 0);
v_extThms_2286_ = lean_ctor_get(v_s_2252_, 1);
v_funCC_2287_ = lean_ctor_get(v_s_2252_, 2);
v_ematch_2288_ = lean_ctor_get(v_s_2252_, 3);
v_inj_2289_ = lean_ctor_get(v_s_2252_, 4);
v_isSharedCheck_2298_ = !lean_is_exclusive(v_s_2252_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2291_ = v_s_2252_;
v_isShared_2292_ = v_isSharedCheck_2298_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_inj_2289_);
lean_inc(v_ematch_2288_);
lean_inc(v_funCC_2287_);
lean_inc(v_extThms_2286_);
lean_inc(v_casesTypes_2285_);
lean_dec(v_s_2252_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2298_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2296_; 
v___x_2293_ = lean_box(v_eager_2284_);
v___x_2294_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_casesTypes_2285_, v_declName_2283_, v___x_2293_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2294_);
v___x_2296_ = v___x_2291_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v_extThms_2286_);
lean_ctor_set(v_reuseFailAlloc_2297_, 2, v_funCC_2287_);
lean_ctor_set(v_reuseFailAlloc_2297_, 3, v_ematch_2288_);
lean_ctor_set(v_reuseFailAlloc_2297_, 4, v_inj_2289_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
case 3:
{
lean_object* v_thm_2299_; lean_object* v_casesTypes_2300_; lean_object* v_extThms_2301_; lean_object* v_funCC_2302_; lean_object* v_ematch_2303_; lean_object* v_inj_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2312_; 
v_thm_2299_ = lean_ctor_get(v_e_2253_, 0);
lean_inc_ref(v_thm_2299_);
lean_dec_ref(v_e_2253_);
v_casesTypes_2300_ = lean_ctor_get(v_s_2252_, 0);
v_extThms_2301_ = lean_ctor_get(v_s_2252_, 1);
v_funCC_2302_ = lean_ctor_get(v_s_2252_, 2);
v_ematch_2303_ = lean_ctor_get(v_s_2252_, 3);
v_inj_2304_ = lean_ctor_get(v_s_2252_, 4);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_s_2252_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2306_ = v_s_2252_;
v_isShared_2307_ = v_isSharedCheck_2312_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_inj_2304_);
lean_inc(v_ematch_2303_);
lean_inc(v_funCC_2302_);
lean_inc(v_extThms_2301_);
lean_inc(v_casesTypes_2300_);
lean_dec(v_s_2252_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2312_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; lean_object* v___x_2310_; 
v___x_2308_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0(v_ematch_2303_, v_thm_2299_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 3, v___x_2308_);
v___x_2310_ = v___x_2306_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_casesTypes_2300_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_extThms_2301_);
lean_ctor_set(v_reuseFailAlloc_2311_, 2, v_funCC_2302_);
lean_ctor_set(v_reuseFailAlloc_2311_, 3, v___x_2308_);
lean_ctor_set(v_reuseFailAlloc_2311_, 4, v_inj_2304_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
default: 
{
lean_object* v_thm_2313_; lean_object* v_casesTypes_2314_; lean_object* v_extThms_2315_; lean_object* v_funCC_2316_; lean_object* v_ematch_2317_; lean_object* v_inj_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2326_; 
v_thm_2313_ = lean_ctor_get(v_e_2253_, 0);
lean_inc_ref(v_thm_2313_);
lean_dec_ref(v_e_2253_);
v_casesTypes_2314_ = lean_ctor_get(v_s_2252_, 0);
v_extThms_2315_ = lean_ctor_get(v_s_2252_, 1);
v_funCC_2316_ = lean_ctor_get(v_s_2252_, 2);
v_ematch_2317_ = lean_ctor_get(v_s_2252_, 3);
v_inj_2318_ = lean_ctor_get(v_s_2252_, 4);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_s_2252_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2320_ = v_s_2252_;
v_isShared_2321_ = v_isSharedCheck_2326_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_inj_2318_);
lean_inc(v_ematch_2317_);
lean_inc(v_funCC_2316_);
lean_inc(v_extThms_2315_);
lean_inc(v_casesTypes_2314_);
lean_dec(v_s_2252_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2326_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2324_; 
v___x_2322_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1(v_inj_2318_, v_thm_2313_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 4, v___x_2322_);
v___x_2324_ = v___x_2320_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_casesTypes_2314_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_extThms_2315_);
lean_ctor_set(v_reuseFailAlloc_2325_, 2, v_funCC_2316_);
lean_ctor_set(v_reuseFailAlloc_2325_, 3, v_ematch_2317_);
lean_ctor_set(v_reuseFailAlloc_2325_, 4, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1(lean_object* v_00_u03b2_2327_, lean_object* v_x_2328_, lean_object* v_x_2329_, lean_object* v_x_2330_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_x_2328_, v_x_2329_, v_x_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2(lean_object* v_00_u03b2_2332_, lean_object* v_x_2333_, lean_object* v_x_2334_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_x_2333_, v_x_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2336_, lean_object* v_x_2337_, lean_object* v_x_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2(v_00_u03b2_2336_, v_x_2337_, v_x_2338_);
lean_dec_ref(v_x_2338_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3(lean_object* v_00_u03b2_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_x_2341_, v_x_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3(v_00_u03b2_2344_, v_x_2345_, v_x_2346_);
lean_dec_ref(v_x_2346_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4(lean_object* v_00_u03b2_2348_, lean_object* v_x_2349_, lean_object* v_x_2350_){
_start:
{
lean_object* v___x_2351_; 
v___x_2351_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_x_2349_, v_x_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___boxed(lean_object* v_00_u03b2_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4(v_00_u03b2_2352_, v_x_2353_, v_x_2354_);
lean_dec(v_x_2354_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2356_, lean_object* v_x_2357_, size_t v_x_2358_, size_t v_x_2359_, lean_object* v_x_2360_, lean_object* v_x_2361_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_2357_, v_x_2358_, v_x_2359_, v_x_2360_, v_x_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2363_, lean_object* v_x_2364_, lean_object* v_x_2365_, lean_object* v_x_2366_, lean_object* v_x_2367_, lean_object* v_x_2368_){
_start:
{
size_t v_x_2326__boxed_2369_; size_t v_x_2327__boxed_2370_; lean_object* v_res_2371_; 
v_x_2326__boxed_2369_ = lean_unbox_usize(v_x_2365_);
lean_dec(v_x_2365_);
v_x_2327__boxed_2370_ = lean_unbox_usize(v_x_2366_);
lean_dec(v_x_2366_);
v_res_2371_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(v_00_u03b2_2363_, v_x_2364_, v_x_2326__boxed_2369_, v_x_2327__boxed_2370_, v_x_2367_, v_x_2368_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2372_, lean_object* v_x_2373_, size_t v_x_2374_, lean_object* v_x_2375_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2373_, v_x_2374_, v_x_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2377_, lean_object* v_x_2378_, lean_object* v_x_2379_, lean_object* v_x_2380_){
_start:
{
size_t v_x_2343__boxed_2381_; lean_object* v_res_2382_; 
v_x_2343__boxed_2381_ = lean_unbox_usize(v_x_2379_);
lean_dec(v_x_2379_);
v_res_2382_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(v_00_u03b2_2377_, v_x_2378_, v_x_2343__boxed_2381_, v_x_2380_);
lean_dec_ref(v_x_2380_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(lean_object* v_00_u03b2_2383_, lean_object* v_x_2384_, size_t v_x_2385_, lean_object* v_x_2386_){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_2384_, v_x_2385_, v_x_2386_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2388_, lean_object* v_x_2389_, lean_object* v_x_2390_, lean_object* v_x_2391_){
_start:
{
size_t v_x_2354__boxed_2392_; lean_object* v_res_2393_; 
v_x_2354__boxed_2392_ = lean_unbox_usize(v_x_2390_);
lean_dec(v_x_2390_);
v_res_2393_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(v_00_u03b2_2388_, v_x_2389_, v_x_2354__boxed_2392_, v_x_2391_);
lean_dec_ref(v_x_2391_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(lean_object* v_00_u03b2_2394_, lean_object* v_x_2395_, size_t v_x_2396_, lean_object* v_x_2397_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_2395_, v_x_2396_, v_x_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2399_, lean_object* v_x_2400_, lean_object* v_x_2401_, lean_object* v_x_2402_){
_start:
{
size_t v_x_2365__boxed_2403_; lean_object* v_res_2404_; 
v_x_2365__boxed_2403_ = lean_unbox_usize(v_x_2401_);
lean_dec(v_x_2401_);
v_res_2404_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(v_00_u03b2_2399_, v_x_2400_, v_x_2365__boxed_2403_, v_x_2402_);
lean_dec(v_x_2402_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2405_, lean_object* v_n_2406_, lean_object* v_k_2407_, lean_object* v_v_2408_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(v_n_2406_, v_k_2407_, v_v_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2410_, size_t v_depth_2411_, lean_object* v_keys_2412_, lean_object* v_vals_2413_, lean_object* v_heq_2414_, lean_object* v_i_2415_, lean_object* v_entries_2416_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_depth_2411_, v_keys_2412_, v_vals_2413_, v_i_2415_, v_entries_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2418_, lean_object* v_depth_2419_, lean_object* v_keys_2420_, lean_object* v_vals_2421_, lean_object* v_heq_2422_, lean_object* v_i_2423_, lean_object* v_entries_2424_){
_start:
{
size_t v_depth_boxed_2425_; lean_object* v_res_2426_; 
v_depth_boxed_2425_ = lean_unbox_usize(v_depth_2419_);
lean_dec(v_depth_2419_);
v_res_2426_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(v_00_u03b2_2418_, v_depth_boxed_2425_, v_keys_2420_, v_vals_2421_, v_heq_2422_, v_i_2423_, v_entries_2424_);
lean_dec_ref(v_vals_2421_);
lean_dec_ref(v_keys_2420_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12(lean_object* v_00_u03b2_2427_, lean_object* v_keys_2428_, lean_object* v_vals_2429_, lean_object* v_heq_2430_, lean_object* v_i_2431_, lean_object* v_k_2432_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_keys_2428_, v_vals_2429_, v_i_2431_, v_k_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___boxed(lean_object* v_00_u03b2_2434_, lean_object* v_keys_2435_, lean_object* v_vals_2436_, lean_object* v_heq_2437_, lean_object* v_i_2438_, lean_object* v_k_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12(v_00_u03b2_2434_, v_keys_2435_, v_vals_2436_, v_heq_2437_, v_i_2438_, v_k_2439_);
lean_dec_ref(v_k_2439_);
lean_dec_ref(v_vals_2436_);
lean_dec_ref(v_keys_2435_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15(lean_object* v_00_u03b2_2441_, lean_object* v_keys_2442_, lean_object* v_vals_2443_, lean_object* v_heq_2444_, lean_object* v_i_2445_, lean_object* v_k_2446_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_keys_2442_, v_vals_2443_, v_i_2445_, v_k_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___boxed(lean_object* v_00_u03b2_2448_, lean_object* v_keys_2449_, lean_object* v_vals_2450_, lean_object* v_heq_2451_, lean_object* v_i_2452_, lean_object* v_k_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15(v_00_u03b2_2448_, v_keys_2449_, v_vals_2450_, v_heq_2451_, v_i_2452_, v_k_2453_);
lean_dec(v_k_2453_);
lean_dec_ref(v_vals_2450_);
lean_dec_ref(v_keys_2449_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_2455_, lean_object* v_x_2456_, lean_object* v_x_2457_, lean_object* v_x_2458_, lean_object* v_x_2459_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(v_x_2456_, v_x_2457_, v_x_2458_, v_x_2459_);
return v___x_2460_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__10));
v___x_2488_ = l_Lean_mkAtom(v___x_2487_);
return v___x_2488_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2489_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__12, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__12_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__12);
v___x_2490_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2491_ = lean_array_push(v___x_2490_, v___x_2489_);
return v___x_2491_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__17));
v___x_2501_ = l_Lean_mkAtom(v___x_2500_);
return v___x_2501_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__18, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__18_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__18);
v___x_2503_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2504_ = lean_array_push(v___x_2503_, v___x_2502_);
return v___x_2504_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__20(void){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2505_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__19, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__19_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__19);
v___x_2506_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__16));
v___x_2507_ = lean_box(2);
v___x_2508_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
lean_ctor_set(v___x_2508_, 1, v___x_2506_);
lean_ctor_set(v___x_2508_, 2, v___x_2505_);
return v___x_2508_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__21(void){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2509_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__20, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__20_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__20);
v___x_2510_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__13, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__13_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__13);
v___x_2511_ = lean_array_push(v___x_2510_, v___x_2509_);
return v___x_2511_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__22(void){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2512_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__21, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__21_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__21);
v___x_2513_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__11));
v___x_2514_ = lean_box(2);
v___x_2515_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
lean_ctor_set(v___x_2515_, 1, v___x_2513_);
lean_ctor_set(v___x_2515_, 2, v___x_2512_);
return v___x_2515_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2516_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__22, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__22_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__22);
v___x_2517_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2518_ = lean_array_push(v___x_2517_, v___x_2516_);
return v___x_2518_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2519_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__23, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__23_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__23);
v___x_2520_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__9));
v___x_2521_ = lean_box(2);
v___x_2522_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
lean_ctor_set(v___x_2522_, 1, v___x_2520_);
lean_ctor_set(v___x_2522_, 2, v___x_2519_);
return v___x_2522_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__25(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__24, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__24_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__24);
v___x_2524_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2525_ = lean_array_push(v___x_2524_, v___x_2523_);
return v___x_2525_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__26(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2526_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__25, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__25_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__25);
v___x_2527_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__7));
v___x_2528_ = lean_box(2);
v___x_2529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
lean_ctor_set(v___x_2529_, 1, v___x_2527_);
lean_ctor_set(v___x_2529_, 2, v___x_2526_);
return v___x_2529_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__27(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__26, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__26_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__26);
v___x_2531_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2532_ = lean_array_push(v___x_2531_, v___x_2530_);
return v___x_2532_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__28(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2533_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__27, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__27_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__27);
v___x_2534_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__4));
v___x_2535_ = lean_box(2);
v___x_2536_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2535_);
lean_ctor_set(v___x_2536_, 1, v___x_2534_);
lean_ctor_set(v___x_2536_, 2, v___x_2533_);
return v___x_2536_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1(void){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__28, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__28_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__28);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(lean_object* v_msg_2538_){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = lean_box(0);
v___x_2540_ = lean_panic_fn_borrowed(v___x_2539_, v_msg_2538_);
return v___x_2540_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2543_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2));
v___x_2544_ = lean_unsigned_to_nat(17u);
v___x_2545_ = lean_unsigned_to_nat(203u);
v___x_2546_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___lam__0___closed__1));
v___x_2547_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___lam__0___closed__0));
v___x_2548_ = l_mkPanicMessageWithDecl(v___x_2547_, v___x_2546_, v___x_2545_, v___x_2544_, v___x_2543_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__0(uint8_t v_lvl_2549_, lean_object* v_e_2550_){
_start:
{
uint8_t v___y_2552_; lean_object* v___y_2556_; 
switch(lean_obj_tag(v_e_2550_))
{
case 3:
{
lean_object* v_thm_2561_; lean_object* v_origin_2562_; 
v_thm_2561_ = lean_ctor_get(v_e_2550_, 0);
v_origin_2562_ = lean_ctor_get(v_thm_2561_, 5);
if (lean_obj_tag(v_origin_2562_) == 0)
{
lean_object* v_declName_2563_; 
v_declName_2563_ = lean_ctor_get(v_origin_2562_, 0);
lean_inc(v_declName_2563_);
v___y_2556_ = v_declName_2563_;
goto v___jp_2555_;
}
else
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2564_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___lam__0___closed__2, &l_Lean_Meta_Grind_mkExtension___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2);
v___x_2565_ = l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(v___x_2564_);
v___y_2556_ = v___x_2565_;
goto v___jp_2555_;
}
}
case 4:
{
lean_object* v_thm_2566_; lean_object* v_origin_2567_; 
v_thm_2566_ = lean_ctor_get(v_e_2550_, 0);
v_origin_2567_ = lean_ctor_get(v_thm_2566_, 3);
if (lean_obj_tag(v_origin_2567_) == 0)
{
lean_object* v_declName_2568_; 
v_declName_2568_ = lean_ctor_get(v_origin_2567_, 0);
lean_inc(v_declName_2568_);
v___y_2556_ = v_declName_2568_;
goto v___jp_2555_;
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___lam__0___closed__2, &l_Lean_Meta_Grind_mkExtension___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2);
v___x_2570_ = l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(v___x_2569_);
v___y_2556_ = v___x_2570_;
goto v___jp_2555_;
}
}
default: 
{
lean_object* v_declName_2571_; 
v_declName_2571_ = lean_ctor_get(v_e_2550_, 0);
lean_inc(v_declName_2571_);
v___y_2556_ = v_declName_2571_;
goto v___jp_2555_;
}
}
v___jp_2551_:
{
if (v___y_2552_ == 0)
{
lean_object* v___x_2553_; 
lean_dec_ref(v_e_2550_);
v___x_2553_ = lean_box(0);
return v___x_2553_;
}
else
{
lean_object* v___x_2554_; 
v___x_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2554_, 0, v_e_2550_);
return v___x_2554_;
}
}
v___jp_2555_:
{
uint8_t v___x_2557_; uint8_t v___x_2558_; 
v___x_2557_ = 2;
v___x_2558_ = l_Lean_instDecidableEqOLeanLevel(v_lvl_2549_, v___x_2557_);
if (v___x_2558_ == 0)
{
uint8_t v___x_2559_; 
v___x_2559_ = l_Lean_isPrivateName(v___y_2556_);
lean_dec(v___y_2556_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2560_, 0, v_e_2550_);
return v___x_2560_;
}
else
{
v___y_2552_ = v___x_2558_;
goto v___jp_2551_;
}
}
else
{
lean_dec(v___y_2556_);
v___y_2552_ = v___x_2558_;
goto v___jp_2551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__0___boxed(lean_object* v_lvl_2572_, lean_object* v_e_2573_){
_start:
{
uint8_t v_lvl_boxed_2574_; lean_object* v_res_2575_; 
v_lvl_boxed_2574_ = lean_unbox(v_lvl_2572_);
v_res_2575_ = l_Lean_Meta_Grind_mkExtension___lam__0(v_lvl_boxed_2574_, v_e_2573_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__1(lean_object* v___y_2576_){
_start:
{
lean_inc_ref(v___y_2576_);
return v___y_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__1___boxed(lean_object* v___y_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_Meta_Grind_mkExtension___lam__1(v___y_2577_);
lean_dec_ref(v___y_2577_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension(lean_object* v_name_2582_){
_start:
{
lean_object* v___f_2584_; lean_object* v___f_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___f_2584_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__0));
v___f_2585_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__1));
v___x_2586_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__2));
v___x_2587_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2);
v___x_2588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2588_, 0, v_name_2582_);
lean_ctor_set(v___x_2588_, 1, v___x_2586_);
lean_ctor_set(v___x_2588_, 2, v___x_2587_);
lean_ctor_set(v___x_2588_, 3, v___f_2585_);
lean_ctor_set(v___x_2588_, 4, v___f_2584_);
v___x_2589_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___boxed(lean_object* v_name_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_Meta_Grind_mkExtension(v_name_2590_);
return v_res_2592_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2593_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0);
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2596_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1);
v___x_2597_ = lean_unsigned_to_nat(0u);
v___x_2598_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
lean_ctor_set(v___x_2598_, 2, v___x_2597_);
lean_ctor_set(v___x_2598_, 3, v___x_2597_);
lean_ctor_set(v___x_2598_, 4, v___x_2596_);
lean_ctor_set(v___x_2598_, 5, v___x_2596_);
lean_ctor_set(v___x_2598_, 6, v___x_2596_);
lean_ctor_set(v___x_2598_, 7, v___x_2596_);
lean_ctor_set(v___x_2598_, 8, v___x_2596_);
lean_ctor_set(v___x_2598_, 9, v___x_2596_);
return v___x_2598_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = lean_unsigned_to_nat(32u);
v___x_2600_ = lean_mk_empty_array_with_capacity(v___x_2599_);
v___x_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
return v___x_2601_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2602_ = ((size_t)5ULL);
v___x_2603_ = lean_unsigned_to_nat(0u);
v___x_2604_ = lean_unsigned_to_nat(32u);
v___x_2605_ = lean_mk_empty_array_with_capacity(v___x_2604_);
v___x_2606_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3);
v___x_2607_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
lean_ctor_set(v___x_2607_, 1, v___x_2605_);
lean_ctor_set(v___x_2607_, 2, v___x_2603_);
lean_ctor_set(v___x_2607_, 3, v___x_2603_);
lean_ctor_set_usize(v___x_2607_, 4, v___x_2602_);
return v___x_2607_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2608_ = lean_box(1);
v___x_2609_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4);
v___x_2610_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1);
v___x_2611_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
lean_ctor_set(v___x_2611_, 1, v___x_2609_);
lean_ctor_set(v___x_2611_, 2, v___x_2608_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(lean_object* v_msgData_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v___x_2616_; lean_object* v_env_2617_; lean_object* v_options_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2616_ = lean_st_ref_get(v___y_2614_);
v_env_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc_ref(v_env_2617_);
lean_dec(v___x_2616_);
v_options_2618_ = lean_ctor_get(v___y_2613_, 2);
v___x_2619_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2);
v___x_2620_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2618_);
v___x_2621_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2621_, 0, v_env_2617_);
lean_ctor_set(v___x_2621_, 1, v___x_2619_);
lean_ctor_set(v___x_2621_, 2, v___x_2620_);
lean_ctor_set(v___x_2621_, 3, v_options_2618_);
v___x_2622_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
lean_ctor_set(v___x_2622_, 1, v_msgData_2612_);
v___x_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___boxed(lean_object* v_msgData_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(v_msgData_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(lean_object* v_msg_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_ref_2633_; lean_object* v___x_2634_; lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2643_; 
v_ref_2633_ = lean_ctor_get(v___y_2630_, 5);
v___x_2634_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(v_msg_2629_, v___y_2630_, v___y_2631_);
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2637_ = v___x_2634_;
v_isShared_2638_ = v_isSharedCheck_2643_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2643_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2639_; lean_object* v___x_2641_; 
lean_inc(v_ref_2633_);
v___x_2639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2639_, 0, v_ref_2633_);
lean_ctor_set(v___x_2639_, 1, v_a_2635_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set_tag(v___x_2637_, 1);
lean_ctor_set(v___x_2637_, 0, v___x_2639_);
v___x_2641_ = v___x_2637_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg___boxed(lean_object* v_msg_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v_msg_2644_, v___y_2645_, v___y_2646_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
return v_res_2648_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = ((lean_object*)(l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__0));
v___x_2651_ = l_Lean_stringToMessageData(v___x_2650_);
return v___x_2651_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = ((lean_object*)(l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__2));
v___x_2654_ = l_Lean_stringToMessageData(v___x_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object* v_declName_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v___x_2659_; uint8_t v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2659_ = lean_obj_once(&l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1, &l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1);
v___x_2660_ = 0;
v___x_2661_ = l_Lean_MessageData_ofConstName(v_declName_2655_, v___x_2660_);
v___x_2662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2659_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
v___x_2663_ = lean_obj_once(&l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3, &l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3_once, _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3);
v___x_2664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2662_);
lean_ctor_set(v___x_2664_, 1, v___x_2663_);
v___x_2665_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v___x_2664_, v_a_2656_, v_a_2657_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___boxed(lean_object* v_declName_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2666_, v_a_2667_, v_a_2668_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(lean_object* v_00_u03b1_2671_, lean_object* v_declName_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2672_, v_a_2673_, v_a_2674_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___boxed(lean_object* v_00_u03b1_2677_, lean_object* v_declName_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(v_00_u03b1_2677_, v_declName_2678_, v_a_2679_, v_a_2680_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(lean_object* v_00_u03b1_2683_, lean_object* v_msg_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v_msg_2684_, v___y_2685_, v___y_2686_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___boxed(lean_object* v_00_u03b1_2689_, lean_object* v_msg_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(v_00_u03b1_2689_, v_msg_2690_, v___y_2691_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
return v_res_2694_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Theorems(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Extension(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedCasesTypes_default = _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedCasesTypes_default);
l_Lean_Meta_Grind_instInhabitedCasesTypes = _init_l_Lean_Meta_Grind_instInhabitedCasesTypes();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedCasesTypes);
l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default = _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default);
l_Lean_Meta_Grind_instInhabitedSymbolPriorities = _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedSymbolPriorities);
l_Lean_Meta_Grind_instInhabitedCnstrRHS_default = _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default);
l_Lean_Meta_Grind_instInhabitedCnstrRHS = _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedCnstrRHS);
l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default = _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default);
l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint = _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint);
l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default = _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default);
l_Lean_Meta_Grind_instInhabitedEMatchTheorem = _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedEMatchTheorem);
l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default = _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default);
l_Lean_Meta_Grind_instInhabitedInjectiveTheorem = _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedInjectiveTheorem);
l_Lean_Meta_Grind_instInhabitedExtensionState_default = _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedExtensionState_default);
l_Lean_Meta_Grind_instInhabitedExtensionState = _init_l_Lean_Meta_Grind_instInhabitedExtensionState();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedExtensionState);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Extension(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Meta_Grind_mkExtension___auto__1 = _init_l_Lean_Meta_Grind_mkExtension___auto__1();
lean_mark_persistent(l_Lean_Meta_Grind_mkExtension___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Theorems(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Extension(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
}
#ifdef __cplusplus
}
#endif
