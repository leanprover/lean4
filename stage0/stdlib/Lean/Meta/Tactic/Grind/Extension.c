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
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__0(lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(lean_object* v_x_44_, size_t v_x_45_, size_t v_x_46_, lean_object* v_x_47_, lean_object* v_x_48_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v_es_49_; size_t v___x_50_; size_t v___x_51_; lean_object* v_j_52_; lean_object* v___x_53_; uint8_t v___x_54_; 
v_es_49_ = lean_ctor_get(v_x_44_, 0);
v___x_50_ = ((size_t)31ULL);
v___x_51_ = lean_usize_land(v_x_45_, v___x_50_);
v_j_52_ = lean_usize_to_nat(v___x_51_);
v___x_53_ = lean_array_get_size(v_es_49_);
v___x_54_ = lean_nat_dec_lt(v_j_52_, v___x_53_);
if (v___x_54_ == 0)
{
lean_dec(v_j_52_);
lean_dec(v_x_48_);
lean_dec(v_x_47_);
return v_x_44_;
}
else
{
lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_93_; 
lean_inc_ref(v_es_49_);
v_isSharedCheck_93_ = !lean_is_exclusive(v_x_44_);
if (v_isSharedCheck_93_ == 0)
{
lean_object* v_unused_94_; 
v_unused_94_ = lean_ctor_get(v_x_44_, 0);
lean_dec(v_unused_94_);
v___x_56_ = v_x_44_;
v_isShared_57_ = v_isSharedCheck_93_;
goto v_resetjp_55_;
}
else
{
lean_dec(v_x_44_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_93_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v_v_58_; lean_object* v___x_59_; lean_object* v_xs_x27_60_; lean_object* v___y_62_; 
v_v_58_ = lean_array_fget(v_es_49_, v_j_52_);
v___x_59_ = lean_box(0);
v_xs_x27_60_ = lean_array_fset(v_es_49_, v_j_52_, v___x_59_);
switch(lean_obj_tag(v_v_58_))
{
case 0:
{
lean_object* v_key_67_; lean_object* v_val_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_78_; 
v_key_67_ = lean_ctor_get(v_v_58_, 0);
v_val_68_ = lean_ctor_get(v_v_58_, 1);
v_isSharedCheck_78_ = !lean_is_exclusive(v_v_58_);
if (v_isSharedCheck_78_ == 0)
{
v___x_70_ = v_v_58_;
v_isShared_71_ = v_isSharedCheck_78_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_val_68_);
lean_inc(v_key_67_);
lean_dec(v_v_58_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_78_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
uint8_t v___x_72_; 
v___x_72_ = lean_name_eq(v_x_47_, v_key_67_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_del_object(v___x_70_);
v___x_73_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_67_, v_val_68_, v_x_47_, v_x_48_);
v___x_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
v___y_62_ = v___x_74_;
goto v___jp_61_;
}
else
{
lean_object* v___x_76_; 
lean_dec(v_val_68_);
lean_dec(v_key_67_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 1, v_x_48_);
lean_ctor_set(v___x_70_, 0, v_x_47_);
v___x_76_ = v___x_70_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_x_47_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v_x_48_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
v___y_62_ = v___x_76_;
goto v___jp_61_;
}
}
}
}
case 1:
{
lean_object* v_node_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_91_; 
v_node_79_ = lean_ctor_get(v_v_58_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v_v_58_);
if (v_isSharedCheck_91_ == 0)
{
v___x_81_ = v_v_58_;
v_isShared_82_ = v_isSharedCheck_91_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_node_79_);
lean_dec(v_v_58_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_91_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; size_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_83_ = ((size_t)5ULL);
v___x_84_ = lean_usize_shift_right(v_x_45_, v___x_83_);
v___x_85_ = ((size_t)1ULL);
v___x_86_ = lean_usize_add(v_x_46_, v___x_85_);
v___x_87_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_node_79_, v___x_84_, v___x_86_, v_x_47_, v_x_48_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v___x_87_);
v___x_89_ = v___x_81_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
v___y_62_ = v___x_89_;
goto v___jp_61_;
}
}
}
default: 
{
lean_object* v___x_92_; 
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v_x_47_);
lean_ctor_set(v___x_92_, 1, v_x_48_);
v___y_62_ = v___x_92_;
goto v___jp_61_;
}
}
v___jp_61_:
{
lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_63_ = lean_array_fset(v_xs_x27_60_, v_j_52_, v___y_62_);
lean_dec(v_j_52_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v___x_63_);
v___x_65_ = v___x_56_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
}
else
{
lean_object* v_ks_95_; lean_object* v_vs_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_116_; 
v_ks_95_ = lean_ctor_get(v_x_44_, 0);
v_vs_96_ = lean_ctor_get(v_x_44_, 1);
v_isSharedCheck_116_ = !lean_is_exclusive(v_x_44_);
if (v_isSharedCheck_116_ == 0)
{
v___x_98_ = v_x_44_;
v_isShared_99_ = v_isSharedCheck_116_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_vs_96_);
lean_inc(v_ks_95_);
lean_dec(v_x_44_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_116_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_ks_95_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v_vs_96_);
v___x_101_ = v_reuseFailAlloc_115_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
lean_object* v_newNode_102_; uint8_t v___y_104_; size_t v___x_110_; uint8_t v___x_111_; 
v_newNode_102_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1___redArg(v___x_101_, v_x_47_, v_x_48_);
v___x_110_ = ((size_t)7ULL);
v___x_111_ = lean_usize_dec_le(v___x_110_, v_x_46_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_112_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_102_);
v___x_113_ = lean_unsigned_to_nat(4u);
v___x_114_ = lean_nat_dec_lt(v___x_112_, v___x_113_);
lean_dec(v___x_112_);
v___y_104_ = v___x_114_;
goto v___jp_103_;
}
else
{
v___y_104_ = v___x_111_;
goto v___jp_103_;
}
v___jp_103_:
{
if (v___y_104_ == 0)
{
lean_object* v_ks_105_; lean_object* v_vs_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_ks_105_ = lean_ctor_get(v_newNode_102_, 0);
lean_inc_ref(v_ks_105_);
v_vs_106_ = lean_ctor_get(v_newNode_102_, 1);
lean_inc_ref(v_vs_106_);
lean_dec_ref(v_newNode_102_);
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0);
v___x_109_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_x_46_, v_ks_105_, v_vs_106_, v___x_107_, v___x_108_);
lean_dec_ref(v_vs_106_);
lean_dec_ref(v_ks_105_);
return v___x_109_;
}
else
{
return v_newNode_102_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(size_t v_depth_117_, lean_object* v_keys_118_, lean_object* v_vals_119_, lean_object* v_i_120_, lean_object* v_entries_121_){
_start:
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = lean_array_get_size(v_keys_118_);
v___x_123_ = lean_nat_dec_lt(v_i_120_, v___x_122_);
if (v___x_123_ == 0)
{
lean_dec(v_i_120_);
return v_entries_121_;
}
else
{
lean_object* v_k_124_; lean_object* v_v_125_; uint64_t v___y_127_; 
v_k_124_ = lean_array_fget_borrowed(v_keys_118_, v_i_120_);
v_v_125_ = lean_array_fget_borrowed(v_vals_119_, v_i_120_);
if (lean_obj_tag(v_k_124_) == 0)
{
uint64_t v___x_138_; 
v___x_138_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_127_ = v___x_138_;
goto v___jp_126_;
}
else
{
uint64_t v_hash_139_; 
v_hash_139_ = lean_ctor_get_uint64(v_k_124_, sizeof(void*)*2);
v___y_127_ = v_hash_139_;
goto v___jp_126_;
}
v___jp_126_:
{
size_t v_h_128_; size_t v___x_129_; lean_object* v___x_130_; size_t v___x_131_; size_t v___x_132_; size_t v___x_133_; size_t v_h_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_h_128_ = lean_uint64_to_usize(v___y_127_);
v___x_129_ = ((size_t)5ULL);
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = ((size_t)1ULL);
v___x_132_ = lean_usize_sub(v_depth_117_, v___x_131_);
v___x_133_ = lean_usize_mul(v___x_129_, v___x_132_);
v_h_134_ = lean_usize_shift_right(v_h_128_, v___x_133_);
v___x_135_ = lean_nat_add(v_i_120_, v___x_130_);
lean_dec(v_i_120_);
lean_inc(v_v_125_);
lean_inc(v_k_124_);
v___x_136_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_entries_121_, v_h_134_, v_depth_117_, v_k_124_, v_v_125_);
v_i_120_ = v___x_135_;
v_entries_121_ = v___x_136_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_140_, lean_object* v_keys_141_, lean_object* v_vals_142_, lean_object* v_i_143_, lean_object* v_entries_144_){
_start:
{
size_t v_depth_boxed_145_; lean_object* v_res_146_; 
v_depth_boxed_145_ = lean_unbox_usize(v_depth_140_);
lean_dec(v_depth_140_);
v_res_146_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_145_, v_keys_141_, v_vals_142_, v_i_143_, v_entries_144_);
lean_dec_ref(v_vals_142_);
lean_dec_ref(v_keys_141_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_147_, lean_object* v_x_148_, lean_object* v_x_149_, lean_object* v_x_150_, lean_object* v_x_151_){
_start:
{
size_t v_x_357__boxed_152_; size_t v_x_358__boxed_153_; lean_object* v_res_154_; 
v_x_357__boxed_152_ = lean_unbox_usize(v_x_148_);
lean_dec(v_x_148_);
v_x_358__boxed_153_ = lean_unbox_usize(v_x_149_);
lean_dec(v_x_149_);
v_res_154_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_147_, v_x_357__boxed_152_, v_x_358__boxed_153_, v_x_150_, v_x_151_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(lean_object* v_x_155_, lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
uint64_t v___y_159_; 
if (lean_obj_tag(v_x_156_) == 0)
{
uint64_t v___x_163_; 
v___x_163_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_159_ = v___x_163_;
goto v___jp_158_;
}
else
{
uint64_t v_hash_164_; 
v_hash_164_ = lean_ctor_get_uint64(v_x_156_, sizeof(void*)*2);
v___y_159_ = v_hash_164_;
goto v___jp_158_;
}
v___jp_158_:
{
size_t v___x_160_; size_t v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_uint64_to_usize(v___y_159_);
v___x_161_ = ((size_t)1ULL);
v___x_162_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_155_, v___x_160_, v___x_161_, v_x_156_, v_x_157_);
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_insert(lean_object* v_s_165_, lean_object* v_declName_166_, uint8_t v_eager_167_){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_box(v_eager_167_);
v___x_169_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_s_165_, v_declName_166_, v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_insert___boxed(lean_object* v_s_170_, lean_object* v_declName_171_, lean_object* v_eager_172_){
_start:
{
uint8_t v_eager_boxed_173_; lean_object* v_res_174_; 
v_eager_boxed_173_ = lean_unbox(v_eager_172_);
v_res_174_ = l_Lean_Meta_Grind_CasesTypes_insert(v_s_170_, v_declName_171_, v_eager_boxed_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0(lean_object* v_00_u03b2_175_, lean_object* v_x_176_, lean_object* v_x_177_, lean_object* v_x_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_x_176_, v_x_177_, v_x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0(lean_object* v_00_u03b2_180_, lean_object* v_x_181_, size_t v_x_182_, size_t v_x_183_, lean_object* v_x_184_, lean_object* v_x_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_181_, v_x_182_, v_x_183_, v_x_184_, v_x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
size_t v_x_550__boxed_193_; size_t v_x_551__boxed_194_; lean_object* v_res_195_; 
v_x_550__boxed_193_ = lean_unbox_usize(v_x_189_);
lean_dec(v_x_189_);
v_x_551__boxed_194_ = lean_unbox_usize(v_x_190_);
lean_dec(v_x_190_);
v_res_195_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0(v_00_u03b2_187_, v_x_188_, v_x_550__boxed_193_, v_x_551__boxed_194_, v_x_191_, v_x_192_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_196_, lean_object* v_n_197_, lean_object* v_k_198_, lean_object* v_v_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1___redArg(v_n_197_, v_k_198_, v_v_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_201_, size_t v_depth_202_, lean_object* v_keys_203_, lean_object* v_vals_204_, lean_object* v_heq_205_, lean_object* v_i_206_, lean_object* v_entries_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_depth_202_, v_keys_203_, v_vals_204_, v_i_206_, v_entries_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_209_, lean_object* v_depth_210_, lean_object* v_keys_211_, lean_object* v_vals_212_, lean_object* v_heq_213_, lean_object* v_i_214_, lean_object* v_entries_215_){
_start:
{
size_t v_depth_boxed_216_; lean_object* v_res_217_; 
v_depth_boxed_216_ = lean_unbox_usize(v_depth_210_);
lean_dec(v_depth_210_);
v_res_217_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2(v_00_u03b2_209_, v_depth_boxed_216_, v_keys_211_, v_vals_212_, v_heq_213_, v_i_214_, v_entries_215_);
lean_dec_ref(v_vals_212_);
lean_dec_ref(v_keys_211_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_218_, lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v_x_221_, lean_object* v_x_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_219_, v_x_220_, v_x_221_, v_x_222_);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0(void){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0, &l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default(void){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1, &l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities(void){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default;
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SymbolPriorities_insert(lean_object* v_s_229_, lean_object* v_declName_230_, lean_object* v_prio_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_s_229_, v_declName_230_, v_prio_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(lean_object* v_x_233_){
_start:
{
switch(lean_obj_tag(v_x_233_))
{
case 0:
{
lean_object* v___x_234_; 
v___x_234_ = lean_unsigned_to_nat(0u);
return v___x_234_;
}
case 1:
{
lean_object* v___x_235_; 
v___x_235_ = lean_unsigned_to_nat(1u);
return v___x_235_;
}
case 2:
{
lean_object* v___x_236_; 
v___x_236_ = lean_unsigned_to_nat(2u);
return v___x_236_;
}
case 3:
{
lean_object* v___x_237_; 
v___x_237_ = lean_unsigned_to_nat(3u);
return v___x_237_;
}
case 4:
{
lean_object* v___x_238_; 
v___x_238_ = lean_unsigned_to_nat(4u);
return v___x_238_;
}
case 5:
{
lean_object* v___x_239_; 
v___x_239_ = lean_unsigned_to_nat(5u);
return v___x_239_;
}
case 6:
{
lean_object* v___x_240_; 
v___x_240_ = lean_unsigned_to_nat(6u);
return v___x_240_;
}
case 7:
{
lean_object* v___x_241_; 
v___x_241_ = lean_unsigned_to_nat(7u);
return v___x_241_;
}
case 8:
{
lean_object* v___x_242_; 
v___x_242_ = lean_unsigned_to_nat(8u);
return v___x_242_;
}
default: 
{
lean_object* v___x_243_; 
v___x_243_ = lean_unsigned_to_nat(9u);
return v___x_243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx___boxed(lean_object* v_x_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(v_x_244_);
lean_dec(v_x_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(lean_object* v_t_246_, lean_object* v_k_247_){
_start:
{
switch(lean_obj_tag(v_t_246_))
{
case 0:
{
uint8_t v_gen_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_gen_248_ = lean_ctor_get_uint8(v_t_246_, 0);
v___x_249_ = lean_box(v_gen_248_);
v___x_250_ = lean_apply_1(v_k_247_, v___x_249_);
return v___x_250_;
}
case 1:
{
uint8_t v_gen_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_gen_251_ = lean_ctor_get_uint8(v_t_246_, 0);
v___x_252_ = lean_box(v_gen_251_);
v___x_253_ = lean_apply_1(v_k_247_, v___x_252_);
return v___x_253_;
}
case 2:
{
uint8_t v_gen_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_gen_254_ = lean_ctor_get_uint8(v_t_246_, 0);
v___x_255_ = lean_box(v_gen_254_);
v___x_256_ = lean_apply_1(v_k_247_, v___x_255_);
return v___x_256_;
}
case 5:
{
uint8_t v_gen_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_gen_257_ = lean_ctor_get_uint8(v_t_246_, 0);
v___x_258_ = lean_box(v_gen_257_);
v___x_259_ = lean_apply_1(v_k_247_, v___x_258_);
return v___x_259_;
}
case 8:
{
uint8_t v_gen_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_gen_260_ = lean_ctor_get_uint8(v_t_246_, 0);
v___x_261_ = lean_box(v_gen_260_);
v___x_262_ = lean_apply_1(v_k_247_, v___x_261_);
return v___x_262_;
}
default: 
{
return v_k_247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg___boxed(lean_object* v_t_263_, lean_object* v_k_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_263_, v_k_264_);
lean_dec(v_t_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim(lean_object* v_motive_266_, lean_object* v_ctorIdx_267_, lean_object* v_t_268_, lean_object* v_h_269_, lean_object* v_k_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_268_, v_k_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___boxed(lean_object* v_motive_272_, lean_object* v_ctorIdx_273_, lean_object* v_t_274_, lean_object* v_h_275_, lean_object* v_k_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim(v_motive_272_, v_ctorIdx_273_, v_t_274_, v_h_275_, v_k_276_);
lean_dec(v_t_274_);
lean_dec(v_ctorIdx_273_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg(lean_object* v_t_278_, lean_object* v_eqLhs_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_278_, v_eqLhs_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg___boxed(lean_object* v_t_281_, lean_object* v_eqLhs_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg(v_t_281_, v_eqLhs_282_);
lean_dec(v_t_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim(lean_object* v_motive_284_, lean_object* v_t_285_, lean_object* v_h_286_, lean_object* v_eqLhs_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_285_, v_eqLhs_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___boxed(lean_object* v_motive_289_, lean_object* v_t_290_, lean_object* v_h_291_, lean_object* v_eqLhs_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim(v_motive_289_, v_t_290_, v_h_291_, v_eqLhs_292_);
lean_dec(v_t_290_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg(lean_object* v_t_294_, lean_object* v_eqRhs_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_294_, v_eqRhs_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg___boxed(lean_object* v_t_297_, lean_object* v_eqRhs_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg(v_t_297_, v_eqRhs_298_);
lean_dec(v_t_297_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim(lean_object* v_motive_300_, lean_object* v_t_301_, lean_object* v_h_302_, lean_object* v_eqRhs_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_301_, v_eqRhs_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___boxed(lean_object* v_motive_305_, lean_object* v_t_306_, lean_object* v_h_307_, lean_object* v_eqRhs_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim(v_motive_305_, v_t_306_, v_h_307_, v_eqRhs_308_);
lean_dec(v_t_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg(lean_object* v_t_310_, lean_object* v_eqBoth_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_310_, v_eqBoth_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg___boxed(lean_object* v_t_313_, lean_object* v_eqBoth_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg(v_t_313_, v_eqBoth_314_);
lean_dec(v_t_313_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim(lean_object* v_motive_316_, lean_object* v_t_317_, lean_object* v_h_318_, lean_object* v_eqBoth_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_317_, v_eqBoth_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___boxed(lean_object* v_motive_321_, lean_object* v_t_322_, lean_object* v_h_323_, lean_object* v_eqBoth_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim(v_motive_321_, v_t_322_, v_h_323_, v_eqBoth_324_);
lean_dec(v_t_322_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg(lean_object* v_t_326_, lean_object* v_eqBwd_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_326_, v_eqBwd_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg___boxed(lean_object* v_t_329_, lean_object* v_eqBwd_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg(v_t_329_, v_eqBwd_330_);
lean_dec(v_t_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim(lean_object* v_motive_332_, lean_object* v_t_333_, lean_object* v_h_334_, lean_object* v_eqBwd_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_333_, v_eqBwd_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___boxed(lean_object* v_motive_337_, lean_object* v_t_338_, lean_object* v_h_339_, lean_object* v_eqBwd_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim(v_motive_337_, v_t_338_, v_h_339_, v_eqBwd_340_);
lean_dec(v_t_338_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg(lean_object* v_t_342_, lean_object* v_fwd_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_342_, v_fwd_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg___boxed(lean_object* v_t_345_, lean_object* v_fwd_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg(v_t_345_, v_fwd_346_);
lean_dec(v_t_345_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim(lean_object* v_motive_348_, lean_object* v_t_349_, lean_object* v_h_350_, lean_object* v_fwd_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_349_, v_fwd_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___boxed(lean_object* v_motive_353_, lean_object* v_t_354_, lean_object* v_h_355_, lean_object* v_fwd_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim(v_motive_353_, v_t_354_, v_h_355_, v_fwd_356_);
lean_dec(v_t_354_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg(lean_object* v_t_358_, lean_object* v_bwd_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_358_, v_bwd_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg___boxed(lean_object* v_t_361_, lean_object* v_bwd_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg(v_t_361_, v_bwd_362_);
lean_dec(v_t_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim(lean_object* v_motive_364_, lean_object* v_t_365_, lean_object* v_h_366_, lean_object* v_bwd_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_365_, v_bwd_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___boxed(lean_object* v_motive_369_, lean_object* v_t_370_, lean_object* v_h_371_, lean_object* v_bwd_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim(v_motive_369_, v_t_370_, v_h_371_, v_bwd_372_);
lean_dec(v_t_370_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg(lean_object* v_t_374_, lean_object* v_leftRight_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_374_, v_leftRight_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg___boxed(lean_object* v_t_377_, lean_object* v_leftRight_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg(v_t_377_, v_leftRight_378_);
lean_dec(v_t_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim(lean_object* v_motive_380_, lean_object* v_t_381_, lean_object* v_h_382_, lean_object* v_leftRight_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_381_, v_leftRight_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___boxed(lean_object* v_motive_385_, lean_object* v_t_386_, lean_object* v_h_387_, lean_object* v_leftRight_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim(v_motive_385_, v_t_386_, v_h_387_, v_leftRight_388_);
lean_dec(v_t_386_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg(lean_object* v_t_390_, lean_object* v_rightLeft_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_390_, v_rightLeft_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg___boxed(lean_object* v_t_393_, lean_object* v_rightLeft_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg(v_t_393_, v_rightLeft_394_);
lean_dec(v_t_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim(lean_object* v_motive_396_, lean_object* v_t_397_, lean_object* v_h_398_, lean_object* v_rightLeft_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_397_, v_rightLeft_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___boxed(lean_object* v_motive_401_, lean_object* v_t_402_, lean_object* v_h_403_, lean_object* v_rightLeft_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim(v_motive_401_, v_t_402_, v_h_403_, v_rightLeft_404_);
lean_dec(v_t_402_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg(lean_object* v_t_406_, lean_object* v_default_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_406_, v_default_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg___boxed(lean_object* v_t_409_, lean_object* v_default_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg(v_t_409_, v_default_410_);
lean_dec(v_t_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim(lean_object* v_motive_412_, lean_object* v_t_413_, lean_object* v_h_414_, lean_object* v_default_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_413_, v_default_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___boxed(lean_object* v_motive_417_, lean_object* v_t_418_, lean_object* v_h_419_, lean_object* v_default_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Meta_Grind_EMatchTheoremKind_default_elim(v_motive_417_, v_t_418_, v_h_419_, v_default_420_);
lean_dec(v_t_418_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg(lean_object* v_t_422_, lean_object* v_user_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_422_, v_user_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg___boxed(lean_object* v_t_425_, lean_object* v_user_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg(v_t_425_, v_user_426_);
lean_dec(v_t_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim(lean_object* v_motive_428_, lean_object* v_t_429_, lean_object* v_h_430_, lean_object* v_user_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_429_, v_user_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___boxed(lean_object* v_motive_433_, lean_object* v_t_434_, lean_object* v_h_435_, lean_object* v_user_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_Grind_EMatchTheoremKind_user_elim(v_motive_433_, v_t_434_, v_h_435_, v_user_436_);
lean_dec(v_t_434_);
return v_res_437_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; uint8_t v_gen_448_; uint8_t v_gen_x27_449_; 
v___x_444_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(v_x_442_);
v___x_445_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(v_x_443_);
v___x_446_ = lean_nat_dec_eq(v___x_444_, v___x_445_);
lean_dec(v___x_445_);
lean_dec(v___x_444_);
if (v___x_446_ == 0)
{
return v___x_446_;
}
else
{
switch(lean_obj_tag(v_x_442_))
{
case 0:
{
uint8_t v_gen_450_; uint8_t v_gen_451_; 
v_gen_450_ = lean_ctor_get_uint8(v_x_442_, 0);
v_gen_451_ = lean_ctor_get_uint8(v_x_443_, 0);
v_gen_448_ = v_gen_450_;
v_gen_x27_449_ = v_gen_451_;
goto v___jp_447_;
}
case 1:
{
uint8_t v_gen_452_; uint8_t v_gen_453_; 
v_gen_452_ = lean_ctor_get_uint8(v_x_442_, 0);
v_gen_453_ = lean_ctor_get_uint8(v_x_443_, 0);
v_gen_448_ = v_gen_452_;
v_gen_x27_449_ = v_gen_453_;
goto v___jp_447_;
}
case 2:
{
uint8_t v_gen_454_; uint8_t v_gen_455_; 
v_gen_454_ = lean_ctor_get_uint8(v_x_442_, 0);
v_gen_455_ = lean_ctor_get_uint8(v_x_443_, 0);
v_gen_448_ = v_gen_454_;
v_gen_x27_449_ = v_gen_455_;
goto v___jp_447_;
}
case 5:
{
uint8_t v_gen_456_; uint8_t v_gen_457_; 
v_gen_456_ = lean_ctor_get_uint8(v_x_442_, 0);
v_gen_457_ = lean_ctor_get_uint8(v_x_443_, 0);
v_gen_448_ = v_gen_456_;
v_gen_x27_449_ = v_gen_457_;
goto v___jp_447_;
}
case 8:
{
uint8_t v_gen_458_; uint8_t v_gen_459_; 
v_gen_458_ = lean_ctor_get_uint8(v_x_442_, 0);
v_gen_459_ = lean_ctor_get_uint8(v_x_443_, 0);
v_gen_448_ = v_gen_458_;
v_gen_x27_449_ = v_gen_459_;
goto v___jp_447_;
}
default: 
{
return v___x_446_;
}
}
}
v___jp_447_:
{
if (v_gen_448_ == 0)
{
if (v_gen_x27_449_ == 0)
{
return v___x_446_;
}
else
{
return v_gen_448_;
}
}
else
{
return v_gen_x27_449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq___boxed(lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_x_460_, v_x_461_);
lean_dec(v_x_461_);
lean_dec(v_x_460_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_unsigned_to_nat(2u);
v___x_488_ = lean_nat_to_int(v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = lean_nat_to_int(v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr(lean_object* v_x_515_, lean_object* v_prec_516_){
_start:
{
lean_object* v___y_518_; lean_object* v___y_525_; lean_object* v___y_532_; lean_object* v___y_539_; lean_object* v___y_546_; 
switch(lean_obj_tag(v_x_515_))
{
case 0:
{
uint8_t v_gen_552_; lean_object* v___y_554_; lean_object* v___x_562_; uint8_t v___x_563_; 
v_gen_552_ = lean_ctor_get_uint8(v_x_515_, 0);
v___x_562_ = lean_unsigned_to_nat(1024u);
v___x_563_ = lean_nat_dec_le(v___x_562_, v_prec_516_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; 
v___x_564_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_554_ = v___x_564_;
goto v___jp_553_;
}
else
{
lean_object* v___x_565_; 
v___x_565_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_554_ = v___x_565_;
goto v___jp_553_;
}
v___jp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_555_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__12));
v___x_556_ = l_Bool_repr___redArg(v_gen_552_);
v___x_557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
lean_inc(v___y_554_);
v___x_558_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_558_, 0, v___y_554_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = 0;
v___x_560_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_560_, 0, v___x_558_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*1, v___x_559_);
v___x_561_ = l_Repr_addAppParen(v___x_560_, v_prec_516_);
return v___x_561_;
}
}
case 1:
{
uint8_t v_gen_566_; lean_object* v___y_568_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_gen_566_ = lean_ctor_get_uint8(v_x_515_, 0);
v___x_576_ = lean_unsigned_to_nat(1024u);
v___x_577_ = lean_nat_dec_le(v___x_576_, v_prec_516_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
v___x_578_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_568_ = v___x_578_;
goto v___jp_567_;
}
else
{
lean_object* v___x_579_; 
v___x_579_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_568_ = v___x_579_;
goto v___jp_567_;
}
v___jp_567_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_569_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__17));
v___x_570_ = l_Bool_repr___redArg(v_gen_566_);
v___x_571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
lean_inc(v___y_568_);
v___x_572_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_572_, 0, v___y_568_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = 0;
v___x_574_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_574_, 0, v___x_572_);
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*1, v___x_573_);
v___x_575_ = l_Repr_addAppParen(v___x_574_, v_prec_516_);
return v___x_575_;
}
}
case 2:
{
uint8_t v_gen_580_; lean_object* v___y_582_; lean_object* v___x_590_; uint8_t v___x_591_; 
v_gen_580_ = lean_ctor_get_uint8(v_x_515_, 0);
v___x_590_ = lean_unsigned_to_nat(1024u);
v___x_591_ = lean_nat_dec_le(v___x_590_, v_prec_516_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_582_ = v___x_592_;
goto v___jp_581_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_582_ = v___x_593_;
goto v___jp_581_;
}
v___jp_581_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_583_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__20));
v___x_584_ = l_Bool_repr___redArg(v_gen_580_);
v___x_585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_583_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
lean_inc(v___y_582_);
v___x_586_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_586_, 0, v___y_582_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = 0;
v___x_588_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set_uint8(v___x_588_, sizeof(void*)*1, v___x_587_);
v___x_589_ = l_Repr_addAppParen(v___x_588_, v_prec_516_);
return v___x_589_;
}
}
case 3:
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_unsigned_to_nat(1024u);
v___x_595_ = lean_nat_dec_le(v___x_594_, v_prec_516_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
v___x_596_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_532_ = v___x_596_;
goto v___jp_531_;
}
else
{
lean_object* v___x_597_; 
v___x_597_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_532_ = v___x_597_;
goto v___jp_531_;
}
}
case 4:
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_unsigned_to_nat(1024u);
v___x_599_ = lean_nat_dec_le(v___x_598_, v_prec_516_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; 
v___x_600_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_539_ = v___x_600_;
goto v___jp_538_;
}
else
{
lean_object* v___x_601_; 
v___x_601_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_539_ = v___x_601_;
goto v___jp_538_;
}
}
case 5:
{
uint8_t v_gen_602_; lean_object* v___y_604_; lean_object* v___x_612_; uint8_t v___x_613_; 
v_gen_602_ = lean_ctor_get_uint8(v_x_515_, 0);
v___x_612_ = lean_unsigned_to_nat(1024u);
v___x_613_ = lean_nat_dec_le(v___x_612_, v_prec_516_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
v___x_614_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_604_ = v___x_614_;
goto v___jp_603_;
}
else
{
lean_object* v___x_615_; 
v___x_615_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_604_ = v___x_615_;
goto v___jp_603_;
}
v___jp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_605_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__23));
v___x_606_ = l_Bool_repr___redArg(v_gen_602_);
v___x_607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
lean_inc(v___y_604_);
v___x_608_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_608_, 0, v___y_604_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = 0;
v___x_610_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*1, v___x_609_);
v___x_611_ = l_Repr_addAppParen(v___x_610_, v_prec_516_);
return v___x_611_;
}
}
case 6:
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = lean_unsigned_to_nat(1024u);
v___x_617_ = lean_nat_dec_le(v___x_616_, v_prec_516_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
v___x_618_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_525_ = v___x_618_;
goto v___jp_524_;
}
else
{
lean_object* v___x_619_; 
v___x_619_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_525_ = v___x_619_;
goto v___jp_524_;
}
}
case 7:
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = lean_unsigned_to_nat(1024u);
v___x_621_ = lean_nat_dec_le(v___x_620_, v_prec_516_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
v___x_622_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_518_ = v___x_622_;
goto v___jp_517_;
}
else
{
lean_object* v___x_623_; 
v___x_623_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_518_ = v___x_623_;
goto v___jp_517_;
}
}
case 8:
{
uint8_t v_gen_624_; lean_object* v___y_626_; lean_object* v___x_634_; uint8_t v___x_635_; 
v_gen_624_ = lean_ctor_get_uint8(v_x_515_, 0);
v___x_634_ = lean_unsigned_to_nat(1024u);
v___x_635_ = lean_nat_dec_le(v___x_634_, v_prec_516_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
v___x_636_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_626_ = v___x_636_;
goto v___jp_625_;
}
else
{
lean_object* v___x_637_; 
v___x_637_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_626_ = v___x_637_;
goto v___jp_625_;
}
v___jp_625_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_627_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__26));
v___x_628_ = l_Bool_repr___redArg(v_gen_624_);
v___x_629_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
lean_inc(v___y_626_);
v___x_630_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_630_, 0, v___y_626_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = 0;
v___x_632_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*1, v___x_631_);
v___x_633_ = l_Repr_addAppParen(v___x_632_, v_prec_516_);
return v___x_633_;
}
}
default: 
{
lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = lean_unsigned_to_nat(1024u);
v___x_639_ = lean_nat_dec_le(v___x_638_, v_prec_516_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
v___x_640_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_546_ = v___x_640_;
goto v___jp_545_;
}
else
{
lean_object* v___x_641_; 
v___x_641_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_546_ = v___x_641_;
goto v___jp_545_;
}
}
}
v___jp_517_:
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_519_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__1));
lean_inc(v___y_518_);
v___x_520_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_520_, 0, v___y_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = 0;
v___x_522_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*1, v___x_521_);
v___x_523_ = l_Repr_addAppParen(v___x_522_, v_prec_516_);
return v___x_523_;
}
v___jp_524_:
{
lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_526_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__3));
lean_inc(v___y_525_);
v___x_527_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_527_, 0, v___y_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = 0;
v___x_529_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*1, v___x_528_);
v___x_530_ = l_Repr_addAppParen(v___x_529_, v_prec_516_);
return v___x_530_;
}
v___jp_531_:
{
lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_533_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__5));
lean_inc(v___y_532_);
v___x_534_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_534_, 0, v___y_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = 0;
v___x_536_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set_uint8(v___x_536_, sizeof(void*)*1, v___x_535_);
v___x_537_ = l_Repr_addAppParen(v___x_536_, v_prec_516_);
return v___x_537_;
}
v___jp_538_:
{
lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_540_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__7));
lean_inc(v___y_539_);
v___x_541_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_541_, 0, v___y_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = 0;
v___x_543_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set_uint8(v___x_543_, sizeof(void*)*1, v___x_542_);
v___x_544_ = l_Repr_addAppParen(v___x_543_, v_prec_516_);
return v___x_544_;
}
v___jp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_547_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__9));
lean_inc(v___y_546_);
v___x_548_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_548_, 0, v___y_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = 0;
v___x_550_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*1, v___x_549_);
v___x_551_ = l_Repr_addAppParen(v___x_550_, v_prec_516_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___boxed(lean_object* v_x_642_, lean_object* v_prec_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr(v_x_642_, v_prec_643_);
lean_dec(v_prec_643_);
lean_dec(v_x_642_);
return v_res_644_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0(void){
_start:
{
uint64_t v___x_647_; uint64_t v___x_648_; uint64_t v___x_649_; 
v___x_647_ = 13ULL;
v___x_648_ = 0ULL;
v___x_649_ = lean_uint64_mix_hash(v___x_648_, v___x_647_);
return v___x_649_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1(void){
_start:
{
uint64_t v___x_650_; uint64_t v___x_651_; uint64_t v___x_652_; 
v___x_650_ = 11ULL;
v___x_651_ = 0ULL;
v___x_652_ = lean_uint64_mix_hash(v___x_651_, v___x_650_);
return v___x_652_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2(void){
_start:
{
uint64_t v___x_653_; uint64_t v___x_654_; uint64_t v___x_655_; 
v___x_653_ = 13ULL;
v___x_654_ = 1ULL;
v___x_655_ = lean_uint64_mix_hash(v___x_654_, v___x_653_);
return v___x_655_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3(void){
_start:
{
uint64_t v___x_656_; uint64_t v___x_657_; uint64_t v___x_658_; 
v___x_656_ = 11ULL;
v___x_657_ = 1ULL;
v___x_658_ = lean_uint64_mix_hash(v___x_657_, v___x_656_);
return v___x_658_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4(void){
_start:
{
uint64_t v___x_659_; uint64_t v___x_660_; uint64_t v___x_661_; 
v___x_659_ = 13ULL;
v___x_660_ = 2ULL;
v___x_661_ = lean_uint64_mix_hash(v___x_660_, v___x_659_);
return v___x_661_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5(void){
_start:
{
uint64_t v___x_662_; uint64_t v___x_663_; uint64_t v___x_664_; 
v___x_662_ = 11ULL;
v___x_663_ = 2ULL;
v___x_664_ = lean_uint64_mix_hash(v___x_663_, v___x_662_);
return v___x_664_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6(void){
_start:
{
uint64_t v___x_665_; uint64_t v___x_666_; uint64_t v___x_667_; 
v___x_665_ = 13ULL;
v___x_666_ = 5ULL;
v___x_667_ = lean_uint64_mix_hash(v___x_666_, v___x_665_);
return v___x_667_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7(void){
_start:
{
uint64_t v___x_668_; uint64_t v___x_669_; uint64_t v___x_670_; 
v___x_668_ = 11ULL;
v___x_669_ = 5ULL;
v___x_670_ = lean_uint64_mix_hash(v___x_669_, v___x_668_);
return v___x_670_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8(void){
_start:
{
uint64_t v___x_671_; uint64_t v___x_672_; uint64_t v___x_673_; 
v___x_671_ = 13ULL;
v___x_672_ = 8ULL;
v___x_673_ = lean_uint64_mix_hash(v___x_672_, v___x_671_);
return v___x_673_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9(void){
_start:
{
uint64_t v___x_674_; uint64_t v___x_675_; uint64_t v___x_676_; 
v___x_674_ = 11ULL;
v___x_675_ = 8ULL;
v___x_676_ = lean_uint64_mix_hash(v___x_675_, v___x_674_);
return v___x_676_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(lean_object* v_x_677_){
_start:
{
switch(lean_obj_tag(v_x_677_))
{
case 0:
{
uint8_t v_gen_678_; 
v_gen_678_ = lean_ctor_get_uint8(v_x_677_, 0);
if (v_gen_678_ == 0)
{
uint64_t v___x_679_; 
v___x_679_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0);
return v___x_679_;
}
else
{
uint64_t v___x_680_; 
v___x_680_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1);
return v___x_680_;
}
}
case 1:
{
uint8_t v_gen_681_; 
v_gen_681_ = lean_ctor_get_uint8(v_x_677_, 0);
if (v_gen_681_ == 0)
{
uint64_t v___x_682_; 
v___x_682_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2);
return v___x_682_;
}
else
{
uint64_t v___x_683_; 
v___x_683_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3);
return v___x_683_;
}
}
case 2:
{
uint8_t v_gen_684_; 
v_gen_684_ = lean_ctor_get_uint8(v_x_677_, 0);
if (v_gen_684_ == 0)
{
uint64_t v___x_685_; 
v___x_685_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4);
return v___x_685_;
}
else
{
uint64_t v___x_686_; 
v___x_686_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5);
return v___x_686_;
}
}
case 3:
{
uint64_t v___x_687_; 
v___x_687_ = 3ULL;
return v___x_687_;
}
case 4:
{
uint64_t v___x_688_; 
v___x_688_ = 4ULL;
return v___x_688_;
}
case 5:
{
uint8_t v_gen_689_; 
v_gen_689_ = lean_ctor_get_uint8(v_x_677_, 0);
if (v_gen_689_ == 0)
{
uint64_t v___x_690_; 
v___x_690_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6);
return v___x_690_;
}
else
{
uint64_t v___x_691_; 
v___x_691_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7);
return v___x_691_;
}
}
case 6:
{
uint64_t v___x_692_; 
v___x_692_ = 6ULL;
return v___x_692_;
}
case 7:
{
uint64_t v___x_693_; 
v___x_693_ = 7ULL;
return v___x_693_;
}
case 8:
{
uint8_t v_gen_694_; 
v_gen_694_ = lean_ctor_get_uint8(v_x_677_, 0);
if (v_gen_694_ == 0)
{
uint64_t v___x_695_; 
v___x_695_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8);
return v___x_695_;
}
else
{
uint64_t v___x_696_; 
v___x_696_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9);
return v___x_696_;
}
}
default: 
{
uint64_t v___x_697_; 
v___x_697_ = 9ULL;
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___boxed(lean_object* v_x_698_){
_start:
{
uint64_t v_res_699_; lean_object* v_r_700_; 
v_res_699_ = l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(v_x_698_);
lean_dec(v_x_698_);
v_r_700_ = lean_box_uint64(v_res_699_);
return v_r_700_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_708_ = lean_box(0);
v___x_709_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__2));
v___x_710_ = l_Lean_Expr_const___override(v___x_709_, v___x_708_);
return v___x_710_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_711_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v___x_712_);
lean_ctor_set(v___x_714_, 2, v___x_711_);
return v___x_714_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default(void){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4);
return v___x_715_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS(void){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default;
return v___x_716_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(lean_object* v_xs_717_, lean_object* v_ys_718_, lean_object* v_x_719_){
_start:
{
lean_object* v_zero_720_; uint8_t v_isZero_721_; 
v_zero_720_ = lean_unsigned_to_nat(0u);
v_isZero_721_ = lean_nat_dec_eq(v_x_719_, v_zero_720_);
if (v_isZero_721_ == 1)
{
lean_dec(v_x_719_);
return v_isZero_721_;
}
else
{
lean_object* v_one_722_; lean_object* v_n_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_one_722_ = lean_unsigned_to_nat(1u);
v_n_723_ = lean_nat_sub(v_x_719_, v_one_722_);
lean_dec(v_x_719_);
v___x_724_ = lean_array_fget_borrowed(v_xs_717_, v_n_723_);
v___x_725_ = lean_array_fget_borrowed(v_ys_718_, v_n_723_);
v___x_726_ = lean_name_eq(v___x_724_, v___x_725_);
if (v___x_726_ == 0)
{
lean_dec(v_n_723_);
return v___x_726_;
}
else
{
v_x_719_ = v_n_723_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg___boxed(lean_object* v_xs_728_, lean_object* v_ys_729_, lean_object* v_x_730_){
_start:
{
uint8_t v_res_731_; lean_object* v_r_732_; 
v_res_731_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_xs_728_, v_ys_729_, v_x_730_);
lean_dec_ref(v_ys_729_);
lean_dec_ref(v_xs_728_);
v_r_732_ = lean_box(v_res_731_);
return v_r_732_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqCnstrRHS_beq(lean_object* v_x_733_, lean_object* v_x_734_){
_start:
{
lean_object* v_levelNames_735_; lean_object* v_numMVars_736_; lean_object* v_expr_737_; lean_object* v_levelNames_738_; lean_object* v_numMVars_739_; lean_object* v_expr_740_; lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v_levelNames_735_ = lean_ctor_get(v_x_733_, 0);
v_numMVars_736_ = lean_ctor_get(v_x_733_, 1);
v_expr_737_ = lean_ctor_get(v_x_733_, 2);
v_levelNames_738_ = lean_ctor_get(v_x_734_, 0);
v_numMVars_739_ = lean_ctor_get(v_x_734_, 1);
v_expr_740_ = lean_ctor_get(v_x_734_, 2);
v___x_741_ = lean_array_get_size(v_levelNames_735_);
v___x_742_ = lean_array_get_size(v_levelNames_738_);
v___x_743_ = lean_nat_dec_eq(v___x_741_, v___x_742_);
if (v___x_743_ == 0)
{
return v___x_743_;
}
else
{
uint8_t v___x_744_; 
v___x_744_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_levelNames_735_, v_levelNames_738_, v___x_741_);
if (v___x_744_ == 0)
{
return v___x_744_;
}
else
{
uint8_t v___x_745_; 
v___x_745_ = lean_nat_dec_eq(v_numMVars_736_, v_numMVars_739_);
if (v___x_745_ == 0)
{
return v___x_745_;
}
else
{
uint8_t v___x_746_; 
v___x_746_ = lean_expr_eqv(v_expr_737_, v_expr_740_);
return v___x_746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqCnstrRHS_beq___boxed(lean_object* v_x_747_, lean_object* v_x_748_){
_start:
{
uint8_t v_res_749_; lean_object* v_r_750_; 
v_res_749_ = l_Lean_Meta_Grind_instBEqCnstrRHS_beq(v_x_747_, v_x_748_);
lean_dec_ref(v_x_748_);
lean_dec_ref(v_x_747_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(lean_object* v_xs_751_, lean_object* v_ys_752_, lean_object* v_hsz_753_, lean_object* v_x_754_, lean_object* v_x_755_){
_start:
{
uint8_t v___x_756_; 
v___x_756_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_xs_751_, v_ys_752_, v_x_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___boxed(lean_object* v_xs_757_, lean_object* v_ys_758_, lean_object* v_hsz_759_, lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
uint8_t v_res_762_; lean_object* v_r_763_; 
v_res_762_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(v_xs_757_, v_ys_758_, v_hsz_759_, v_x_760_, v_x_761_);
lean_dec_ref(v_ys_758_);
lean_dec_ref(v_xs_757_);
v_r_763_ = lean_box(v_res_762_);
return v_r_763_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__1(lean_object* v_a_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = lean_nat_to_int(v_a_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_768_, lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
if (lean_obj_tag(v_x_770_) == 0)
{
lean_dec(v_x_768_);
return v_x_769_;
}
else
{
lean_object* v_head_771_; lean_object* v_tail_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_783_; 
v_head_771_ = lean_ctor_get(v_x_770_, 0);
v_tail_772_ = lean_ctor_get(v_x_770_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_x_770_);
if (v_isSharedCheck_783_ == 0)
{
v___x_774_ = v_x_770_;
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_tail_772_);
lean_inc(v_head_771_);
lean_dec(v_x_770_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
lean_inc(v_x_768_);
if (v_isShared_775_ == 0)
{
lean_ctor_set_tag(v___x_774_, 5);
lean_ctor_set(v___x_774_, 1, v_x_768_);
lean_ctor_set(v___x_774_, 0, v_x_769_);
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_x_769_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_x_768_);
v___x_777_ = v_reuseFailAlloc_782_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = l_Lean_Name_reprPrec(v_head_771_, v___x_778_);
v___x_780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_777_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v_x_769_ = v___x_780_;
v_x_770_ = v_tail_772_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2(lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
if (lean_obj_tag(v_x_786_) == 0)
{
lean_dec(v_x_784_);
return v_x_785_;
}
else
{
lean_object* v_head_787_; lean_object* v_tail_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_799_; 
v_head_787_ = lean_ctor_get(v_x_786_, 0);
v_tail_788_ = lean_ctor_get(v_x_786_, 1);
v_isSharedCheck_799_ = !lean_is_exclusive(v_x_786_);
if (v_isSharedCheck_799_ == 0)
{
v___x_790_ = v_x_786_;
v_isShared_791_ = v_isSharedCheck_799_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_tail_788_);
lean_inc(v_head_787_);
lean_dec(v_x_786_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_799_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
lean_inc(v_x_784_);
if (v_isShared_791_ == 0)
{
lean_ctor_set_tag(v___x_790_, 5);
lean_ctor_set(v___x_790_, 1, v_x_784_);
lean_ctor_set(v___x_790_, 0, v_x_785_);
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_x_785_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_x_784_);
v___x_793_ = v_reuseFailAlloc_798_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = l_Lean_Name_reprPrec(v_head_787_, v___x_794_);
v___x_796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_793_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2_spec__3(v_x_784_, v___x_796_, v_tail_788_);
return v___x_797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(lean_object* v___y_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_unsigned_to_nat(0u);
v___x_802_ = l_Lean_Name_reprPrec(v___y_800_, v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0(lean_object* v_x_803_, lean_object* v_x_804_){
_start:
{
if (lean_obj_tag(v_x_803_) == 0)
{
lean_object* v___x_805_; 
lean_dec(v_x_804_);
v___x_805_ = lean_box(0);
return v___x_805_;
}
else
{
lean_object* v_tail_806_; 
v_tail_806_ = lean_ctor_get(v_x_803_, 1);
if (lean_obj_tag(v_tail_806_) == 0)
{
lean_object* v_head_807_; lean_object* v___x_808_; 
lean_dec(v_x_804_);
v_head_807_ = lean_ctor_get(v_x_803_, 0);
lean_inc(v_head_807_);
lean_dec_ref_known(v_x_803_, 2);
v___x_808_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(v_head_807_);
return v___x_808_;
}
else
{
lean_object* v_head_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
lean_inc(v_tail_806_);
v_head_809_ = lean_ctor_get(v_x_803_, 0);
lean_inc(v_head_809_);
lean_dec_ref_known(v_x_803_, 2);
v___x_810_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(v_head_809_);
v___x_811_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2(v_x_804_, v___x_810_, v_tail_806_);
return v___x_811_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0));
v___x_821_ = lean_string_length(v___x_820_);
return v___x_821_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5);
v___x_823_ = lean_nat_to_int(v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0(lean_object* v_xs_831_){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_832_ = lean_array_get_size(v_xs_831_);
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = lean_nat_dec_eq(v___x_832_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_835_ = lean_array_to_list(v_xs_831_);
v___x_836_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__3));
v___x_837_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0(v___x_835_, v___x_836_);
v___x_838_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6);
v___x_839_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__7));
v___x_840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
lean_ctor_set(v___x_840_, 1, v___x_837_);
v___x_841_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__8));
v___x_842_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_840_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_838_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = l_Std_Format_fill(v___x_843_);
return v___x_844_;
}
else
{
lean_object* v___x_845_; 
lean_dec_ref(v_xs_831_);
v___x_845_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__10));
return v___x_845_;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_unsigned_to_nat(14u);
v___x_860_ = lean_nat_to_int(v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_unsigned_to_nat(12u);
v___x_865_ = lean_nat_to_int(v___x_864_);
return v___x_865_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_unsigned_to_nat(8u);
v___x_870_ = lean_nat_to_int(v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0));
v___x_873_ = lean_string_length(v___x_872_);
return v___x_873_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15);
v___x_875_ = lean_nat_to_int(v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(lean_object* v_x_880_){
_start:
{
lean_object* v_levelNames_881_; lean_object* v_numMVars_882_; lean_object* v_expr_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_levelNames_881_ = lean_ctor_get(v_x_880_, 0);
lean_inc_ref(v_levelNames_881_);
v_numMVars_882_ = lean_ctor_get(v_x_880_, 1);
lean_inc(v_numMVars_882_);
v_expr_883_ = lean_ctor_get(v_x_880_, 2);
lean_inc_ref(v_expr_883_);
lean_dec_ref(v_x_880_);
v___x_884_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5));
v___x_885_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__6));
v___x_886_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7);
v___x_887_ = l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0(v_levelNames_881_);
v___x_888_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = 0;
v___x_890_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set_uint8(v___x_890_, sizeof(void*)*1, v___x_889_);
v___x_891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_885_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2));
v___x_893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = lean_box(1);
v___x_895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__9));
v___x_897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v___x_884_);
v___x_899_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10);
v___x_900_ = l_Nat_reprFast(v_numMVars_882_);
v___x_901_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
v___x_902_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_899_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*1, v___x_889_);
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_898_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___x_892_);
v___x_906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v___x_894_);
v___x_907_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__12));
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v___x_884_);
v___x_910_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13);
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = l_Lean_instReprExpr_repr(v_expr_883_, v___x_911_);
v___x_913_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_910_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*1, v___x_889_);
v___x_915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_909_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16);
v___x_917_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__17));
v___x_918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v___x_915_);
v___x_919_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__18));
v___x_920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_916_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*1, v___x_889_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr(lean_object* v_x_923_, lean_object* v_prec_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_x_923_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___boxed(lean_object* v_x_926_, lean_object* v_prec_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr(v_x_926_, v_prec_927_);
lean_dec(v_prec_927_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(lean_object* v_x_931_){
_start:
{
switch(lean_obj_tag(v_x_931_))
{
case 0:
{
lean_object* v___x_932_; 
v___x_932_ = lean_unsigned_to_nat(0u);
return v___x_932_;
}
case 1:
{
lean_object* v___x_933_; 
v___x_933_ = lean_unsigned_to_nat(1u);
return v___x_933_;
}
case 2:
{
lean_object* v___x_934_; 
v___x_934_ = lean_unsigned_to_nat(2u);
return v___x_934_;
}
case 3:
{
lean_object* v___x_935_; 
v___x_935_ = lean_unsigned_to_nat(3u);
return v___x_935_;
}
case 4:
{
lean_object* v___x_936_; 
v___x_936_ = lean_unsigned_to_nat(4u);
return v___x_936_;
}
case 5:
{
lean_object* v___x_937_; 
v___x_937_ = lean_unsigned_to_nat(5u);
return v___x_937_;
}
case 6:
{
lean_object* v___x_938_; 
v___x_938_ = lean_unsigned_to_nat(6u);
return v___x_938_;
}
case 7:
{
lean_object* v___x_939_; 
v___x_939_ = lean_unsigned_to_nat(7u);
return v___x_939_;
}
case 8:
{
lean_object* v___x_940_; 
v___x_940_ = lean_unsigned_to_nat(8u);
return v___x_940_;
}
case 9:
{
lean_object* v___x_941_; 
v___x_941_ = lean_unsigned_to_nat(9u);
return v___x_941_;
}
default: 
{
lean_object* v___x_942_; 
v___x_942_ = lean_unsigned_to_nat(10u);
return v___x_942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx___boxed(lean_object* v_x_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_943_);
lean_dec_ref(v_x_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(lean_object* v_t_945_, lean_object* v_k_946_){
_start:
{
switch(lean_obj_tag(v_t_945_))
{
case 0:
{
lean_object* v_lhs_947_; lean_object* v_rhs_948_; lean_object* v___x_949_; 
v_lhs_947_ = lean_ctor_get(v_t_945_, 0);
lean_inc(v_lhs_947_);
v_rhs_948_ = lean_ctor_get(v_t_945_, 1);
lean_inc_ref(v_rhs_948_);
lean_dec_ref_known(v_t_945_, 2);
v___x_949_ = lean_apply_2(v_k_946_, v_lhs_947_, v_rhs_948_);
return v___x_949_;
}
case 1:
{
lean_object* v_lhs_950_; lean_object* v_rhs_951_; lean_object* v___x_952_; 
v_lhs_950_ = lean_ctor_get(v_t_945_, 0);
lean_inc(v_lhs_950_);
v_rhs_951_ = lean_ctor_get(v_t_945_, 1);
lean_inc_ref(v_rhs_951_);
lean_dec_ref_known(v_t_945_, 2);
v___x_952_ = lean_apply_2(v_k_946_, v_lhs_950_, v_rhs_951_);
return v___x_952_;
}
case 2:
{
lean_object* v_lhs_953_; lean_object* v_n_954_; lean_object* v___x_955_; 
v_lhs_953_ = lean_ctor_get(v_t_945_, 0);
lean_inc(v_lhs_953_);
v_n_954_ = lean_ctor_get(v_t_945_, 1);
lean_inc(v_n_954_);
lean_dec_ref_known(v_t_945_, 2);
v___x_955_ = lean_apply_2(v_k_946_, v_lhs_953_, v_n_954_);
return v___x_955_;
}
case 3:
{
lean_object* v_lhs_956_; lean_object* v_n_957_; lean_object* v___x_958_; 
v_lhs_956_ = lean_ctor_get(v_t_945_, 0);
lean_inc(v_lhs_956_);
v_n_957_ = lean_ctor_get(v_t_945_, 1);
lean_inc(v_n_957_);
lean_dec_ref_known(v_t_945_, 2);
v___x_958_ = lean_apply_2(v_k_946_, v_lhs_956_, v_n_957_);
return v___x_958_;
}
case 6:
{
lean_object* v_bvarIdx_959_; uint8_t v_strict_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_bvarIdx_959_ = lean_ctor_get(v_t_945_, 0);
lean_inc(v_bvarIdx_959_);
v_strict_960_ = lean_ctor_get_uint8(v_t_945_, sizeof(void*)*1);
lean_dec_ref_known(v_t_945_, 1);
v___x_961_ = lean_box(v_strict_960_);
v___x_962_ = lean_apply_2(v_k_946_, v_bvarIdx_959_, v___x_961_);
return v___x_962_;
}
case 8:
{
lean_object* v_e_963_; lean_object* v___x_964_; 
v_e_963_ = lean_ctor_get(v_t_945_, 0);
lean_inc_ref(v_e_963_);
lean_dec_ref_known(v_t_945_, 1);
v___x_964_ = lean_apply_1(v_k_946_, v_e_963_);
return v___x_964_;
}
case 9:
{
lean_object* v_e_965_; lean_object* v___x_966_; 
v_e_965_ = lean_ctor_get(v_t_945_, 0);
lean_inc_ref(v_e_965_);
lean_dec_ref_known(v_t_945_, 1);
v___x_966_ = lean_apply_1(v_k_946_, v_e_965_);
return v___x_966_;
}
case 10:
{
lean_object* v_bvarIdx_967_; uint8_t v_strict_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_bvarIdx_967_ = lean_ctor_get(v_t_945_, 0);
lean_inc(v_bvarIdx_967_);
v_strict_968_ = lean_ctor_get_uint8(v_t_945_, sizeof(void*)*1);
lean_dec_ref_known(v_t_945_, 1);
v___x_969_ = lean_box(v_strict_968_);
v___x_970_ = lean_apply_2(v_k_946_, v_bvarIdx_967_, v___x_969_);
return v___x_970_;
}
default: 
{
lean_object* v_n_971_; lean_object* v___x_972_; 
v_n_971_ = lean_ctor_get(v_t_945_, 0);
lean_inc(v_n_971_);
lean_dec_ref(v_t_945_);
v___x_972_ = lean_apply_1(v_k_946_, v_n_971_);
return v___x_972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim(lean_object* v_motive_973_, lean_object* v_ctorIdx_974_, lean_object* v_t_975_, lean_object* v_h_976_, lean_object* v_k_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_975_, v_k_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___boxed(lean_object* v_motive_979_, lean_object* v_ctorIdx_980_, lean_object* v_t_981_, lean_object* v_h_982_, lean_object* v_k_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim(v_motive_979_, v_ctorIdx_980_, v_t_981_, v_h_982_, v_k_983_);
lean_dec(v_ctorIdx_980_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim___redArg(lean_object* v_t_985_, lean_object* v_notDefEq_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_985_, v_notDefEq_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim(lean_object* v_motive_988_, lean_object* v_t_989_, lean_object* v_h_990_, lean_object* v_notDefEq_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_989_, v_notDefEq_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim___redArg(lean_object* v_t_993_, lean_object* v_defEq_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_993_, v_defEq_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim(lean_object* v_motive_996_, lean_object* v_t_997_, lean_object* v_h_998_, lean_object* v_defEq_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_997_, v_defEq_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim___redArg(lean_object* v_t_1001_, lean_object* v_sizeLt_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1001_, v_sizeLt_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim(lean_object* v_motive_1004_, lean_object* v_t_1005_, lean_object* v_h_1006_, lean_object* v_sizeLt_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1005_, v_sizeLt_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim___redArg(lean_object* v_t_1009_, lean_object* v_depthLt_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1009_, v_depthLt_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim(lean_object* v_motive_1012_, lean_object* v_t_1013_, lean_object* v_h_1014_, lean_object* v_depthLt_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1013_, v_depthLt_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim___redArg(lean_object* v_t_1017_, lean_object* v_genLt_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1017_, v_genLt_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim(lean_object* v_motive_1020_, lean_object* v_t_1021_, lean_object* v_h_1022_, lean_object* v_genLt_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1021_, v_genLt_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim___redArg(lean_object* v_t_1025_, lean_object* v_isGround_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1025_, v_isGround_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim(lean_object* v_motive_1028_, lean_object* v_t_1029_, lean_object* v_h_1030_, lean_object* v_isGround_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1029_, v_isGround_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim___redArg(lean_object* v_t_1033_, lean_object* v_isValue_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1033_, v_isValue_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim(lean_object* v_motive_1036_, lean_object* v_t_1037_, lean_object* v_h_1038_, lean_object* v_isValue_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1037_, v_isValue_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim___redArg(lean_object* v_t_1041_, lean_object* v_maxInsts_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1041_, v_maxInsts_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim(lean_object* v_motive_1044_, lean_object* v_t_1045_, lean_object* v_h_1046_, lean_object* v_maxInsts_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1045_, v_maxInsts_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim___redArg(lean_object* v_t_1049_, lean_object* v_guard_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1049_, v_guard_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim(lean_object* v_motive_1052_, lean_object* v_t_1053_, lean_object* v_h_1054_, lean_object* v_guard_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1053_, v_guard_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim___redArg(lean_object* v_t_1057_, lean_object* v_check_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1057_, v_check_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim(lean_object* v_motive_1060_, lean_object* v_t_1061_, lean_object* v_h_1062_, lean_object* v_check_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1061_, v_check_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim___redArg(lean_object* v_t_1065_, lean_object* v_notValue_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1065_, v_notValue_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim(lean_object* v_motive_1068_, lean_object* v_t_1069_, lean_object* v_h_1070_, lean_object* v_notValue_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1069_, v_notValue_1071_);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1073_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default;
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v___x_1073_);
return v___x_1075_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default(void){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0, &l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint(void){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default;
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr(lean_object* v_x_1144_, lean_object* v_prec_1145_){
_start:
{
switch(lean_obj_tag(v_x_1144_))
{
case 0:
{
lean_object* v_lhs_1146_; lean_object* v_rhs_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1171_; 
v_lhs_1146_ = lean_ctor_get(v_x_1144_, 0);
v_rhs_1147_ = lean_ctor_get(v_x_1144_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_x_1144_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1149_ = v_x_1144_;
v_isShared_1150_ = v_isSharedCheck_1171_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_rhs_1147_);
lean_inc(v_lhs_1146_);
lean_dec(v_x_1144_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1171_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___y_1152_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = lean_unsigned_to_nat(1024u);
v___x_1168_ = lean_nat_dec_le(v___x_1167_, v_prec_1145_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1152_ = v___x_1169_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1170_; 
v___x_1170_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1152_ = v___x_1170_;
goto v___jp_1151_;
}
v___jp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1153_ = lean_box(1);
v___x_1154_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__2));
v___x_1155_ = l_Nat_reprFast(v_lhs_1146_);
v___x_1156_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set_tag(v___x_1149_, 5);
lean_ctor_set(v___x_1149_, 1, v___x_1156_);
lean_ctor_set(v___x_1149_, 0, v___x_1154_);
v___x_1158_ = v___x_1149_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v___x_1153_);
v___x_1160_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_rhs_1147_);
v___x_1161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
lean_inc(v___y_1152_);
v___x_1162_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___y_1152_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = 0;
v___x_1164_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set_uint8(v___x_1164_, sizeof(void*)*1, v___x_1163_);
v___x_1165_ = l_Repr_addAppParen(v___x_1164_, v_prec_1145_);
return v___x_1165_;
}
}
}
}
case 1:
{
lean_object* v_lhs_1172_; lean_object* v_rhs_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1197_; 
v_lhs_1172_ = lean_ctor_get(v_x_1144_, 0);
v_rhs_1173_ = lean_ctor_get(v_x_1144_, 1);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_x_1144_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1175_ = v_x_1144_;
v_isShared_1176_ = v_isSharedCheck_1197_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_rhs_1173_);
lean_inc(v_lhs_1172_);
lean_dec(v_x_1144_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1197_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___y_1178_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = lean_unsigned_to_nat(1024u);
v___x_1194_ = lean_nat_dec_le(v___x_1193_, v_prec_1145_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1178_ = v___x_1195_;
goto v___jp_1177_;
}
else
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1178_ = v___x_1196_;
goto v___jp_1177_;
}
v___jp_1177_:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1179_ = lean_box(1);
v___x_1180_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__5));
v___x_1181_ = l_Nat_reprFast(v_lhs_1172_);
v___x_1182_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set_tag(v___x_1175_, 5);
lean_ctor_set(v___x_1175_, 1, v___x_1182_);
lean_ctor_set(v___x_1175_, 0, v___x_1180_);
v___x_1184_ = v___x_1175_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v___x_1179_);
v___x_1186_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_rhs_1173_);
v___x_1187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
lean_inc(v___y_1178_);
v___x_1188_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___y_1178_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = 0;
v___x_1190_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
lean_ctor_set_uint8(v___x_1190_, sizeof(void*)*1, v___x_1189_);
v___x_1191_ = l_Repr_addAppParen(v___x_1190_, v_prec_1145_);
return v___x_1191_;
}
}
}
}
case 2:
{
lean_object* v_lhs_1198_; lean_object* v_n_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1224_; 
v_lhs_1198_ = lean_ctor_get(v_x_1144_, 0);
v_n_1199_ = lean_ctor_get(v_x_1144_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_x_1144_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1201_ = v_x_1144_;
v_isShared_1202_ = v_isSharedCheck_1224_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_n_1199_);
lean_inc(v_lhs_1198_);
lean_dec(v_x_1144_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1224_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___y_1204_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = lean_unsigned_to_nat(1024u);
v___x_1221_ = lean_nat_dec_le(v___x_1220_, v_prec_1145_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1204_ = v___x_1222_;
goto v___jp_1203_;
}
else
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1204_ = v___x_1223_;
goto v___jp_1203_;
}
v___jp_1203_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1205_ = lean_box(1);
v___x_1206_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__8));
v___x_1207_ = l_Nat_reprFast(v_lhs_1198_);
v___x_1208_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set_tag(v___x_1201_, 5);
lean_ctor_set(v___x_1201_, 1, v___x_1208_);
lean_ctor_set(v___x_1201_, 0, v___x_1206_);
v___x_1210_ = v___x_1201_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v___x_1205_);
v___x_1212_ = l_Nat_reprFast(v_n_1199_);
v___x_1213_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
v___x_1214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1211_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
lean_inc(v___y_1204_);
v___x_1215_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___y_1204_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = 0;
v___x_1217_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1217_, 0, v___x_1215_);
lean_ctor_set_uint8(v___x_1217_, sizeof(void*)*1, v___x_1216_);
v___x_1218_ = l_Repr_addAppParen(v___x_1217_, v_prec_1145_);
return v___x_1218_;
}
}
}
}
case 3:
{
lean_object* v_lhs_1225_; lean_object* v_n_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1251_; 
v_lhs_1225_ = lean_ctor_get(v_x_1144_, 0);
v_n_1226_ = lean_ctor_get(v_x_1144_, 1);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_x_1144_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1228_ = v_x_1144_;
v_isShared_1229_ = v_isSharedCheck_1251_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_n_1226_);
lean_inc(v_lhs_1225_);
lean_dec(v_x_1144_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1251_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___y_1231_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1247_ = lean_unsigned_to_nat(1024u);
v___x_1248_ = lean_nat_dec_le(v___x_1247_, v_prec_1145_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1231_ = v___x_1249_;
goto v___jp_1230_;
}
else
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1231_ = v___x_1250_;
goto v___jp_1230_;
}
v___jp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1232_ = lean_box(1);
v___x_1233_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__11));
v___x_1234_ = l_Nat_reprFast(v_lhs_1225_);
v___x_1235_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set_tag(v___x_1228_, 5);
lean_ctor_set(v___x_1228_, 1, v___x_1235_);
lean_ctor_set(v___x_1228_, 0, v___x_1233_);
v___x_1237_ = v___x_1228_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v___x_1232_);
v___x_1239_ = l_Nat_reprFast(v_n_1226_);
v___x_1240_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
v___x_1241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1238_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
lean_inc(v___y_1231_);
v___x_1242_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___y_1231_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = 0;
v___x_1244_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set_uint8(v___x_1244_, sizeof(void*)*1, v___x_1243_);
v___x_1245_ = l_Repr_addAppParen(v___x_1244_, v_prec_1145_);
return v___x_1245_;
}
}
}
}
case 4:
{
lean_object* v_n_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1272_; 
v_n_1252_ = lean_ctor_get(v_x_1144_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_x_1144_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1254_ = v_x_1144_;
v_isShared_1255_ = v_isSharedCheck_1272_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_n_1252_);
lean_dec(v_x_1144_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1272_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___y_1257_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = lean_unsigned_to_nat(1024u);
v___x_1269_ = lean_nat_dec_le(v___x_1268_, v_prec_1145_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1257_ = v___x_1270_;
goto v___jp_1256_;
}
else
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1257_ = v___x_1271_;
goto v___jp_1256_;
}
v___jp_1256_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1258_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__14));
v___x_1259_ = l_Nat_reprFast(v_n_1252_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set_tag(v___x_1254_, 3);
lean_ctor_set(v___x_1254_, 0, v___x_1259_);
v___x_1261_ = v___x_1254_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1258_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
lean_inc(v___y_1257_);
v___x_1263_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___y_1257_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v___x_1264_ = 0;
v___x_1265_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set_uint8(v___x_1265_, sizeof(void*)*1, v___x_1264_);
v___x_1266_ = l_Repr_addAppParen(v___x_1265_, v_prec_1145_);
return v___x_1266_;
}
}
}
}
case 5:
{
lean_object* v_bvarIdx_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1293_; 
v_bvarIdx_1273_ = lean_ctor_get(v_x_1144_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_x_1144_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1275_ = v_x_1144_;
v_isShared_1276_ = v_isSharedCheck_1293_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_bvarIdx_1273_);
lean_dec(v_x_1144_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1293_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___y_1278_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1289_ = lean_unsigned_to_nat(1024u);
v___x_1290_ = lean_nat_dec_le(v___x_1289_, v_prec_1145_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1278_ = v___x_1291_;
goto v___jp_1277_;
}
else
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1278_ = v___x_1292_;
goto v___jp_1277_;
}
v___jp_1277_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1279_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__17));
v___x_1280_ = l_Nat_reprFast(v_bvarIdx_1273_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set_tag(v___x_1275_, 3);
lean_ctor_set(v___x_1275_, 0, v___x_1280_);
v___x_1282_ = v___x_1275_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1279_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
lean_inc(v___y_1278_);
v___x_1284_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___y_1278_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = 0;
v___x_1286_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set_uint8(v___x_1286_, sizeof(void*)*1, v___x_1285_);
v___x_1287_ = l_Repr_addAppParen(v___x_1286_, v_prec_1145_);
return v___x_1287_;
}
}
}
}
case 6:
{
lean_object* v_bvarIdx_1294_; uint8_t v_strict_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1319_; 
v_bvarIdx_1294_ = lean_ctor_get(v_x_1144_, 0);
v_strict_1295_ = lean_ctor_get_uint8(v_x_1144_, sizeof(void*)*1);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_x_1144_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1297_ = v_x_1144_;
v_isShared_1298_ = v_isSharedCheck_1319_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_bvarIdx_1294_);
lean_dec(v_x_1144_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1319_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___y_1300_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1315_ = lean_unsigned_to_nat(1024u);
v___x_1316_ = lean_nat_dec_le(v___x_1315_, v_prec_1145_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; 
v___x_1317_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1300_ = v___x_1317_;
goto v___jp_1299_;
}
else
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1300_ = v___x_1318_;
goto v___jp_1299_;
}
v___jp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; lean_object* v___x_1312_; 
v___x_1301_ = lean_box(1);
v___x_1302_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__20));
v___x_1303_ = l_Nat_reprFast(v_bvarIdx_1294_);
v___x_1304_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
v___x_1305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1302_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v___x_1301_);
v___x_1307_ = l_Bool_repr___redArg(v_strict_1295_);
v___x_1308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
lean_inc(v___y_1300_);
v___x_1309_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___y_1300_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = 0;
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1309_);
v___x_1312_ = v___x_1297_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1309_);
v___x_1312_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1313_; 
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*1, v___x_1310_);
v___x_1313_ = l_Repr_addAppParen(v___x_1312_, v_prec_1145_);
return v___x_1313_;
}
}
}
}
case 7:
{
lean_object* v_n_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1340_; 
v_n_1320_ = lean_ctor_get(v_x_1144_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_x_1144_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1322_ = v_x_1144_;
v_isShared_1323_ = v_isSharedCheck_1340_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_n_1320_);
lean_dec(v_x_1144_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1340_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___y_1325_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = lean_unsigned_to_nat(1024u);
v___x_1337_ = lean_nat_dec_le(v___x_1336_, v_prec_1145_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1325_ = v___x_1338_;
goto v___jp_1324_;
}
else
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1325_ = v___x_1339_;
goto v___jp_1324_;
}
v___jp_1324_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1326_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__23));
v___x_1327_ = l_Nat_reprFast(v_n_1320_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set_tag(v___x_1322_, 3);
lean_ctor_set(v___x_1322_, 0, v___x_1327_);
v___x_1329_ = v___x_1322_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1326_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
lean_inc(v___y_1325_);
v___x_1331_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___y_1325_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = 0;
v___x_1333_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*1, v___x_1332_);
v___x_1334_ = l_Repr_addAppParen(v___x_1333_, v_prec_1145_);
return v___x_1334_;
}
}
}
}
case 8:
{
lean_object* v_e_1341_; lean_object* v___y_1343_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v_e_1341_ = lean_ctor_get(v_x_1144_, 0);
lean_inc_ref(v_e_1341_);
lean_dec_ref_known(v_x_1144_, 1);
v___x_1352_ = lean_unsigned_to_nat(1024u);
v___x_1353_ = lean_nat_dec_le(v___x_1352_, v_prec_1145_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1343_ = v___x_1354_;
goto v___jp_1342_;
}
else
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1343_ = v___x_1355_;
goto v___jp_1342_;
}
v___jp_1342_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1344_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__26));
v___x_1345_ = lean_unsigned_to_nat(1024u);
v___x_1346_ = l_Lean_instReprExpr_repr(v_e_1341_, v___x_1345_);
v___x_1347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1344_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
lean_inc(v___y_1343_);
v___x_1348_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___y_1343_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = 0;
v___x_1350_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*1, v___x_1349_);
v___x_1351_ = l_Repr_addAppParen(v___x_1350_, v_prec_1145_);
return v___x_1351_;
}
}
case 9:
{
lean_object* v_e_1356_; lean_object* v___y_1358_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v_e_1356_ = lean_ctor_get(v_x_1144_, 0);
lean_inc_ref(v_e_1356_);
lean_dec_ref_known(v_x_1144_, 1);
v___x_1367_ = lean_unsigned_to_nat(1024u);
v___x_1368_ = lean_nat_dec_le(v___x_1367_, v_prec_1145_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1358_ = v___x_1369_;
goto v___jp_1357_;
}
else
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1358_ = v___x_1370_;
goto v___jp_1357_;
}
v___jp_1357_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1359_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__29));
v___x_1360_ = lean_unsigned_to_nat(1024u);
v___x_1361_ = l_Lean_instReprExpr_repr(v_e_1356_, v___x_1360_);
v___x_1362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1359_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
lean_inc(v___y_1358_);
v___x_1363_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___y_1358_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = 0;
v___x_1365_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1365_, 0, v___x_1363_);
lean_ctor_set_uint8(v___x_1365_, sizeof(void*)*1, v___x_1364_);
v___x_1366_ = l_Repr_addAppParen(v___x_1365_, v_prec_1145_);
return v___x_1366_;
}
}
default: 
{
lean_object* v_bvarIdx_1371_; uint8_t v_strict_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1396_; 
v_bvarIdx_1371_ = lean_ctor_get(v_x_1144_, 0);
v_strict_1372_ = lean_ctor_get_uint8(v_x_1144_, sizeof(void*)*1);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_x_1144_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1374_ = v_x_1144_;
v_isShared_1375_ = v_isSharedCheck_1396_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_bvarIdx_1371_);
lean_dec(v_x_1144_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1396_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___y_1377_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = lean_unsigned_to_nat(1024u);
v___x_1393_ = lean_nat_dec_le(v___x_1392_, v_prec_1145_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1377_ = v___x_1394_;
goto v___jp_1376_;
}
else
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1377_ = v___x_1395_;
goto v___jp_1376_;
}
v___jp_1376_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; lean_object* v___x_1389_; 
v___x_1378_ = lean_box(1);
v___x_1379_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__32));
v___x_1380_ = l_Nat_reprFast(v_bvarIdx_1371_);
v___x_1381_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
v___x_1382_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1379_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v___x_1378_);
v___x_1384_ = l_Bool_repr___redArg(v_strict_1372_);
v___x_1385_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1383_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
lean_inc(v___y_1377_);
v___x_1386_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___y_1377_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v___x_1387_ = 0;
if (v_isShared_1375_ == 0)
{
lean_ctor_set_tag(v___x_1374_, 6);
lean_ctor_set(v___x_1374_, 0, v___x_1386_);
v___x_1389_ = v___x_1374_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1386_);
v___x_1389_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; 
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*1, v___x_1387_);
v___x_1390_ = l_Repr_addAppParen(v___x_1389_, v_prec_1145_);
return v___x_1390_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___boxed(lean_object* v_x_1397_, lean_object* v_prec_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr(v_x_1397_, v_prec_1398_);
lean_dec(v_prec_1398_);
return v_res_1399_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(lean_object* v_x_1402_, lean_object* v_x_1403_){
_start:
{
lean_object* v_lhs_1405_; lean_object* v_rhs_1406_; lean_object* v_lhs_x27_1407_; lean_object* v_rhs_x27_1408_; lean_object* v_lhs_1412_; lean_object* v_n_1413_; lean_object* v_lhs_x27_1414_; lean_object* v_n_x27_1415_; lean_object* v_bvarIdx_1419_; uint8_t v_strict_1420_; lean_object* v_bvarIdx_x27_1421_; uint8_t v_strict_x27_1422_; lean_object* v___x_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
v___x_1424_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_1402_);
v___x_1425_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_1403_);
v___x_1426_ = lean_nat_dec_eq(v___x_1424_, v___x_1425_);
lean_dec(v___x_1425_);
lean_dec(v___x_1424_);
if (v___x_1426_ == 0)
{
return v___x_1426_;
}
else
{
switch(lean_obj_tag(v_x_1402_))
{
case 0:
{
lean_object* v_lhs_1427_; lean_object* v_rhs_1428_; lean_object* v_lhs_1429_; lean_object* v_rhs_1430_; 
v_lhs_1427_ = lean_ctor_get(v_x_1402_, 0);
v_rhs_1428_ = lean_ctor_get(v_x_1402_, 1);
v_lhs_1429_ = lean_ctor_get(v_x_1403_, 0);
v_rhs_1430_ = lean_ctor_get(v_x_1403_, 1);
v_lhs_1405_ = v_lhs_1427_;
v_rhs_1406_ = v_rhs_1428_;
v_lhs_x27_1407_ = v_lhs_1429_;
v_rhs_x27_1408_ = v_rhs_1430_;
goto v___jp_1404_;
}
case 1:
{
lean_object* v_lhs_1431_; lean_object* v_rhs_1432_; lean_object* v_lhs_1433_; lean_object* v_rhs_1434_; 
v_lhs_1431_ = lean_ctor_get(v_x_1402_, 0);
v_rhs_1432_ = lean_ctor_get(v_x_1402_, 1);
v_lhs_1433_ = lean_ctor_get(v_x_1403_, 0);
v_rhs_1434_ = lean_ctor_get(v_x_1403_, 1);
v_lhs_1405_ = v_lhs_1431_;
v_rhs_1406_ = v_rhs_1432_;
v_lhs_x27_1407_ = v_lhs_1433_;
v_rhs_x27_1408_ = v_rhs_1434_;
goto v___jp_1404_;
}
case 2:
{
lean_object* v_lhs_1435_; lean_object* v_n_1436_; lean_object* v_lhs_1437_; lean_object* v_n_1438_; 
v_lhs_1435_ = lean_ctor_get(v_x_1402_, 0);
v_n_1436_ = lean_ctor_get(v_x_1402_, 1);
v_lhs_1437_ = lean_ctor_get(v_x_1403_, 0);
v_n_1438_ = lean_ctor_get(v_x_1403_, 1);
v_lhs_1412_ = v_lhs_1435_;
v_n_1413_ = v_n_1436_;
v_lhs_x27_1414_ = v_lhs_1437_;
v_n_x27_1415_ = v_n_1438_;
goto v___jp_1411_;
}
case 3:
{
lean_object* v_lhs_1439_; lean_object* v_n_1440_; lean_object* v_lhs_1441_; lean_object* v_n_1442_; 
v_lhs_1439_ = lean_ctor_get(v_x_1402_, 0);
v_n_1440_ = lean_ctor_get(v_x_1402_, 1);
v_lhs_1441_ = lean_ctor_get(v_x_1403_, 0);
v_n_1442_ = lean_ctor_get(v_x_1403_, 1);
v_lhs_1412_ = v_lhs_1439_;
v_n_1413_ = v_n_1440_;
v_lhs_x27_1414_ = v_lhs_1441_;
v_n_x27_1415_ = v_n_1442_;
goto v___jp_1411_;
}
case 6:
{
lean_object* v_bvarIdx_1443_; uint8_t v_strict_1444_; lean_object* v_bvarIdx_1445_; uint8_t v_strict_1446_; 
v_bvarIdx_1443_ = lean_ctor_get(v_x_1402_, 0);
v_strict_1444_ = lean_ctor_get_uint8(v_x_1402_, sizeof(void*)*1);
v_bvarIdx_1445_ = lean_ctor_get(v_x_1403_, 0);
v_strict_1446_ = lean_ctor_get_uint8(v_x_1403_, sizeof(void*)*1);
v_bvarIdx_1419_ = v_bvarIdx_1443_;
v_strict_1420_ = v_strict_1444_;
v_bvarIdx_x27_1421_ = v_bvarIdx_1445_;
v_strict_x27_1422_ = v_strict_1446_;
goto v___jp_1418_;
}
case 8:
{
lean_object* v_e_1447_; lean_object* v_e_1448_; uint8_t v___x_1449_; 
v_e_1447_ = lean_ctor_get(v_x_1402_, 0);
v_e_1448_ = lean_ctor_get(v_x_1403_, 0);
v___x_1449_ = lean_expr_eqv(v_e_1447_, v_e_1448_);
return v___x_1449_;
}
case 9:
{
lean_object* v_e_1450_; lean_object* v_e_1451_; uint8_t v___x_1452_; 
v_e_1450_ = lean_ctor_get(v_x_1402_, 0);
v_e_1451_ = lean_ctor_get(v_x_1403_, 0);
v___x_1452_ = lean_expr_eqv(v_e_1450_, v_e_1451_);
return v___x_1452_;
}
case 10:
{
lean_object* v_bvarIdx_1453_; uint8_t v_strict_1454_; lean_object* v_bvarIdx_1455_; uint8_t v_strict_1456_; 
v_bvarIdx_1453_ = lean_ctor_get(v_x_1402_, 0);
v_strict_1454_ = lean_ctor_get_uint8(v_x_1402_, sizeof(void*)*1);
v_bvarIdx_1455_ = lean_ctor_get(v_x_1403_, 0);
v_strict_1456_ = lean_ctor_get_uint8(v_x_1403_, sizeof(void*)*1);
v_bvarIdx_1419_ = v_bvarIdx_1453_;
v_strict_1420_ = v_strict_1454_;
v_bvarIdx_x27_1421_ = v_bvarIdx_1455_;
v_strict_x27_1422_ = v_strict_1456_;
goto v___jp_1418_;
}
default: 
{
lean_object* v_n_1457_; lean_object* v_n_1458_; uint8_t v___x_1459_; 
v_n_1457_ = lean_ctor_get(v_x_1402_, 0);
v_n_1458_ = lean_ctor_get(v_x_1403_, 0);
v___x_1459_ = lean_nat_dec_eq(v_n_1457_, v_n_1458_);
return v___x_1459_;
}
}
}
v___jp_1404_:
{
uint8_t v___x_1409_; 
v___x_1409_ = lean_nat_dec_eq(v_lhs_1405_, v_lhs_x27_1407_);
if (v___x_1409_ == 0)
{
return v___x_1409_;
}
else
{
uint8_t v___x_1410_; 
v___x_1410_ = l_Lean_Meta_Grind_instBEqCnstrRHS_beq(v_rhs_1406_, v_rhs_x27_1408_);
return v___x_1410_;
}
}
v___jp_1411_:
{
uint8_t v___x_1416_; 
v___x_1416_ = lean_nat_dec_eq(v_lhs_1412_, v_lhs_x27_1414_);
if (v___x_1416_ == 0)
{
return v___x_1416_;
}
else
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_nat_dec_eq(v_n_1413_, v_n_x27_1415_);
return v___x_1417_;
}
}
v___jp_1418_:
{
uint8_t v___x_1423_; 
v___x_1423_ = lean_nat_dec_eq(v_bvarIdx_1419_, v_bvarIdx_x27_1421_);
if (v___x_1423_ == 0)
{
return v___x_1423_;
}
else
{
if (v_strict_1420_ == 0)
{
if (v_strict_x27_1422_ == 0)
{
return v___x_1423_;
}
else
{
return v_strict_1420_;
}
}
else
{
return v_strict_x27_1422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq___boxed(lean_object* v_x_1460_, lean_object* v_x_1461_){
_start:
{
uint8_t v_res_1462_; lean_object* v_r_1463_; 
v_res_1462_ = l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(v_x_1460_, v_x_1461_);
lean_dec_ref(v_x_1461_);
lean_dec_ref(v_x_1460_);
v_r_1463_ = lean_box(v_res_1462_);
return v_r_1463_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0(void){
_start:
{
uint8_t v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1466_ = 0;
v___x_1467_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default));
v___x_1468_ = l_Lean_Meta_Grind_instInhabitedOrigin_default;
v___x_1469_ = lean_box(0);
v___x_1470_ = lean_unsigned_to_nat(0u);
v___x_1471_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_1472_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_1473_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v___x_1471_);
lean_ctor_set(v___x_1473_, 2, v___x_1470_);
lean_ctor_set(v___x_1473_, 3, v___x_1469_);
lean_ctor_set(v___x_1473_, 4, v___x_1469_);
lean_ctor_set(v___x_1473_, 5, v___x_1468_);
lean_ctor_set(v___x_1473_, 6, v___x_1467_);
lean_ctor_set(v___x_1473_, 7, v___x_1469_);
lean_ctor_set_uint8(v___x_1473_, sizeof(void*)*8, v___x_1466_);
return v___x_1473_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default(void){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0, &l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0);
return v___x_1474_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem(void){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default;
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0(lean_object* v_thm_1476_){
_start:
{
lean_object* v_symbols_1477_; 
v_symbols_1477_ = lean_ctor_get(v_thm_1476_, 4);
lean_inc(v_symbols_1477_);
return v_symbols_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0___boxed(lean_object* v_thm_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0(v_thm_1478_);
lean_dec_ref(v_thm_1478_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__1(lean_object* v_thm_1480_, lean_object* v_symbols_1481_){
_start:
{
lean_object* v_levelParams_1482_; lean_object* v_proof_1483_; lean_object* v_numParams_1484_; lean_object* v_patterns_1485_; lean_object* v_origin_1486_; lean_object* v_kind_1487_; uint8_t v_minIndexable_1488_; lean_object* v_cnstrs_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
v_levelParams_1482_ = lean_ctor_get(v_thm_1480_, 0);
v_proof_1483_ = lean_ctor_get(v_thm_1480_, 1);
v_numParams_1484_ = lean_ctor_get(v_thm_1480_, 2);
v_patterns_1485_ = lean_ctor_get(v_thm_1480_, 3);
v_origin_1486_ = lean_ctor_get(v_thm_1480_, 5);
v_kind_1487_ = lean_ctor_get(v_thm_1480_, 6);
v_minIndexable_1488_ = lean_ctor_get_uint8(v_thm_1480_, sizeof(void*)*8);
v_cnstrs_1489_ = lean_ctor_get(v_thm_1480_, 7);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_thm_1480_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; 
v_unused_1497_ = lean_ctor_get(v_thm_1480_, 4);
lean_dec(v_unused_1497_);
v___x_1491_ = v_thm_1480_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_cnstrs_1489_);
lean_inc(v_kind_1487_);
lean_inc(v_origin_1486_);
lean_inc(v_patterns_1485_);
lean_inc(v_numParams_1484_);
lean_inc(v_proof_1483_);
lean_inc(v_levelParams_1482_);
lean_dec(v_thm_1480_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 4, v_symbols_1481_);
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_levelParams_1482_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_proof_1483_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_numParams_1484_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v_patterns_1485_);
lean_ctor_set(v_reuseFailAlloc_1495_, 4, v_symbols_1481_);
lean_ctor_set(v_reuseFailAlloc_1495_, 5, v_origin_1486_);
lean_ctor_set(v_reuseFailAlloc_1495_, 6, v_kind_1487_);
lean_ctor_set(v_reuseFailAlloc_1495_, 7, v_cnstrs_1489_);
lean_ctor_set_uint8(v_reuseFailAlloc_1495_, sizeof(void*)*8, v_minIndexable_1488_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2(lean_object* v_thm_1498_){
_start:
{
lean_object* v_origin_1499_; 
v_origin_1499_ = lean_ctor_get(v_thm_1498_, 5);
lean_inc_ref(v_origin_1499_);
return v_origin_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2___boxed(lean_object* v_thm_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2(v_thm_1500_);
lean_dec_ref(v_thm_1500_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3(lean_object* v_thm_1502_){
_start:
{
lean_object* v_proof_1503_; 
v_proof_1503_ = lean_ctor_get(v_thm_1502_, 1);
lean_inc_ref(v_proof_1503_);
return v_proof_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3___boxed(lean_object* v_thm_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3(v_thm_1504_);
lean_dec_ref(v_thm_1504_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4(lean_object* v_thm_1506_){
_start:
{
lean_object* v_levelParams_1507_; 
v_levelParams_1507_ = lean_ctor_get(v_thm_1506_, 0);
lean_inc_ref(v_levelParams_1507_);
return v_levelParams_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4___boxed(lean_object* v_thm_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4(v_thm_1508_);
lean_dec_ref(v_thm_1508_);
return v_res_1509_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1522_ = l_Lean_Meta_Grind_instInhabitedOrigin_default;
v___x_1523_ = lean_box(0);
v___x_1524_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_1525_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_1526_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v___x_1524_);
lean_ctor_set(v___x_1526_, 2, v___x_1523_);
lean_ctor_set(v___x_1526_, 3, v___x_1522_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default(void){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0, &l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0);
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem(void){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default;
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0(lean_object* v_thm_1529_){
_start:
{
lean_object* v_symbols_1530_; 
v_symbols_1530_ = lean_ctor_get(v_thm_1529_, 2);
lean_inc(v_symbols_1530_);
return v_symbols_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0___boxed(lean_object* v_thm_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0(v_thm_1531_);
lean_dec_ref(v_thm_1531_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__1(lean_object* v_thm_1533_, lean_object* v_symbols_1534_){
_start:
{
lean_object* v_levelParams_1535_; lean_object* v_proof_1536_; lean_object* v_origin_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
v_levelParams_1535_ = lean_ctor_get(v_thm_1533_, 0);
v_proof_1536_ = lean_ctor_get(v_thm_1533_, 1);
v_origin_1537_ = lean_ctor_get(v_thm_1533_, 3);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_thm_1533_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; 
v_unused_1545_ = lean_ctor_get(v_thm_1533_, 2);
lean_dec(v_unused_1545_);
v___x_1539_ = v_thm_1533_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_origin_1537_);
lean_inc(v_proof_1536_);
lean_inc(v_levelParams_1535_);
lean_dec(v_thm_1533_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 2, v_symbols_1534_);
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_levelParams_1535_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_proof_1536_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_symbols_1534_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v_origin_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2(lean_object* v_thm_1546_){
_start:
{
lean_object* v_origin_1547_; 
v_origin_1547_ = lean_ctor_get(v_thm_1546_, 3);
lean_inc_ref(v_origin_1547_);
return v_origin_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2___boxed(lean_object* v_thm_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2(v_thm_1548_);
lean_dec_ref(v_thm_1548_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3(lean_object* v_thm_1550_){
_start:
{
lean_object* v_proof_1551_; 
v_proof_1551_ = lean_ctor_get(v_thm_1550_, 1);
lean_inc_ref(v_proof_1551_);
return v_proof_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3___boxed(lean_object* v_thm_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3(v_thm_1552_);
lean_dec_ref(v_thm_1552_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4(lean_object* v_thm_1554_){
_start:
{
lean_object* v_levelParams_1555_; 
v_levelParams_1555_ = lean_ctor_get(v_thm_1554_, 0);
lean_inc_ref(v_levelParams_1555_);
return v_levelParams_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4___boxed(lean_object* v_thm_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4(v_thm_1556_);
lean_dec_ref(v_thm_1556_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorIdx(lean_object* v_x_1570_){
_start:
{
switch(lean_obj_tag(v_x_1570_))
{
case 0:
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_unsigned_to_nat(0u);
return v___x_1571_;
}
case 1:
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_unsigned_to_nat(1u);
return v___x_1572_;
}
case 2:
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_unsigned_to_nat(2u);
return v___x_1573_;
}
case 3:
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_unsigned_to_nat(3u);
return v___x_1574_;
}
default: 
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_unsigned_to_nat(4u);
return v___x_1575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorIdx___boxed(lean_object* v_x_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Lean_Meta_Grind_Entry_ctorIdx(v_x_1576_);
lean_dec_ref(v_x_1576_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim___redArg(lean_object* v_t_1578_, lean_object* v_k_1579_){
_start:
{
switch(lean_obj_tag(v_t_1578_))
{
case 2:
{
lean_object* v_declName_1580_; uint8_t v_eager_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v_declName_1580_ = lean_ctor_get(v_t_1578_, 0);
lean_inc(v_declName_1580_);
v_eager_1581_ = lean_ctor_get_uint8(v_t_1578_, sizeof(void*)*1);
lean_dec_ref_known(v_t_1578_, 1);
v___x_1582_ = lean_box(v_eager_1581_);
v___x_1583_ = lean_apply_2(v_k_1579_, v_declName_1580_, v___x_1582_);
return v___x_1583_;
}
case 3:
{
lean_object* v_thm_1584_; lean_object* v___x_1585_; 
v_thm_1584_ = lean_ctor_get(v_t_1578_, 0);
lean_inc_ref(v_thm_1584_);
lean_dec_ref_known(v_t_1578_, 1);
v___x_1585_ = lean_apply_1(v_k_1579_, v_thm_1584_);
return v___x_1585_;
}
case 4:
{
lean_object* v_thm_1586_; lean_object* v___x_1587_; 
v_thm_1586_ = lean_ctor_get(v_t_1578_, 0);
lean_inc_ref(v_thm_1586_);
lean_dec_ref_known(v_t_1578_, 1);
v___x_1587_ = lean_apply_1(v_k_1579_, v_thm_1586_);
return v___x_1587_;
}
default: 
{
lean_object* v_declName_1588_; lean_object* v___x_1589_; 
v_declName_1588_ = lean_ctor_get(v_t_1578_, 0);
lean_inc(v_declName_1588_);
lean_dec_ref(v_t_1578_);
v___x_1589_ = lean_apply_1(v_k_1579_, v_declName_1588_);
return v___x_1589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim(lean_object* v_motive_1590_, lean_object* v_ctorIdx_1591_, lean_object* v_t_1592_, lean_object* v_h_1593_, lean_object* v_k_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1592_, v_k_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim___boxed(lean_object* v_motive_1596_, lean_object* v_ctorIdx_1597_, lean_object* v_t_1598_, lean_object* v_h_1599_, lean_object* v_k_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_Meta_Grind_Entry_ctorElim(v_motive_1596_, v_ctorIdx_1597_, v_t_1598_, v_h_1599_, v_k_1600_);
lean_dec(v_ctorIdx_1597_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ext_elim___redArg(lean_object* v_t_1602_, lean_object* v_ext_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1602_, v_ext_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ext_elim(lean_object* v_motive_1605_, lean_object* v_t_1606_, lean_object* v_h_1607_, lean_object* v_ext_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1606_, v_ext_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_funCC_elim___redArg(lean_object* v_t_1610_, lean_object* v_funCC_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1610_, v_funCC_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_funCC_elim(lean_object* v_motive_1613_, lean_object* v_t_1614_, lean_object* v_h_1615_, lean_object* v_funCC_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1614_, v_funCC_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_cases_elim___redArg(lean_object* v_t_1618_, lean_object* v_cases_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1618_, v_cases_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_cases_elim(lean_object* v_motive_1621_, lean_object* v_t_1622_, lean_object* v_h_1623_, lean_object* v_cases_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1622_, v_cases_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ematch_elim___redArg(lean_object* v_t_1626_, lean_object* v_ematch_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1626_, v_ematch_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ematch_elim(lean_object* v_motive_1629_, lean_object* v_t_1630_, lean_object* v_h_1631_, lean_object* v_ematch_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1630_, v_ematch_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_inj_elim___redArg(lean_object* v_t_1634_, lean_object* v_inj_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1634_, v_inj_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_inj_elim(lean_object* v_motive_1637_, lean_object* v_t_1638_, lean_object* v_h_1639_, lean_object* v_inj_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1638_, v_inj_1640_);
return v___x_1641_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1646_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0);
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0(lean_object* v_00_u03b2_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1);
return v___x_1650_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0(lean_box(0));
return v___x_1651_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1(void){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_Meta_Grind_Theorems_mkEmpty(lean_box(0));
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1653_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1);
v___x_1654_ = l_Lean_NameSet_empty;
v___x_1655_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0);
v___x_1656_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1, &l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1);
v___x_1657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
lean_ctor_set(v___x_1657_, 1, v___x_1655_);
lean_ctor_set(v___x_1657_, 2, v___x_1654_);
lean_ctor_set(v___x_1657_, 3, v___x_1653_);
lean_ctor_set(v___x_1657_, 4, v___x_1653_);
return v___x_1657_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default(void){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2);
return v___x_1658_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState(void){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_x_1660_, lean_object* v_x_1661_, lean_object* v_x_1662_, lean_object* v_x_1663_){
_start:
{
lean_object* v_ks_1664_; lean_object* v_vs_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1691_; 
v_ks_1664_ = lean_ctor_get(v_x_1660_, 0);
v_vs_1665_ = lean_ctor_get(v_x_1660_, 1);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_x_1660_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1667_ = v_x_1660_;
v_isShared_1668_ = v_isSharedCheck_1691_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_vs_1665_);
lean_inc(v_ks_1664_);
lean_dec(v_x_1660_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1691_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; uint8_t v___x_1670_; 
v___x_1669_ = lean_array_get_size(v_ks_1664_);
v___x_1670_ = lean_nat_dec_lt(v_x_1661_, v___x_1669_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1674_; 
lean_dec(v_x_1661_);
v___x_1671_ = lean_array_push(v_ks_1664_, v_x_1662_);
v___x_1672_ = lean_array_push(v_vs_1665_, v_x_1663_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 1, v___x_1672_);
lean_ctor_set(v___x_1667_, 0, v___x_1671_);
v___x_1674_ = v___x_1667_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
else
{
lean_object* v_k_x27_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v_k_x27_1676_ = lean_array_fget_borrowed(v_ks_1664_, v_x_1661_);
v___x_1677_ = l_Lean_Meta_Grind_Origin_key(v_x_1662_);
v___x_1678_ = l_Lean_Meta_Grind_Origin_key(v_k_x27_1676_);
v___x_1679_ = lean_name_eq(v___x_1677_, v___x_1678_);
lean_dec(v___x_1678_);
lean_dec(v___x_1677_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1681_; 
if (v_isShared_1668_ == 0)
{
v___x_1681_ = v___x_1667_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_ks_1664_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_vs_1665_);
v___x_1681_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = lean_unsigned_to_nat(1u);
v___x_1683_ = lean_nat_add(v_x_1661_, v___x_1682_);
lean_dec(v_x_1661_);
v_x_1660_ = v___x_1681_;
v_x_1661_ = v___x_1683_;
goto _start;
}
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1686_ = lean_array_fset(v_ks_1664_, v_x_1661_, v_x_1662_);
v___x_1687_ = lean_array_fset(v_vs_1665_, v_x_1661_, v_x_1663_);
lean_dec(v_x_1661_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 1, v___x_1687_);
lean_ctor_set(v___x_1667_, 0, v___x_1686_);
v___x_1689_ = v___x_1667_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_n_1692_, lean_object* v_k_1693_, lean_object* v_v_1694_){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = lean_unsigned_to_nat(0u);
v___x_1696_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(v_n_1692_, v___x_1695_, v_k_1693_, v_v_1694_);
return v___x_1696_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1698_, size_t v_x_1699_, size_t v_x_1700_, lean_object* v_x_1701_, lean_object* v_x_1702_){
_start:
{
if (lean_obj_tag(v_x_1698_) == 0)
{
lean_object* v_es_1703_; size_t v___x_1704_; size_t v___x_1705_; lean_object* v_j_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; 
v_es_1703_ = lean_ctor_get(v_x_1698_, 0);
v___x_1704_ = ((size_t)31ULL);
v___x_1705_ = lean_usize_land(v_x_1699_, v___x_1704_);
v_j_1706_ = lean_usize_to_nat(v___x_1705_);
v___x_1707_ = lean_array_get_size(v_es_1703_);
v___x_1708_ = lean_nat_dec_lt(v_j_1706_, v___x_1707_);
if (v___x_1708_ == 0)
{
lean_dec(v_j_1706_);
lean_dec(v_x_1702_);
lean_dec_ref(v_x_1701_);
return v_x_1698_;
}
else
{
lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1749_; 
lean_inc_ref(v_es_1703_);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1749_ == 0)
{
lean_object* v_unused_1750_; 
v_unused_1750_ = lean_ctor_get(v_x_1698_, 0);
lean_dec(v_unused_1750_);
v___x_1710_ = v_x_1698_;
v_isShared_1711_ = v_isSharedCheck_1749_;
goto v_resetjp_1709_;
}
else
{
lean_dec(v_x_1698_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1749_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v_v_1712_; lean_object* v___x_1713_; lean_object* v_xs_x27_1714_; lean_object* v___y_1716_; 
v_v_1712_ = lean_array_fget(v_es_1703_, v_j_1706_);
v___x_1713_ = lean_box(0);
v_xs_x27_1714_ = lean_array_fset(v_es_1703_, v_j_1706_, v___x_1713_);
switch(lean_obj_tag(v_v_1712_))
{
case 0:
{
lean_object* v_key_1721_; lean_object* v_val_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1734_; 
v_key_1721_ = lean_ctor_get(v_v_1712_, 0);
v_val_1722_ = lean_ctor_get(v_v_1712_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_v_1712_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1724_ = v_v_1712_;
v_isShared_1725_ = v_isSharedCheck_1734_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_val_1722_);
lean_inc(v_key_1721_);
lean_dec(v_v_1712_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1734_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1726_ = l_Lean_Meta_Grind_Origin_key(v_x_1701_);
v___x_1727_ = l_Lean_Meta_Grind_Origin_key(v_key_1721_);
v___x_1728_ = lean_name_eq(v___x_1726_, v___x_1727_);
lean_dec(v___x_1727_);
lean_dec(v___x_1726_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_del_object(v___x_1724_);
v___x_1729_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1721_, v_val_1722_, v_x_1701_, v_x_1702_);
v___x_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
v___y_1716_ = v___x_1730_;
goto v___jp_1715_;
}
else
{
lean_object* v___x_1732_; 
lean_dec(v_val_1722_);
lean_dec(v_key_1721_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v_x_1702_);
lean_ctor_set(v___x_1724_, 0, v_x_1701_);
v___x_1732_ = v___x_1724_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_x_1701_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_x_1702_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
v___y_1716_ = v___x_1732_;
goto v___jp_1715_;
}
}
}
}
case 1:
{
lean_object* v_node_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1747_; 
v_node_1735_ = lean_ctor_get(v_v_1712_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_v_1712_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1737_ = v_v_1712_;
v_isShared_1738_ = v_isSharedCheck_1747_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_node_1735_);
lean_dec(v_v_1712_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1747_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
size_t v___x_1739_; size_t v___x_1740_; size_t v___x_1741_; size_t v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1739_ = ((size_t)5ULL);
v___x_1740_ = lean_usize_shift_right(v_x_1699_, v___x_1739_);
v___x_1741_ = ((size_t)1ULL);
v___x_1742_ = lean_usize_add(v_x_1700_, v___x_1741_);
v___x_1743_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_node_1735_, v___x_1740_, v___x_1742_, v_x_1701_, v_x_1702_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v___x_1743_);
v___x_1745_ = v___x_1737_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
v___y_1716_ = v___x_1745_;
goto v___jp_1715_;
}
}
}
default: 
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v_x_1701_);
lean_ctor_set(v___x_1748_, 1, v_x_1702_);
v___y_1716_ = v___x_1748_;
goto v___jp_1715_;
}
}
v___jp_1715_:
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1717_ = lean_array_fset(v_xs_x27_1714_, v_j_1706_, v___y_1716_);
lean_dec(v_j_1706_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1717_);
v___x_1719_ = v___x_1710_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
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
}
else
{
lean_object* v_ks_1751_; lean_object* v_vs_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1772_; 
v_ks_1751_ = lean_ctor_get(v_x_1698_, 0);
v_vs_1752_ = lean_ctor_get(v_x_1698_, 1);
v_isSharedCheck_1772_ = !lean_is_exclusive(v_x_1698_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1754_ = v_x_1698_;
v_isShared_1755_ = v_isSharedCheck_1772_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_vs_1752_);
lean_inc(v_ks_1751_);
lean_dec(v_x_1698_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1772_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_ks_1751_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_vs_1752_);
v___x_1757_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v_newNode_1758_; uint8_t v___y_1760_; size_t v___x_1766_; uint8_t v___x_1767_; 
v_newNode_1758_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(v___x_1757_, v_x_1701_, v_x_1702_);
v___x_1766_ = ((size_t)7ULL);
v___x_1767_ = lean_usize_dec_le(v___x_1766_, v_x_1700_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1768_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1758_);
v___x_1769_ = lean_unsigned_to_nat(4u);
v___x_1770_ = lean_nat_dec_lt(v___x_1768_, v___x_1769_);
lean_dec(v___x_1768_);
v___y_1760_ = v___x_1770_;
goto v___jp_1759_;
}
else
{
v___y_1760_ = v___x_1767_;
goto v___jp_1759_;
}
v___jp_1759_:
{
if (v___y_1760_ == 0)
{
lean_object* v_ks_1761_; lean_object* v_vs_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v_ks_1761_ = lean_ctor_get(v_newNode_1758_, 0);
lean_inc_ref(v_ks_1761_);
v_vs_1762_ = lean_ctor_get(v_newNode_1758_, 1);
lean_inc_ref(v_vs_1762_);
lean_dec_ref(v_newNode_1758_);
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0);
v___x_1765_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_x_1700_, v_ks_1761_, v_vs_1762_, v___x_1763_, v___x_1764_);
lean_dec_ref(v_vs_1762_);
lean_dec_ref(v_ks_1761_);
return v___x_1765_;
}
else
{
return v_newNode_1758_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(size_t v_depth_1773_, lean_object* v_keys_1774_, lean_object* v_vals_1775_, lean_object* v_i_1776_, lean_object* v_entries_1777_){
_start:
{
lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = lean_array_get_size(v_keys_1774_);
v___x_1779_ = lean_nat_dec_lt(v_i_1776_, v___x_1778_);
if (v___x_1779_ == 0)
{
lean_dec(v_i_1776_);
return v_entries_1777_;
}
else
{
lean_object* v_k_1780_; lean_object* v_v_1781_; uint64_t v___y_1783_; lean_object* v___x_1794_; 
v_k_1780_ = lean_array_fget_borrowed(v_keys_1774_, v_i_1776_);
v_v_1781_ = lean_array_fget_borrowed(v_vals_1775_, v_i_1776_);
v___x_1794_ = l_Lean_Meta_Grind_Origin_key(v_k_1780_);
if (lean_obj_tag(v___x_1794_) == 0)
{
uint64_t v___x_1795_; 
v___x_1795_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1783_ = v___x_1795_;
goto v___jp_1782_;
}
else
{
uint64_t v_hash_1796_; 
v_hash_1796_ = lean_ctor_get_uint64(v___x_1794_, sizeof(void*)*2);
lean_dec(v___x_1794_);
v___y_1783_ = v_hash_1796_;
goto v___jp_1782_;
}
v___jp_1782_:
{
size_t v_h_1784_; size_t v___x_1785_; lean_object* v___x_1786_; size_t v___x_1787_; size_t v___x_1788_; size_t v___x_1789_; size_t v_h_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v_h_1784_ = lean_uint64_to_usize(v___y_1783_);
v___x_1785_ = ((size_t)5ULL);
v___x_1786_ = lean_unsigned_to_nat(1u);
v___x_1787_ = ((size_t)1ULL);
v___x_1788_ = lean_usize_sub(v_depth_1773_, v___x_1787_);
v___x_1789_ = lean_usize_mul(v___x_1785_, v___x_1788_);
v_h_1790_ = lean_usize_shift_right(v_h_1784_, v___x_1789_);
v___x_1791_ = lean_nat_add(v_i_1776_, v___x_1786_);
lean_dec(v_i_1776_);
lean_inc(v_v_1781_);
lean_inc(v_k_1780_);
v___x_1792_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_entries_1777_, v_h_1790_, v_depth_1773_, v_k_1780_, v_v_1781_);
v_i_1776_ = v___x_1791_;
v_entries_1777_ = v___x_1792_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_depth_1797_, lean_object* v_keys_1798_, lean_object* v_vals_1799_, lean_object* v_i_1800_, lean_object* v_entries_1801_){
_start:
{
size_t v_depth_boxed_1802_; lean_object* v_res_1803_; 
v_depth_boxed_1802_ = lean_unbox_usize(v_depth_1797_);
lean_dec(v_depth_1797_);
v_res_1803_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_depth_boxed_1802_, v_keys_1798_, v_vals_1799_, v_i_1800_, v_entries_1801_);
lean_dec_ref(v_vals_1799_);
lean_dec_ref(v_keys_1798_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_x_1804_, lean_object* v_x_1805_, lean_object* v_x_1806_, lean_object* v_x_1807_, lean_object* v_x_1808_){
_start:
{
size_t v_x_1244__boxed_1809_; size_t v_x_1245__boxed_1810_; lean_object* v_res_1811_; 
v_x_1244__boxed_1809_ = lean_unbox_usize(v_x_1805_);
lean_dec(v_x_1805_);
v_x_1245__boxed_1810_ = lean_unbox_usize(v_x_1806_);
lean_dec(v_x_1806_);
v_res_1811_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_1804_, v_x_1244__boxed_1809_, v_x_1245__boxed_1810_, v_x_1807_, v_x_1808_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(lean_object* v_x_1812_, lean_object* v_x_1813_, lean_object* v_x_1814_){
_start:
{
uint64_t v___y_1816_; lean_object* v___x_1820_; 
v___x_1820_ = l_Lean_Meta_Grind_Origin_key(v_x_1813_);
if (lean_obj_tag(v___x_1820_) == 0)
{
uint64_t v___x_1821_; 
v___x_1821_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1816_ = v___x_1821_;
goto v___jp_1815_;
}
else
{
uint64_t v_hash_1822_; 
v_hash_1822_ = lean_ctor_get_uint64(v___x_1820_, sizeof(void*)*2);
lean_dec(v___x_1820_);
v___y_1816_ = v_hash_1822_;
goto v___jp_1815_;
}
v___jp_1815_:
{
size_t v___x_1817_; size_t v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = lean_uint64_to_usize(v___y_1816_);
v___x_1818_ = ((size_t)1ULL);
v___x_1819_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_1812_, v___x_1817_, v___x_1818_, v_x_1813_, v_x_1814_);
return v___x_1819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(lean_object* v_keys_1823_, lean_object* v_vals_1824_, lean_object* v_i_1825_, lean_object* v_k_1826_){
_start:
{
lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1827_ = lean_array_get_size(v_keys_1823_);
v___x_1828_ = lean_nat_dec_lt(v_i_1825_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; 
lean_dec(v_i_1825_);
v___x_1829_ = lean_box(0);
return v___x_1829_;
}
else
{
lean_object* v_k_x27_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v_k_x27_1830_ = lean_array_fget_borrowed(v_keys_1823_, v_i_1825_);
v___x_1831_ = l_Lean_Meta_Grind_Origin_key(v_k_1826_);
v___x_1832_ = l_Lean_Meta_Grind_Origin_key(v_k_x27_1830_);
v___x_1833_ = lean_name_eq(v___x_1831_, v___x_1832_);
lean_dec(v___x_1832_);
lean_dec(v___x_1831_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = lean_unsigned_to_nat(1u);
v___x_1835_ = lean_nat_add(v_i_1825_, v___x_1834_);
lean_dec(v_i_1825_);
v_i_1825_ = v___x_1835_;
goto _start;
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = lean_array_fget_borrowed(v_vals_1824_, v_i_1825_);
lean_dec(v_i_1825_);
lean_inc(v___x_1837_);
v___x_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
return v___x_1838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg___boxed(lean_object* v_keys_1839_, lean_object* v_vals_1840_, lean_object* v_i_1841_, lean_object* v_k_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_keys_1839_, v_vals_1840_, v_i_1841_, v_k_1842_);
lean_dec_ref(v_k_1842_);
lean_dec_ref(v_vals_1840_);
lean_dec_ref(v_keys_1839_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(lean_object* v_x_1844_, size_t v_x_1845_, lean_object* v_x_1846_){
_start:
{
if (lean_obj_tag(v_x_1844_) == 0)
{
lean_object* v_es_1847_; lean_object* v___x_1848_; size_t v___x_1849_; size_t v___x_1850_; lean_object* v_j_1851_; lean_object* v___x_1852_; 
v_es_1847_ = lean_ctor_get(v_x_1844_, 0);
v___x_1848_ = lean_box(2);
v___x_1849_ = ((size_t)31ULL);
v___x_1850_ = lean_usize_land(v_x_1845_, v___x_1849_);
v_j_1851_ = lean_usize_to_nat(v___x_1850_);
v___x_1852_ = lean_array_get_borrowed(v___x_1848_, v_es_1847_, v_j_1851_);
lean_dec(v_j_1851_);
switch(lean_obj_tag(v___x_1852_))
{
case 0:
{
lean_object* v_key_1853_; lean_object* v_val_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; 
v_key_1853_ = lean_ctor_get(v___x_1852_, 0);
v_val_1854_ = lean_ctor_get(v___x_1852_, 1);
v___x_1855_ = l_Lean_Meta_Grind_Origin_key(v_x_1846_);
v___x_1856_ = l_Lean_Meta_Grind_Origin_key(v_key_1853_);
v___x_1857_ = lean_name_eq(v___x_1855_, v___x_1856_);
lean_dec(v___x_1856_);
lean_dec(v___x_1855_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; 
v___x_1858_ = lean_box(0);
return v___x_1858_;
}
else
{
lean_object* v___x_1859_; 
lean_inc(v_val_1854_);
v___x_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_val_1854_);
return v___x_1859_;
}
}
case 1:
{
lean_object* v_node_1860_; size_t v___x_1861_; size_t v___x_1862_; 
v_node_1860_ = lean_ctor_get(v___x_1852_, 0);
v___x_1861_ = ((size_t)5ULL);
v___x_1862_ = lean_usize_shift_right(v_x_1845_, v___x_1861_);
v_x_1844_ = v_node_1860_;
v_x_1845_ = v___x_1862_;
goto _start;
}
default: 
{
lean_object* v___x_1864_; 
v___x_1864_ = lean_box(0);
return v___x_1864_;
}
}
}
else
{
lean_object* v_ks_1865_; lean_object* v_vs_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v_ks_1865_ = lean_ctor_get(v_x_1844_, 0);
v_vs_1866_ = lean_ctor_get(v_x_1844_, 1);
v___x_1867_ = lean_unsigned_to_nat(0u);
v___x_1868_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_ks_1865_, v_vs_1866_, v___x_1867_, v_x_1846_);
return v___x_1868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_x_1869_, lean_object* v_x_1870_, lean_object* v_x_1871_){
_start:
{
size_t v_x_1452__boxed_1872_; lean_object* v_res_1873_; 
v_x_1452__boxed_1872_ = lean_unbox_usize(v_x_1870_);
lean_dec(v_x_1870_);
v_res_1873_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_1869_, v_x_1452__boxed_1872_, v_x_1871_);
lean_dec_ref(v_x_1871_);
lean_dec_ref(v_x_1869_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(lean_object* v_x_1874_, lean_object* v_x_1875_){
_start:
{
uint64_t v___y_1877_; lean_object* v___x_1880_; 
v___x_1880_ = l_Lean_Meta_Grind_Origin_key(v_x_1875_);
if (lean_obj_tag(v___x_1880_) == 0)
{
uint64_t v___x_1881_; 
v___x_1881_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1877_ = v___x_1881_;
goto v___jp_1876_;
}
else
{
uint64_t v_hash_1882_; 
v_hash_1882_ = lean_ctor_get_uint64(v___x_1880_, sizeof(void*)*2);
lean_dec(v___x_1880_);
v___y_1877_ = v_hash_1882_;
goto v___jp_1876_;
}
v___jp_1876_:
{
size_t v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_uint64_to_usize(v___y_1877_);
v___x_1879_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_1874_, v___x_1878_, v_x_1875_);
return v___x_1879_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg___boxed(lean_object* v_x_1883_, lean_object* v_x_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_x_1883_, v_x_1884_);
lean_dec_ref(v_x_1884_);
lean_dec_ref(v_x_1883_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(lean_object* v_keys_1886_, lean_object* v_vals_1887_, lean_object* v_i_1888_, lean_object* v_k_1889_){
_start:
{
lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1890_ = lean_array_get_size(v_keys_1886_);
v___x_1891_ = lean_nat_dec_lt(v_i_1888_, v___x_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; 
lean_dec(v_i_1888_);
v___x_1892_ = lean_box(0);
return v___x_1892_;
}
else
{
lean_object* v_k_x27_1893_; uint8_t v___x_1894_; 
v_k_x27_1893_ = lean_array_fget_borrowed(v_keys_1886_, v_i_1888_);
v___x_1894_ = lean_name_eq(v_k_1889_, v_k_x27_1893_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_unsigned_to_nat(1u);
v___x_1896_ = lean_nat_add(v_i_1888_, v___x_1895_);
lean_dec(v_i_1888_);
v_i_1888_ = v___x_1896_;
goto _start;
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_array_fget_borrowed(v_vals_1887_, v_i_1888_);
lean_dec(v_i_1888_);
lean_inc(v___x_1898_);
v___x_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
return v___x_1899_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg___boxed(lean_object* v_keys_1900_, lean_object* v_vals_1901_, lean_object* v_i_1902_, lean_object* v_k_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_keys_1900_, v_vals_1901_, v_i_1902_, v_k_1903_);
lean_dec(v_k_1903_);
lean_dec_ref(v_vals_1901_);
lean_dec_ref(v_keys_1900_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(lean_object* v_x_1905_, size_t v_x_1906_, lean_object* v_x_1907_){
_start:
{
if (lean_obj_tag(v_x_1905_) == 0)
{
lean_object* v_es_1908_; lean_object* v___x_1909_; size_t v___x_1910_; size_t v___x_1911_; lean_object* v_j_1912_; lean_object* v___x_1913_; 
v_es_1908_ = lean_ctor_get(v_x_1905_, 0);
v___x_1909_ = lean_box(2);
v___x_1910_ = ((size_t)31ULL);
v___x_1911_ = lean_usize_land(v_x_1906_, v___x_1910_);
v_j_1912_ = lean_usize_to_nat(v___x_1911_);
v___x_1913_ = lean_array_get_borrowed(v___x_1909_, v_es_1908_, v_j_1912_);
lean_dec(v_j_1912_);
switch(lean_obj_tag(v___x_1913_))
{
case 0:
{
lean_object* v_key_1914_; lean_object* v_val_1915_; uint8_t v___x_1916_; 
v_key_1914_ = lean_ctor_get(v___x_1913_, 0);
v_val_1915_ = lean_ctor_get(v___x_1913_, 1);
v___x_1916_ = lean_name_eq(v_x_1907_, v_key_1914_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_box(0);
return v___x_1917_;
}
else
{
lean_object* v___x_1918_; 
lean_inc(v_val_1915_);
v___x_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1918_, 0, v_val_1915_);
return v___x_1918_;
}
}
case 1:
{
lean_object* v_node_1919_; size_t v___x_1920_; size_t v___x_1921_; 
v_node_1919_ = lean_ctor_get(v___x_1913_, 0);
v___x_1920_ = ((size_t)5ULL);
v___x_1921_ = lean_usize_shift_right(v_x_1906_, v___x_1920_);
v_x_1905_ = v_node_1919_;
v_x_1906_ = v___x_1921_;
goto _start;
}
default: 
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_box(0);
return v___x_1923_;
}
}
}
else
{
lean_object* v_ks_1924_; lean_object* v_vs_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_ks_1924_ = lean_ctor_get(v_x_1905_, 0);
v_vs_1925_ = lean_ctor_get(v_x_1905_, 1);
v___x_1926_ = lean_unsigned_to_nat(0u);
v___x_1927_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_ks_1924_, v_vs_1925_, v___x_1926_, v_x_1907_);
return v___x_1927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg___boxed(lean_object* v_x_1928_, lean_object* v_x_1929_, lean_object* v_x_1930_){
_start:
{
size_t v_x_1542__boxed_1931_; lean_object* v_res_1932_; 
v_x_1542__boxed_1931_ = lean_unbox_usize(v_x_1929_);
lean_dec(v_x_1929_);
v_res_1932_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_1928_, v_x_1542__boxed_1931_, v_x_1930_);
lean_dec(v_x_1930_);
lean_dec_ref(v_x_1928_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(lean_object* v_x_1933_, lean_object* v_x_1934_){
_start:
{
uint64_t v___y_1936_; 
if (lean_obj_tag(v_x_1934_) == 0)
{
uint64_t v___x_1939_; 
v___x_1939_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1936_ = v___x_1939_;
goto v___jp_1935_;
}
else
{
uint64_t v_hash_1940_; 
v_hash_1940_ = lean_ctor_get_uint64(v_x_1934_, sizeof(void*)*2);
v___y_1936_ = v_hash_1940_;
goto v___jp_1935_;
}
v___jp_1935_:
{
size_t v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = lean_uint64_to_usize(v___y_1936_);
v___x_1938_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_1933_, v___x_1937_, v_x_1934_);
return v___x_1938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg___boxed(lean_object* v_x_1941_, lean_object* v_x_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_x_1941_, v_x_1942_);
lean_dec(v_x_1942_);
lean_dec_ref(v_x_1941_);
return v_res_1943_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_Meta_Grind_instInhabitedTheorems_default(lean_box(0));
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0(lean_object* v_msg_1952_){
_start:
{
lean_object* v___f_1953_; lean_object* v___f_1954_; lean_object* v___f_1955_; lean_object* v___f_1956_; lean_object* v___f_1957_; lean_object* v___f_1958_; lean_object* v___f_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___f_1953_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0));
v___f_1954_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1));
v___f_1955_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2));
v___f_1956_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3));
v___f_1957_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4));
v___f_1958_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5));
v___f_1959_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6));
v___x_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___f_1953_);
lean_ctor_set(v___x_1960_, 1, v___f_1954_);
v___x_1961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
lean_ctor_set(v___x_1961_, 1, v___f_1955_);
lean_ctor_set(v___x_1961_, 2, v___f_1956_);
lean_ctor_set(v___x_1961_, 3, v___f_1957_);
lean_ctor_set(v___x_1961_, 4, v___f_1958_);
v___x_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
lean_ctor_set(v___x_1962_, 1, v___f_1959_);
v___x_1963_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7, &l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once, _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7);
v___x_1964_ = l_instInhabitedOfMonad___redArg(v___x_1962_, v___x_1963_);
v___x_1965_ = lean_panic_fn_borrowed(v___x_1964_, v_msg_1952_);
lean_dec(v___x_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(lean_object* v_xs_1966_, lean_object* v_v_1967_, lean_object* v_i_1968_){
_start:
{
lean_object* v___x_1969_; uint8_t v___x_1970_; 
v___x_1969_ = lean_array_get_size(v_xs_1966_);
v___x_1970_ = lean_nat_dec_lt(v_i_1968_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; 
lean_dec(v_i_1968_);
v___x_1971_ = lean_box(0);
return v___x_1971_;
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v___x_1972_ = lean_array_fget_borrowed(v_xs_1966_, v_i_1968_);
v___x_1973_ = l_Lean_Meta_Grind_Origin_key(v___x_1972_);
v___x_1974_ = l_Lean_Meta_Grind_Origin_key(v_v_1967_);
v___x_1975_ = lean_name_eq(v___x_1973_, v___x_1974_);
lean_dec(v___x_1974_);
lean_dec(v___x_1973_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = lean_unsigned_to_nat(1u);
v___x_1977_ = lean_nat_add(v_i_1968_, v___x_1976_);
lean_dec(v_i_1968_);
v_i_1968_ = v___x_1977_;
goto _start;
}
else
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1979_, 0, v_i_1968_);
return v___x_1979_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13___boxed(lean_object* v_xs_1980_, lean_object* v_v_1981_, lean_object* v_i_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(v_xs_1980_, v_v_1981_, v_i_1982_);
lean_dec_ref(v_v_1981_);
lean_dec_ref(v_xs_1980_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(lean_object* v_xs_1984_, lean_object* v_v_1985_){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = lean_unsigned_to_nat(0u);
v___x_1987_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(v_xs_1984_, v_v_1985_, v___x_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9___boxed(lean_object* v_xs_1988_, lean_object* v_v_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(v_xs_1988_, v_v_1989_);
lean_dec_ref(v_v_1989_);
lean_dec_ref(v_xs_1988_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(lean_object* v_x_1991_, size_t v_x_1992_, lean_object* v_x_1993_){
_start:
{
if (lean_obj_tag(v_x_1991_) == 0)
{
lean_object* v_es_1994_; lean_object* v___x_1995_; size_t v___x_1996_; size_t v___x_1997_; lean_object* v_j_1998_; lean_object* v_entry_1999_; 
v_es_1994_ = lean_ctor_get(v_x_1991_, 0);
v___x_1995_ = lean_box(2);
v___x_1996_ = ((size_t)31ULL);
v___x_1997_ = lean_usize_land(v_x_1992_, v___x_1996_);
v_j_1998_ = lean_usize_to_nat(v___x_1997_);
v_entry_1999_ = lean_array_get(v___x_1995_, v_es_1994_, v_j_1998_);
switch(lean_obj_tag(v_entry_1999_))
{
case 0:
{
lean_object* v_key_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v_key_2000_ = lean_ctor_get(v_entry_1999_, 0);
lean_inc(v_key_2000_);
lean_dec_ref_known(v_entry_1999_, 2);
v___x_2001_ = l_Lean_Meta_Grind_Origin_key(v_x_1993_);
v___x_2002_ = l_Lean_Meta_Grind_Origin_key(v_key_2000_);
lean_dec(v_key_2000_);
v___x_2003_ = lean_name_eq(v___x_2001_, v___x_2002_);
lean_dec(v___x_2002_);
lean_dec(v___x_2001_);
if (v___x_2003_ == 0)
{
lean_dec(v_j_1998_);
return v_x_1991_;
}
else
{
lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2011_; 
lean_inc_ref(v_es_1994_);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_x_1991_);
if (v_isSharedCheck_2011_ == 0)
{
lean_object* v_unused_2012_; 
v_unused_2012_ = lean_ctor_get(v_x_1991_, 0);
lean_dec(v_unused_2012_);
v___x_2005_ = v_x_1991_;
v_isShared_2006_ = v_isSharedCheck_2011_;
goto v_resetjp_2004_;
}
else
{
lean_dec(v_x_1991_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2011_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2007_ = lean_array_set(v_es_1994_, v_j_1998_, v___x_1995_);
lean_dec(v_j_1998_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v___x_2007_);
v___x_2009_ = v___x_2005_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
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
case 1:
{
lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2047_; 
lean_inc_ref(v_es_1994_);
v_isSharedCheck_2047_ = !lean_is_exclusive(v_x_1991_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; 
v_unused_2048_ = lean_ctor_get(v_x_1991_, 0);
lean_dec(v_unused_2048_);
v___x_2014_ = v_x_1991_;
v_isShared_2015_ = v_isSharedCheck_2047_;
goto v_resetjp_2013_;
}
else
{
lean_dec(v_x_1991_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2047_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v_node_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2046_; 
v_node_2016_ = lean_ctor_get(v_entry_1999_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_entry_1999_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2018_ = v_entry_1999_;
v_isShared_2019_ = v_isSharedCheck_2046_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_node_2016_);
lean_dec(v_entry_1999_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2046_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
size_t v___x_2020_; lean_object* v_entries_2021_; size_t v___x_2022_; lean_object* v_newNode_2023_; lean_object* v___x_2024_; 
v___x_2020_ = ((size_t)5ULL);
v_entries_2021_ = lean_array_set(v_es_1994_, v_j_1998_, v___x_1995_);
v___x_2022_ = lean_usize_shift_right(v_x_1992_, v___x_2020_);
v_newNode_2023_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_node_2016_, v___x_2022_, v_x_1993_);
lean_inc_ref(v_newNode_2023_);
v___x_2024_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2023_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v___x_2026_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v_newNode_2023_);
v___x_2026_ = v___x_2018_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_newNode_2023_);
v___x_2026_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2027_ = lean_array_set(v_entries_2021_, v_j_1998_, v___x_2026_);
lean_dec(v_j_1998_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2027_);
v___x_2029_ = v___x_2014_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
else
{
lean_object* v_val_2032_; lean_object* v_fst_2033_; lean_object* v_snd_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v_newNode_2023_);
lean_del_object(v___x_2018_);
v_val_2032_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_val_2032_);
lean_dec_ref_known(v___x_2024_, 1);
v_fst_2033_ = lean_ctor_get(v_val_2032_, 0);
v_snd_2034_ = lean_ctor_get(v_val_2032_, 1);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_val_2032_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2036_ = v_val_2032_;
v_isShared_2037_ = v_isSharedCheck_2045_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_snd_2034_);
lean_inc(v_fst_2033_);
lean_dec(v_val_2032_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2045_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_fst_2033_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_snd_2034_);
v___x_2039_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___x_2040_ = lean_array_set(v_entries_2021_, v_j_1998_, v___x_2039_);
lean_dec(v_j_1998_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2040_);
v___x_2042_ = v___x_2014_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_1998_);
return v_x_1991_;
}
}
}
else
{
lean_object* v_ks_2049_; lean_object* v_vs_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2064_; 
v_ks_2049_ = lean_ctor_get(v_x_1991_, 0);
v_vs_2050_ = lean_ctor_get(v_x_1991_, 1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_x_1991_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2052_ = v_x_1991_;
v_isShared_2053_ = v_isSharedCheck_2064_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_vs_2050_);
lean_inc(v_ks_2049_);
lean_dec(v_x_1991_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2064_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(v_ks_2049_, v_x_1993_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v___x_2056_; 
if (v_isShared_2053_ == 0)
{
v___x_2056_ = v___x_2052_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_ks_2049_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_vs_2050_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
else
{
lean_object* v_val_2058_; lean_object* v_keys_x27_2059_; lean_object* v_vals_x27_2060_; lean_object* v___x_2062_; 
v_val_2058_ = lean_ctor_get(v___x_2054_, 0);
lean_inc_n(v_val_2058_, 2);
lean_dec_ref_known(v___x_2054_, 1);
v_keys_x27_2059_ = l_Array_eraseIdx___redArg(v_ks_2049_, v_val_2058_);
v_vals_x27_2060_ = l_Array_eraseIdx___redArg(v_vs_2050_, v_val_2058_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 1, v_vals_x27_2060_);
lean_ctor_set(v___x_2052_, 0, v_keys_x27_2059_);
v___x_2062_ = v___x_2052_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_keys_x27_2059_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_vals_x27_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2065_, lean_object* v_x_2066_, lean_object* v_x_2067_){
_start:
{
size_t v_x_1684__boxed_2068_; lean_object* v_res_2069_; 
v_x_1684__boxed_2068_ = lean_unbox_usize(v_x_2066_);
lean_dec(v_x_2066_);
v_res_2069_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2065_, v_x_1684__boxed_2068_, v_x_2067_);
lean_dec_ref(v_x_2067_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(lean_object* v_x_2070_, lean_object* v_x_2071_){
_start:
{
uint64_t v___y_2073_; lean_object* v___x_2076_; 
v___x_2076_ = l_Lean_Meta_Grind_Origin_key(v_x_2071_);
if (lean_obj_tag(v___x_2076_) == 0)
{
uint64_t v___x_2077_; 
v___x_2077_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_2073_ = v___x_2077_;
goto v___jp_2072_;
}
else
{
uint64_t v_hash_2078_; 
v_hash_2078_ = lean_ctor_get_uint64(v___x_2076_, sizeof(void*)*2);
lean_dec(v___x_2076_);
v___y_2073_ = v_hash_2078_;
goto v___jp_2072_;
}
v___jp_2072_:
{
size_t v_h_2074_; lean_object* v___x_2075_; 
v_h_2074_ = lean_uint64_to_usize(v___y_2073_);
v___x_2075_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2070_, v_h_2074_, v_x_2071_);
return v___x_2075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg___boxed(lean_object* v_x_2079_, lean_object* v_x_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_x_2079_, v_x_2080_);
lean_dec_ref(v_x_2080_);
return v_res_2081_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2085_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2));
v___x_2086_ = lean_unsigned_to_nat(6u);
v___x_2087_ = lean_unsigned_to_nat(82u);
v___x_2088_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__1));
v___x_2089_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__0));
v___x_2090_ = l_mkPanicMessageWithDecl(v___x_2089_, v___x_2088_, v___x_2087_, v___x_2086_, v___x_2085_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0(lean_object* v_s_2091_, lean_object* v_thm_2092_){
_start:
{
lean_object* v_symbols_2096_; 
v_symbols_2096_ = lean_ctor_get(v_thm_2092_, 4);
lean_inc(v_symbols_2096_);
if (lean_obj_tag(v_symbols_2096_) == 1)
{
lean_object* v_head_2097_; 
v_head_2097_ = lean_ctor_get(v_symbols_2096_, 0);
lean_inc(v_head_2097_);
if (lean_obj_tag(v_head_2097_) == 2)
{
lean_object* v_levelParams_2098_; lean_object* v_proof_2099_; lean_object* v_numParams_2100_; lean_object* v_patterns_2101_; lean_object* v_origin_2102_; lean_object* v_kind_2103_; uint8_t v_minIndexable_2104_; lean_object* v_cnstrs_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2156_; 
v_levelParams_2098_ = lean_ctor_get(v_thm_2092_, 0);
v_proof_2099_ = lean_ctor_get(v_thm_2092_, 1);
v_numParams_2100_ = lean_ctor_get(v_thm_2092_, 2);
v_patterns_2101_ = lean_ctor_get(v_thm_2092_, 3);
v_origin_2102_ = lean_ctor_get(v_thm_2092_, 5);
v_kind_2103_ = lean_ctor_get(v_thm_2092_, 6);
v_minIndexable_2104_ = lean_ctor_get_uint8(v_thm_2092_, sizeof(void*)*8);
v_cnstrs_2105_ = lean_ctor_get(v_thm_2092_, 7);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_thm_2092_);
if (v_isSharedCheck_2156_ == 0)
{
lean_object* v_unused_2157_; 
v_unused_2157_ = lean_ctor_get(v_thm_2092_, 4);
lean_dec(v_unused_2157_);
v___x_2107_ = v_thm_2092_;
v_isShared_2108_ = v_isSharedCheck_2156_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_cnstrs_2105_);
lean_inc(v_kind_2103_);
lean_inc(v_origin_2102_);
lean_inc(v_patterns_2101_);
lean_inc(v_numParams_2100_);
lean_inc(v_proof_2099_);
lean_inc(v_levelParams_2098_);
lean_dec(v_thm_2092_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2156_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v_tail_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2154_; 
v_tail_2109_ = lean_ctor_get(v_symbols_2096_, 1);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_symbols_2096_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v_symbols_2096_, 0);
lean_dec(v_unused_2155_);
v___x_2111_ = v_symbols_2096_;
v_isShared_2112_ = v_isSharedCheck_2154_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_tail_2109_);
lean_dec(v_symbols_2096_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2154_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v_constName_2113_; lean_object* v_smap_2114_; lean_object* v_origins_2115_; lean_object* v_erased_2116_; lean_object* v_omap_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2153_; 
v_constName_2113_ = lean_ctor_get(v_head_2097_, 0);
lean_inc(v_constName_2113_);
lean_dec_ref_known(v_head_2097_, 1);
v_smap_2114_ = lean_ctor_get(v_s_2091_, 0);
v_origins_2115_ = lean_ctor_get(v_s_2091_, 1);
v_erased_2116_ = lean_ctor_get(v_s_2091_, 2);
v_omap_2117_ = lean_ctor_get(v_s_2091_, 3);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_s_2091_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2119_ = v_s_2091_;
v_isShared_2120_ = v_isSharedCheck_2153_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_omap_2117_);
lean_inc(v_erased_2116_);
lean_inc(v_origins_2115_);
lean_inc(v_smap_2114_);
lean_dec(v_s_2091_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2153_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v_thm_2122_; 
lean_inc_ref(v_origin_2102_);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 4, v_tail_2109_);
v_thm_2122_ = v___x_2107_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_levelParams_2098_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_proof_2099_);
lean_ctor_set(v_reuseFailAlloc_2152_, 2, v_numParams_2100_);
lean_ctor_set(v_reuseFailAlloc_2152_, 3, v_patterns_2101_);
lean_ctor_set(v_reuseFailAlloc_2152_, 4, v_tail_2109_);
lean_ctor_set(v_reuseFailAlloc_2152_, 5, v_origin_2102_);
lean_ctor_set(v_reuseFailAlloc_2152_, 6, v_kind_2103_);
lean_ctor_set(v_reuseFailAlloc_2152_, 7, v_cnstrs_2105_);
lean_ctor_set_uint8(v_reuseFailAlloc_2152_, sizeof(void*)*8, v_minIndexable_2104_);
v_thm_2122_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v_origins_2124_; lean_object* v_erased_2125_; lean_object* v___y_2127_; lean_object* v___x_2145_; 
v___x_2123_ = lean_box(0);
lean_inc_ref(v_origin_2102_);
v_origins_2124_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_origins_2115_, v_origin_2102_, v___x_2123_);
v_erased_2125_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_erased_2116_, v_origin_2102_);
v___x_2145_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_smap_2114_, v_constName_2113_);
if (lean_obj_tag(v___x_2145_) == 1)
{
lean_object* v_val_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v_val_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_val_2146_);
lean_dec_ref_known(v___x_2145_, 1);
lean_inc_ref(v_thm_2122_);
v___x_2147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2147_, 0, v_thm_2122_);
lean_ctor_set(v___x_2147_, 1, v_val_2146_);
v___x_2148_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2114_, v_constName_2113_, v___x_2147_);
v___y_2127_ = v___x_2148_;
goto v___jp_2126_;
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
lean_dec(v___x_2145_);
v___x_2149_ = lean_box(0);
lean_inc_ref(v_thm_2122_);
v___x_2150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2150_, 0, v_thm_2122_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2114_, v_constName_2113_, v___x_2150_);
v___y_2127_ = v___x_2151_;
goto v___jp_2126_;
}
v___jp_2126_:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_omap_2117_, v_origin_2102_);
if (lean_obj_tag(v___x_2128_) == 1)
{
lean_object* v_val_2129_; lean_object* v___x_2131_; 
v_val_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_val_2129_);
lean_dec_ref_known(v___x_2128_, 1);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 1, v_val_2129_);
lean_ctor_set(v___x_2111_, 0, v_thm_2122_);
v___x_2131_ = v___x_2111_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_thm_2122_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_val_2129_);
v___x_2131_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2132_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2117_, v_origin_2102_, v___x_2131_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 3, v___x_2132_);
lean_ctor_set(v___x_2119_, 2, v_erased_2125_);
lean_ctor_set(v___x_2119_, 1, v_origins_2124_);
lean_ctor_set(v___x_2119_, 0, v___y_2127_);
v___x_2134_ = v___x_2119_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___y_2127_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_origins_2124_);
lean_ctor_set(v_reuseFailAlloc_2135_, 2, v_erased_2125_);
lean_ctor_set(v_reuseFailAlloc_2135_, 3, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2139_; 
lean_dec(v___x_2128_);
v___x_2137_ = lean_box(0);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 1, v___x_2137_);
lean_ctor_set(v___x_2111_, 0, v_thm_2122_);
v___x_2139_ = v___x_2111_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_thm_2122_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2117_, v_origin_2102_, v___x_2139_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 3, v___x_2140_);
lean_ctor_set(v___x_2119_, 2, v_erased_2125_);
lean_ctor_set(v___x_2119_, 1, v_origins_2124_);
lean_ctor_set(v___x_2119_, 0, v___y_2127_);
v___x_2142_ = v___x_2119_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___y_2127_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_origins_2124_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_erased_2125_);
lean_ctor_set(v_reuseFailAlloc_2143_, 3, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
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
lean_dec(v_head_2097_);
lean_dec_ref_known(v_symbols_2096_, 2);
lean_dec_ref(v_thm_2092_);
lean_dec_ref(v_s_2091_);
goto v___jp_2093_;
}
}
else
{
lean_dec(v_symbols_2096_);
lean_dec_ref(v_thm_2092_);
lean_dec_ref(v_s_2091_);
goto v___jp_2093_;
}
v___jp_2093_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2094_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3, &l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3);
v___x_2095_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0(v___x_2094_);
return v___x_2095_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1_spec__6(lean_object* v_msg_2158_){
_start:
{
lean_object* v___f_2159_; lean_object* v___f_2160_; lean_object* v___f_2161_; lean_object* v___f_2162_; lean_object* v___f_2163_; lean_object* v___f_2164_; lean_object* v___f_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___f_2159_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0));
v___f_2160_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1));
v___f_2161_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2));
v___f_2162_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3));
v___f_2163_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4));
v___f_2164_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5));
v___f_2165_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6));
v___x_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___f_2159_);
lean_ctor_set(v___x_2166_, 1, v___f_2160_);
v___x_2167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
lean_ctor_set(v___x_2167_, 1, v___f_2161_);
lean_ctor_set(v___x_2167_, 2, v___f_2162_);
lean_ctor_set(v___x_2167_, 3, v___f_2163_);
lean_ctor_set(v___x_2167_, 4, v___f_2164_);
v___x_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
lean_ctor_set(v___x_2168_, 1, v___f_2165_);
v___x_2169_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7, &l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once, _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7);
v___x_2170_ = l_instInhabitedOfMonad___redArg(v___x_2168_, v___x_2169_);
v___x_2171_ = lean_panic_fn_borrowed(v___x_2170_, v_msg_2158_);
lean_dec(v___x_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1(lean_object* v_s_2172_, lean_object* v_thm_2173_){
_start:
{
lean_object* v_symbols_2177_; 
v_symbols_2177_ = lean_ctor_get(v_thm_2173_, 2);
lean_inc(v_symbols_2177_);
if (lean_obj_tag(v_symbols_2177_) == 1)
{
lean_object* v_head_2178_; 
v_head_2178_ = lean_ctor_get(v_symbols_2177_, 0);
lean_inc(v_head_2178_);
if (lean_obj_tag(v_head_2178_) == 2)
{
lean_object* v_levelParams_2179_; lean_object* v_proof_2180_; lean_object* v_origin_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2232_; 
v_levelParams_2179_ = lean_ctor_get(v_thm_2173_, 0);
v_proof_2180_ = lean_ctor_get(v_thm_2173_, 1);
v_origin_2181_ = lean_ctor_get(v_thm_2173_, 3);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_thm_2173_);
if (v_isSharedCheck_2232_ == 0)
{
lean_object* v_unused_2233_; 
v_unused_2233_ = lean_ctor_get(v_thm_2173_, 2);
lean_dec(v_unused_2233_);
v___x_2183_ = v_thm_2173_;
v_isShared_2184_ = v_isSharedCheck_2232_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_origin_2181_);
lean_inc(v_proof_2180_);
lean_inc(v_levelParams_2179_);
lean_dec(v_thm_2173_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2232_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v_tail_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2230_; 
v_tail_2185_ = lean_ctor_get(v_symbols_2177_, 1);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_symbols_2177_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v_symbols_2177_, 0);
lean_dec(v_unused_2231_);
v___x_2187_ = v_symbols_2177_;
v_isShared_2188_ = v_isSharedCheck_2230_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_tail_2185_);
lean_dec(v_symbols_2177_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2230_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v_constName_2189_; lean_object* v_smap_2190_; lean_object* v_origins_2191_; lean_object* v_erased_2192_; lean_object* v_omap_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2229_; 
v_constName_2189_ = lean_ctor_get(v_head_2178_, 0);
lean_inc(v_constName_2189_);
lean_dec_ref_known(v_head_2178_, 1);
v_smap_2190_ = lean_ctor_get(v_s_2172_, 0);
v_origins_2191_ = lean_ctor_get(v_s_2172_, 1);
v_erased_2192_ = lean_ctor_get(v_s_2172_, 2);
v_omap_2193_ = lean_ctor_get(v_s_2172_, 3);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_s_2172_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2195_ = v_s_2172_;
v_isShared_2196_ = v_isSharedCheck_2229_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_omap_2193_);
lean_inc(v_erased_2192_);
lean_inc(v_origins_2191_);
lean_inc(v_smap_2190_);
lean_dec(v_s_2172_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2229_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v_thm_2198_; 
lean_inc_ref(v_origin_2181_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 2, v_tail_2185_);
v_thm_2198_ = v___x_2183_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_levelParams_2179_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_proof_2180_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v_tail_2185_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v_origin_2181_);
v_thm_2198_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; lean_object* v_origins_2200_; lean_object* v_erased_2201_; lean_object* v___y_2203_; lean_object* v___x_2221_; 
v___x_2199_ = lean_box(0);
lean_inc_ref(v_origin_2181_);
v_origins_2200_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_origins_2191_, v_origin_2181_, v___x_2199_);
v_erased_2201_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_erased_2192_, v_origin_2181_);
v___x_2221_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_smap_2190_, v_constName_2189_);
if (lean_obj_tag(v___x_2221_) == 1)
{
lean_object* v_val_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v_val_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_val_2222_);
lean_dec_ref_known(v___x_2221_, 1);
lean_inc_ref(v_thm_2198_);
v___x_2223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2223_, 0, v_thm_2198_);
lean_ctor_set(v___x_2223_, 1, v_val_2222_);
v___x_2224_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2190_, v_constName_2189_, v___x_2223_);
v___y_2203_ = v___x_2224_;
goto v___jp_2202_;
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
lean_dec(v___x_2221_);
v___x_2225_ = lean_box(0);
lean_inc_ref(v_thm_2198_);
v___x_2226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2226_, 0, v_thm_2198_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
v___x_2227_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2190_, v_constName_2189_, v___x_2226_);
v___y_2203_ = v___x_2227_;
goto v___jp_2202_;
}
v___jp_2202_:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_omap_2193_, v_origin_2181_);
if (lean_obj_tag(v___x_2204_) == 1)
{
lean_object* v_val_2205_; lean_object* v___x_2207_; 
v_val_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_val_2205_);
lean_dec_ref_known(v___x_2204_, 1);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 1, v_val_2205_);
lean_ctor_set(v___x_2187_, 0, v_thm_2198_);
v___x_2207_ = v___x_2187_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_thm_2198_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v_val_2205_);
v___x_2207_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2208_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2193_, v_origin_2181_, v___x_2207_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 3, v___x_2208_);
lean_ctor_set(v___x_2195_, 2, v_erased_2201_);
lean_ctor_set(v___x_2195_, 1, v_origins_2200_);
lean_ctor_set(v___x_2195_, 0, v___y_2203_);
v___x_2210_ = v___x_2195_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___y_2203_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_origins_2200_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_erased_2201_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2215_; 
lean_dec(v___x_2204_);
v___x_2213_ = lean_box(0);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 1, v___x_2213_);
lean_ctor_set(v___x_2187_, 0, v_thm_2198_);
v___x_2215_ = v___x_2187_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_thm_2198_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2216_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2193_, v_origin_2181_, v___x_2215_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 3, v___x_2216_);
lean_ctor_set(v___x_2195_, 2, v_erased_2201_);
lean_ctor_set(v___x_2195_, 1, v_origins_2200_);
lean_ctor_set(v___x_2195_, 0, v___y_2203_);
v___x_2218_ = v___x_2195_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___y_2203_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_origins_2200_);
lean_ctor_set(v_reuseFailAlloc_2219_, 2, v_erased_2201_);
lean_ctor_set(v_reuseFailAlloc_2219_, 3, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
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
lean_dec_ref_known(v_symbols_2177_, 2);
lean_dec(v_head_2178_);
lean_dec_ref(v_thm_2173_);
lean_dec_ref(v_s_2172_);
goto v___jp_2174_;
}
}
else
{
lean_dec(v_symbols_2177_);
lean_dec_ref(v_thm_2173_);
lean_dec_ref(v_s_2172_);
goto v___jp_2174_;
}
v___jp_2174_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3, &l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3);
v___x_2176_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1_spec__6(v___x_2175_);
return v___x_2176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionState_addEntry(lean_object* v_s_2234_, lean_object* v_e_2235_){
_start:
{
switch(lean_obj_tag(v_e_2235_))
{
case 0:
{
lean_object* v_declName_2236_; lean_object* v_casesTypes_2237_; lean_object* v_extThms_2238_; lean_object* v_funCC_2239_; lean_object* v_ematch_2240_; lean_object* v_inj_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2250_; 
v_declName_2236_ = lean_ctor_get(v_e_2235_, 0);
lean_inc(v_declName_2236_);
lean_dec_ref_known(v_e_2235_, 1);
v_casesTypes_2237_ = lean_ctor_get(v_s_2234_, 0);
v_extThms_2238_ = lean_ctor_get(v_s_2234_, 1);
v_funCC_2239_ = lean_ctor_get(v_s_2234_, 2);
v_ematch_2240_ = lean_ctor_get(v_s_2234_, 3);
v_inj_2241_ = lean_ctor_get(v_s_2234_, 4);
v_isSharedCheck_2250_ = !lean_is_exclusive(v_s_2234_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2243_ = v_s_2234_;
v_isShared_2244_ = v_isSharedCheck_2250_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_inj_2241_);
lean_inc(v_ematch_2240_);
lean_inc(v_funCC_2239_);
lean_inc(v_extThms_2238_);
lean_inc(v_casesTypes_2237_);
lean_dec(v_s_2234_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2250_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2245_ = lean_box(0);
v___x_2246_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_extThms_2238_, v_declName_2236_, v___x_2245_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 1, v___x_2246_);
v___x_2248_ = v___x_2243_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_casesTypes_2237_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v___x_2246_);
lean_ctor_set(v_reuseFailAlloc_2249_, 2, v_funCC_2239_);
lean_ctor_set(v_reuseFailAlloc_2249_, 3, v_ematch_2240_);
lean_ctor_set(v_reuseFailAlloc_2249_, 4, v_inj_2241_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
case 1:
{
lean_object* v_declName_2251_; lean_object* v_casesTypes_2252_; lean_object* v_extThms_2253_; lean_object* v_funCC_2254_; lean_object* v_ematch_2255_; lean_object* v_inj_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2264_; 
v_declName_2251_ = lean_ctor_get(v_e_2235_, 0);
lean_inc(v_declName_2251_);
lean_dec_ref_known(v_e_2235_, 1);
v_casesTypes_2252_ = lean_ctor_get(v_s_2234_, 0);
v_extThms_2253_ = lean_ctor_get(v_s_2234_, 1);
v_funCC_2254_ = lean_ctor_get(v_s_2234_, 2);
v_ematch_2255_ = lean_ctor_get(v_s_2234_, 3);
v_inj_2256_ = lean_ctor_get(v_s_2234_, 4);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_s_2234_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2258_ = v_s_2234_;
v_isShared_2259_ = v_isSharedCheck_2264_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_inj_2256_);
lean_inc(v_ematch_2255_);
lean_inc(v_funCC_2254_);
lean_inc(v_extThms_2253_);
lean_inc(v_casesTypes_2252_);
lean_dec(v_s_2234_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2264_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2260_ = l_Lean_NameSet_insert(v_funCC_2254_, v_declName_2251_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 2, v___x_2260_);
v___x_2262_ = v___x_2258_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_casesTypes_2252_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v_extThms_2253_);
lean_ctor_set(v_reuseFailAlloc_2263_, 2, v___x_2260_);
lean_ctor_set(v_reuseFailAlloc_2263_, 3, v_ematch_2255_);
lean_ctor_set(v_reuseFailAlloc_2263_, 4, v_inj_2256_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
case 2:
{
lean_object* v_declName_2265_; uint8_t v_eager_2266_; lean_object* v_casesTypes_2267_; lean_object* v_extThms_2268_; lean_object* v_funCC_2269_; lean_object* v_ematch_2270_; lean_object* v_inj_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2280_; 
v_declName_2265_ = lean_ctor_get(v_e_2235_, 0);
lean_inc(v_declName_2265_);
v_eager_2266_ = lean_ctor_get_uint8(v_e_2235_, sizeof(void*)*1);
lean_dec_ref_known(v_e_2235_, 1);
v_casesTypes_2267_ = lean_ctor_get(v_s_2234_, 0);
v_extThms_2268_ = lean_ctor_get(v_s_2234_, 1);
v_funCC_2269_ = lean_ctor_get(v_s_2234_, 2);
v_ematch_2270_ = lean_ctor_get(v_s_2234_, 3);
v_inj_2271_ = lean_ctor_get(v_s_2234_, 4);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_s_2234_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2273_ = v_s_2234_;
v_isShared_2274_ = v_isSharedCheck_2280_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_inj_2271_);
lean_inc(v_ematch_2270_);
lean_inc(v_funCC_2269_);
lean_inc(v_extThms_2268_);
lean_inc(v_casesTypes_2267_);
lean_dec(v_s_2234_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2280_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2275_ = lean_box(v_eager_2266_);
v___x_2276_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_casesTypes_2267_, v_declName_2265_, v___x_2275_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v___x_2276_);
v___x_2278_ = v___x_2273_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_extThms_2268_);
lean_ctor_set(v_reuseFailAlloc_2279_, 2, v_funCC_2269_);
lean_ctor_set(v_reuseFailAlloc_2279_, 3, v_ematch_2270_);
lean_ctor_set(v_reuseFailAlloc_2279_, 4, v_inj_2271_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
case 3:
{
lean_object* v_thm_2281_; lean_object* v_casesTypes_2282_; lean_object* v_extThms_2283_; lean_object* v_funCC_2284_; lean_object* v_ematch_2285_; lean_object* v_inj_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2294_; 
v_thm_2281_ = lean_ctor_get(v_e_2235_, 0);
lean_inc_ref(v_thm_2281_);
lean_dec_ref_known(v_e_2235_, 1);
v_casesTypes_2282_ = lean_ctor_get(v_s_2234_, 0);
v_extThms_2283_ = lean_ctor_get(v_s_2234_, 1);
v_funCC_2284_ = lean_ctor_get(v_s_2234_, 2);
v_ematch_2285_ = lean_ctor_get(v_s_2234_, 3);
v_inj_2286_ = lean_ctor_get(v_s_2234_, 4);
v_isSharedCheck_2294_ = !lean_is_exclusive(v_s_2234_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2288_ = v_s_2234_;
v_isShared_2289_ = v_isSharedCheck_2294_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_inj_2286_);
lean_inc(v_ematch_2285_);
lean_inc(v_funCC_2284_);
lean_inc(v_extThms_2283_);
lean_inc(v_casesTypes_2282_);
lean_dec(v_s_2234_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2294_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2290_; lean_object* v___x_2292_; 
v___x_2290_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0(v_ematch_2285_, v_thm_2281_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 3, v___x_2290_);
v___x_2292_ = v___x_2288_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_casesTypes_2282_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_extThms_2283_);
lean_ctor_set(v_reuseFailAlloc_2293_, 2, v_funCC_2284_);
lean_ctor_set(v_reuseFailAlloc_2293_, 3, v___x_2290_);
lean_ctor_set(v_reuseFailAlloc_2293_, 4, v_inj_2286_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
default: 
{
lean_object* v_thm_2295_; lean_object* v_casesTypes_2296_; lean_object* v_extThms_2297_; lean_object* v_funCC_2298_; lean_object* v_ematch_2299_; lean_object* v_inj_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2308_; 
v_thm_2295_ = lean_ctor_get(v_e_2235_, 0);
lean_inc_ref(v_thm_2295_);
lean_dec_ref_known(v_e_2235_, 1);
v_casesTypes_2296_ = lean_ctor_get(v_s_2234_, 0);
v_extThms_2297_ = lean_ctor_get(v_s_2234_, 1);
v_funCC_2298_ = lean_ctor_get(v_s_2234_, 2);
v_ematch_2299_ = lean_ctor_get(v_s_2234_, 3);
v_inj_2300_ = lean_ctor_get(v_s_2234_, 4);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_s_2234_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2302_ = v_s_2234_;
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_inj_2300_);
lean_inc(v_ematch_2299_);
lean_inc(v_funCC_2298_);
lean_inc(v_extThms_2297_);
lean_inc(v_casesTypes_2296_);
lean_dec(v_s_2234_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2304_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1(v_inj_2300_, v_thm_2295_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 4, v___x_2304_);
v___x_2306_ = v___x_2302_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_casesTypes_2296_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_extThms_2297_);
lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_funCC_2298_);
lean_ctor_set(v_reuseFailAlloc_2307_, 3, v_ematch_2299_);
lean_ctor_set(v_reuseFailAlloc_2307_, 4, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1(lean_object* v_00_u03b2_2309_, lean_object* v_x_2310_, lean_object* v_x_2311_, lean_object* v_x_2312_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_x_2310_, v_x_2311_, v_x_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2(lean_object* v_00_u03b2_2314_, lean_object* v_x_2315_, lean_object* v_x_2316_){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_x_2315_, v_x_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2318_, lean_object* v_x_2319_, lean_object* v_x_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2(v_00_u03b2_2318_, v_x_2319_, v_x_2320_);
lean_dec_ref(v_x_2320_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3(lean_object* v_00_u03b2_2322_, lean_object* v_x_2323_, lean_object* v_x_2324_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_x_2323_, v_x_2324_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2326_, lean_object* v_x_2327_, lean_object* v_x_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3(v_00_u03b2_2326_, v_x_2327_, v_x_2328_);
lean_dec_ref(v_x_2328_);
lean_dec_ref(v_x_2327_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4(lean_object* v_00_u03b2_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_x_2331_, v_x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___boxed(lean_object* v_00_u03b2_2334_, lean_object* v_x_2335_, lean_object* v_x_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4(v_00_u03b2_2334_, v_x_2335_, v_x_2336_);
lean_dec(v_x_2336_);
lean_dec_ref(v_x_2335_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2338_, lean_object* v_x_2339_, size_t v_x_2340_, size_t v_x_2341_, lean_object* v_x_2342_, lean_object* v_x_2343_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_2339_, v_x_2340_, v_x_2341_, v_x_2342_, v_x_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2345_, lean_object* v_x_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_, lean_object* v_x_2349_, lean_object* v_x_2350_){
_start:
{
size_t v_x_2258__boxed_2351_; size_t v_x_2259__boxed_2352_; lean_object* v_res_2353_; 
v_x_2258__boxed_2351_ = lean_unbox_usize(v_x_2347_);
lean_dec(v_x_2347_);
v_x_2259__boxed_2352_ = lean_unbox_usize(v_x_2348_);
lean_dec(v_x_2348_);
v_res_2353_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(v_00_u03b2_2345_, v_x_2346_, v_x_2258__boxed_2351_, v_x_2259__boxed_2352_, v_x_2349_, v_x_2350_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2354_, lean_object* v_x_2355_, size_t v_x_2356_, lean_object* v_x_2357_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2355_, v_x_2356_, v_x_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2359_, lean_object* v_x_2360_, lean_object* v_x_2361_, lean_object* v_x_2362_){
_start:
{
size_t v_x_2275__boxed_2363_; lean_object* v_res_2364_; 
v_x_2275__boxed_2363_ = lean_unbox_usize(v_x_2361_);
lean_dec(v_x_2361_);
v_res_2364_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(v_00_u03b2_2359_, v_x_2360_, v_x_2275__boxed_2363_, v_x_2362_);
lean_dec_ref(v_x_2362_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(lean_object* v_00_u03b2_2365_, lean_object* v_x_2366_, size_t v_x_2367_, lean_object* v_x_2368_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_2366_, v_x_2367_, v_x_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2370_, lean_object* v_x_2371_, lean_object* v_x_2372_, lean_object* v_x_2373_){
_start:
{
size_t v_x_2286__boxed_2374_; lean_object* v_res_2375_; 
v_x_2286__boxed_2374_ = lean_unbox_usize(v_x_2372_);
lean_dec(v_x_2372_);
v_res_2375_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(v_00_u03b2_2370_, v_x_2371_, v_x_2286__boxed_2374_, v_x_2373_);
lean_dec_ref(v_x_2373_);
lean_dec_ref(v_x_2371_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(lean_object* v_00_u03b2_2376_, lean_object* v_x_2377_, size_t v_x_2378_, lean_object* v_x_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_2377_, v_x_2378_, v_x_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_, lean_object* v_x_2384_){
_start:
{
size_t v_x_2297__boxed_2385_; lean_object* v_res_2386_; 
v_x_2297__boxed_2385_ = lean_unbox_usize(v_x_2383_);
lean_dec(v_x_2383_);
v_res_2386_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(v_00_u03b2_2381_, v_x_2382_, v_x_2297__boxed_2385_, v_x_2384_);
lean_dec(v_x_2384_);
lean_dec_ref(v_x_2382_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2387_, lean_object* v_n_2388_, lean_object* v_k_2389_, lean_object* v_v_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(v_n_2388_, v_k_2389_, v_v_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2392_, size_t v_depth_2393_, lean_object* v_keys_2394_, lean_object* v_vals_2395_, lean_object* v_heq_2396_, lean_object* v_i_2397_, lean_object* v_entries_2398_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_depth_2393_, v_keys_2394_, v_vals_2395_, v_i_2397_, v_entries_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2400_, lean_object* v_depth_2401_, lean_object* v_keys_2402_, lean_object* v_vals_2403_, lean_object* v_heq_2404_, lean_object* v_i_2405_, lean_object* v_entries_2406_){
_start:
{
size_t v_depth_boxed_2407_; lean_object* v_res_2408_; 
v_depth_boxed_2407_ = lean_unbox_usize(v_depth_2401_);
lean_dec(v_depth_2401_);
v_res_2408_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(v_00_u03b2_2400_, v_depth_boxed_2407_, v_keys_2402_, v_vals_2403_, v_heq_2404_, v_i_2405_, v_entries_2406_);
lean_dec_ref(v_vals_2403_);
lean_dec_ref(v_keys_2402_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12(lean_object* v_00_u03b2_2409_, lean_object* v_keys_2410_, lean_object* v_vals_2411_, lean_object* v_heq_2412_, lean_object* v_i_2413_, lean_object* v_k_2414_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_keys_2410_, v_vals_2411_, v_i_2413_, v_k_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___boxed(lean_object* v_00_u03b2_2416_, lean_object* v_keys_2417_, lean_object* v_vals_2418_, lean_object* v_heq_2419_, lean_object* v_i_2420_, lean_object* v_k_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12(v_00_u03b2_2416_, v_keys_2417_, v_vals_2418_, v_heq_2419_, v_i_2420_, v_k_2421_);
lean_dec_ref(v_k_2421_);
lean_dec_ref(v_vals_2418_);
lean_dec_ref(v_keys_2417_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15(lean_object* v_00_u03b2_2423_, lean_object* v_keys_2424_, lean_object* v_vals_2425_, lean_object* v_heq_2426_, lean_object* v_i_2427_, lean_object* v_k_2428_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_keys_2424_, v_vals_2425_, v_i_2427_, v_k_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___boxed(lean_object* v_00_u03b2_2430_, lean_object* v_keys_2431_, lean_object* v_vals_2432_, lean_object* v_heq_2433_, lean_object* v_i_2434_, lean_object* v_k_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15(v_00_u03b2_2430_, v_keys_2431_, v_vals_2432_, v_heq_2433_, v_i_2434_, v_k_2435_);
lean_dec(v_k_2435_);
lean_dec_ref(v_vals_2432_);
lean_dec_ref(v_keys_2431_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_2437_, lean_object* v_x_2438_, lean_object* v_x_2439_, lean_object* v_x_2440_, lean_object* v_x_2441_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(v_x_2438_, v_x_2439_, v_x_2440_, v_x_2441_);
return v___x_2442_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__10));
v___x_2470_ = l_Lean_mkAtom(v___x_2469_);
return v___x_2470_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2471_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__12, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__12_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__12);
v___x_2472_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2473_ = lean_array_push(v___x_2472_, v___x_2471_);
return v___x_2473_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__17));
v___x_2483_ = l_Lean_mkAtom(v___x_2482_);
return v___x_2483_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__18, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__18_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__18);
v___x_2485_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2486_ = lean_array_push(v___x_2485_, v___x_2484_);
return v___x_2486_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__20(void){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2487_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__19, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__19_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__19);
v___x_2488_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__16));
v___x_2489_ = lean_box(2);
v___x_2490_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
lean_ctor_set(v___x_2490_, 1, v___x_2488_);
lean_ctor_set(v___x_2490_, 2, v___x_2487_);
return v___x_2490_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__21(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2491_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__20, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__20_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__20);
v___x_2492_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__13, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__13_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__13);
v___x_2493_ = lean_array_push(v___x_2492_, v___x_2491_);
return v___x_2493_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__22(void){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2494_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__21, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__21_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__21);
v___x_2495_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__11));
v___x_2496_ = lean_box(2);
v___x_2497_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v___x_2495_);
lean_ctor_set(v___x_2497_, 2, v___x_2494_);
return v___x_2497_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2498_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__22, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__22_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__22);
v___x_2499_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2500_ = lean_array_push(v___x_2499_, v___x_2498_);
return v___x_2500_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2501_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__23, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__23_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__23);
v___x_2502_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__9));
v___x_2503_ = lean_box(2);
v___x_2504_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
lean_ctor_set(v___x_2504_, 1, v___x_2502_);
lean_ctor_set(v___x_2504_, 2, v___x_2501_);
return v___x_2504_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__25(void){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__24, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__24_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__24);
v___x_2506_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2507_ = lean_array_push(v___x_2506_, v___x_2505_);
return v___x_2507_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__26(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2508_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__25, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__25_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__25);
v___x_2509_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__7));
v___x_2510_ = lean_box(2);
v___x_2511_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v___x_2509_);
lean_ctor_set(v___x_2511_, 2, v___x_2508_);
return v___x_2511_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__27(void){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__26, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__26_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__26);
v___x_2513_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2514_ = lean_array_push(v___x_2513_, v___x_2512_);
return v___x_2514_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__28(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2515_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__27, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__27_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__27);
v___x_2516_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__4));
v___x_2517_ = lean_box(2);
v___x_2518_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
lean_ctor_set(v___x_2518_, 1, v___x_2516_);
lean_ctor_set(v___x_2518_, 2, v___x_2515_);
return v___x_2518_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1(void){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__28, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__28_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__28);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(lean_object* v_msg_2520_){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = lean_box(0);
v___x_2522_ = lean_panic_fn_borrowed(v___x_2521_, v_msg_2520_);
return v___x_2522_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2525_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2));
v___x_2526_ = lean_unsigned_to_nat(17u);
v___x_2527_ = lean_unsigned_to_nat(203u);
v___x_2528_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___lam__0___closed__1));
v___x_2529_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___lam__0___closed__0));
v___x_2530_ = l_mkPanicMessageWithDecl(v___x_2529_, v___x_2528_, v___x_2527_, v___x_2526_, v___x_2525_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__0(lean_object* v_x_2531_, lean_object* v_e_2532_){
_start:
{
lean_object* v___y_2534_; 
switch(lean_obj_tag(v_e_2532_))
{
case 3:
{
lean_object* v_thm_2541_; lean_object* v_origin_2542_; 
v_thm_2541_ = lean_ctor_get(v_e_2532_, 0);
v_origin_2542_ = lean_ctor_get(v_thm_2541_, 5);
if (lean_obj_tag(v_origin_2542_) == 0)
{
lean_object* v_declName_2543_; 
v_declName_2543_ = lean_ctor_get(v_origin_2542_, 0);
lean_inc(v_declName_2543_);
v___y_2534_ = v_declName_2543_;
goto v___jp_2533_;
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___lam__0___closed__2, &l_Lean_Meta_Grind_mkExtension___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2);
v___x_2545_ = l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(v___x_2544_);
v___y_2534_ = v___x_2545_;
goto v___jp_2533_;
}
}
case 4:
{
lean_object* v_thm_2546_; lean_object* v_origin_2547_; 
v_thm_2546_ = lean_ctor_get(v_e_2532_, 0);
v_origin_2547_ = lean_ctor_get(v_thm_2546_, 3);
if (lean_obj_tag(v_origin_2547_) == 0)
{
lean_object* v_declName_2548_; 
v_declName_2548_ = lean_ctor_get(v_origin_2547_, 0);
lean_inc(v_declName_2548_);
v___y_2534_ = v_declName_2548_;
goto v___jp_2533_;
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___lam__0___closed__2, &l_Lean_Meta_Grind_mkExtension___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2);
v___x_2550_ = l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(v___x_2549_);
v___y_2534_ = v___x_2550_;
goto v___jp_2533_;
}
}
default: 
{
lean_object* v_declName_2551_; 
v_declName_2551_ = lean_ctor_get(v_e_2532_, 0);
lean_inc(v_declName_2551_);
v___y_2534_ = v_declName_2551_;
goto v___jp_2533_;
}
}
v___jp_2533_:
{
uint8_t v___x_2535_; 
v___x_2535_ = l_Lean_isPrivateName(v___y_2534_);
lean_dec(v___y_2534_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2536_, 0, v_e_2532_);
lean_inc_ref_n(v___x_2536_, 2);
v___x_2537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
lean_ctor_set(v___x_2537_, 2, v___x_2536_);
return v___x_2537_;
}
else
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2538_ = lean_box(0);
v___x_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2539_, 0, v_e_2532_);
v___x_2540_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2538_);
lean_ctor_set(v___x_2540_, 1, v___x_2538_);
lean_ctor_set(v___x_2540_, 2, v___x_2539_);
return v___x_2540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__0___boxed(lean_object* v_x_2552_, lean_object* v_e_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_Meta_Grind_mkExtension___lam__0(v_x_2552_, v_e_2553_);
lean_dec_ref(v_x_2552_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__1(lean_object* v___y_2555_){
_start:
{
lean_inc_ref(v___y_2555_);
return v___y_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__1___boxed(lean_object* v___y_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_Meta_Grind_mkExtension___lam__1(v___y_2556_);
lean_dec_ref(v___y_2556_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension(lean_object* v_name_2561_){
_start:
{
lean_object* v___f_2563_; lean_object* v___f_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___f_2563_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__0));
v___f_2564_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__1));
v___x_2565_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__2));
v___x_2566_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2);
v___x_2567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2567_, 0, v_name_2561_);
lean_ctor_set(v___x_2567_, 1, v___x_2565_);
lean_ctor_set(v___x_2567_, 2, v___x_2566_);
lean_ctor_set(v___x_2567_, 3, v___f_2564_);
lean_ctor_set(v___x_2567_, 4, v___f_2563_);
v___x_2568_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___boxed(lean_object* v_name_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_Meta_Grind_mkExtension(v_name_2569_);
return v_res_2571_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2572_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0);
v___x_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
return v___x_2574_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2575_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1);
v___x_2576_ = lean_unsigned_to_nat(0u);
v___x_2577_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
lean_ctor_set(v___x_2577_, 2, v___x_2576_);
lean_ctor_set(v___x_2577_, 3, v___x_2576_);
lean_ctor_set(v___x_2577_, 4, v___x_2575_);
lean_ctor_set(v___x_2577_, 5, v___x_2575_);
lean_ctor_set(v___x_2577_, 6, v___x_2575_);
lean_ctor_set(v___x_2577_, 7, v___x_2575_);
lean_ctor_set(v___x_2577_, 8, v___x_2575_);
lean_ctor_set(v___x_2577_, 9, v___x_2575_);
return v___x_2577_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2578_ = lean_unsigned_to_nat(32u);
v___x_2579_ = lean_mk_empty_array_with_capacity(v___x_2578_);
v___x_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
return v___x_2580_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2581_ = ((size_t)5ULL);
v___x_2582_ = lean_unsigned_to_nat(0u);
v___x_2583_ = lean_unsigned_to_nat(32u);
v___x_2584_ = lean_mk_empty_array_with_capacity(v___x_2583_);
v___x_2585_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3);
v___x_2586_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
lean_ctor_set(v___x_2586_, 1, v___x_2584_);
lean_ctor_set(v___x_2586_, 2, v___x_2582_);
lean_ctor_set(v___x_2586_, 3, v___x_2582_);
lean_ctor_set_usize(v___x_2586_, 4, v___x_2581_);
return v___x_2586_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2587_ = lean_box(1);
v___x_2588_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4);
v___x_2589_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1);
v___x_2590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
lean_ctor_set(v___x_2590_, 1, v___x_2588_);
lean_ctor_set(v___x_2590_, 2, v___x_2587_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(lean_object* v_msgData_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v___x_2595_; lean_object* v_env_2596_; lean_object* v_options_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2595_ = lean_st_ref_get(v___y_2593_);
v_env_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc_ref(v_env_2596_);
lean_dec(v___x_2595_);
v_options_2597_ = lean_ctor_get(v___y_2592_, 2);
v___x_2598_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2);
v___x_2599_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2597_);
v___x_2600_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2600_, 0, v_env_2596_);
lean_ctor_set(v___x_2600_, 1, v___x_2598_);
lean_ctor_set(v___x_2600_, 2, v___x_2599_);
lean_ctor_set(v___x_2600_, 3, v_options_2597_);
v___x_2601_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set(v___x_2601_, 1, v_msgData_2591_);
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___boxed(lean_object* v_msgData_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(v_msgData_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(lean_object* v_msg_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_ref_2612_; lean_object* v___x_2613_; lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2622_; 
v_ref_2612_ = lean_ctor_get(v___y_2609_, 5);
v___x_2613_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(v_msg_2608_, v___y_2609_, v___y_2610_);
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2622_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2622_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; lean_object* v___x_2620_; 
lean_inc(v_ref_2612_);
v___x_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2618_, 0, v_ref_2612_);
lean_ctor_set(v___x_2618_, 1, v_a_2614_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set_tag(v___x_2616_, 1);
lean_ctor_set(v___x_2616_, 0, v___x_2618_);
v___x_2620_ = v___x_2616_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg___boxed(lean_object* v_msg_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v_msg_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
return v_res_2627_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2629_ = ((lean_object*)(l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__0));
v___x_2630_ = l_Lean_stringToMessageData(v___x_2629_);
return v___x_2630_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3(void){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2632_ = ((lean_object*)(l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__2));
v___x_2633_ = l_Lean_stringToMessageData(v___x_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object* v_declName_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_){
_start:
{
lean_object* v___x_2638_; uint8_t v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2638_ = lean_obj_once(&l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1, &l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1);
v___x_2639_ = 0;
v___x_2640_ = l_Lean_MessageData_ofConstName(v_declName_2634_, v___x_2639_);
v___x_2641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2638_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
v___x_2642_ = lean_obj_once(&l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3, &l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3_once, _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3);
v___x_2643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2641_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
v___x_2644_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v___x_2643_, v_a_2635_, v_a_2636_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___boxed(lean_object* v_declName_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2645_, v_a_2646_, v_a_2647_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(lean_object* v_00_u03b1_2650_, lean_object* v_declName_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2651_, v_a_2652_, v_a_2653_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___boxed(lean_object* v_00_u03b1_2656_, lean_object* v_declName_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(v_00_u03b1_2656_, v_declName_2657_, v_a_2658_, v_a_2659_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(lean_object* v_00_u03b1_2662_, lean_object* v_msg_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v_msg_2663_, v___y_2664_, v___y_2665_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___boxed(lean_object* v_00_u03b1_2668_, lean_object* v_msg_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(v_00_u03b1_2668_, v_msg_2669_, v___y_2670_, v___y_2671_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
return v_res_2673_;
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
