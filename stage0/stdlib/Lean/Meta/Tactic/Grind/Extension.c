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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(lean_object* v_x_42_, size_t v_x_43_, size_t v_x_44_, lean_object* v_x_45_, lean_object* v_x_46_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
lean_object* v_es_47_; size_t v___x_48_; size_t v___x_49_; lean_object* v_j_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v_es_47_ = lean_ctor_get(v_x_42_, 0);
v___x_48_ = ((size_t)31ULL);
v___x_49_ = lean_usize_land(v_x_43_, v___x_48_);
v_j_50_ = lean_usize_to_nat(v___x_49_);
v___x_51_ = lean_array_get_size(v_es_47_);
v___x_52_ = lean_nat_dec_lt(v_j_50_, v___x_51_);
if (v___x_52_ == 0)
{
lean_dec(v_j_50_);
lean_dec(v_x_46_);
lean_dec(v_x_45_);
return v_x_42_;
}
else
{
lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_91_; 
lean_inc_ref(v_es_47_);
v_isSharedCheck_91_ = !lean_is_exclusive(v_x_42_);
if (v_isSharedCheck_91_ == 0)
{
lean_object* v_unused_92_; 
v_unused_92_ = lean_ctor_get(v_x_42_, 0);
lean_dec(v_unused_92_);
v___x_54_ = v_x_42_;
v_isShared_55_ = v_isSharedCheck_91_;
goto v_resetjp_53_;
}
else
{
lean_dec(v_x_42_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_91_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v_v_56_; lean_object* v___x_57_; lean_object* v_xs_x27_58_; lean_object* v___y_60_; 
v_v_56_ = lean_array_fget(v_es_47_, v_j_50_);
v___x_57_ = lean_box(0);
v_xs_x27_58_ = lean_array_fset(v_es_47_, v_j_50_, v___x_57_);
switch(lean_obj_tag(v_v_56_))
{
case 0:
{
lean_object* v_key_65_; lean_object* v_val_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_76_; 
v_key_65_ = lean_ctor_get(v_v_56_, 0);
v_val_66_ = lean_ctor_get(v_v_56_, 1);
v_isSharedCheck_76_ = !lean_is_exclusive(v_v_56_);
if (v_isSharedCheck_76_ == 0)
{
v___x_68_ = v_v_56_;
v_isShared_69_ = v_isSharedCheck_76_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_val_66_);
lean_inc(v_key_65_);
lean_dec(v_v_56_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_76_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
uint8_t v___x_70_; 
v___x_70_ = lean_name_eq(v_x_45_, v_key_65_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_del_object(v___x_68_);
v___x_71_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_65_, v_val_66_, v_x_45_, v_x_46_);
v___x_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
v___y_60_ = v___x_72_;
goto v___jp_59_;
}
else
{
lean_object* v___x_74_; 
lean_dec(v_val_66_);
lean_dec(v_key_65_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 1, v_x_46_);
lean_ctor_set(v___x_68_, 0, v_x_45_);
v___x_74_ = v___x_68_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_x_45_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_x_46_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
v___y_60_ = v___x_74_;
goto v___jp_59_;
}
}
}
}
case 1:
{
lean_object* v_node_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_89_; 
v_node_77_ = lean_ctor_get(v_v_56_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v_v_56_);
if (v_isSharedCheck_89_ == 0)
{
v___x_79_ = v_v_56_;
v_isShared_80_ = v_isSharedCheck_89_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_node_77_);
lean_dec(v_v_56_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_89_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
size_t v___x_81_; size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_81_ = ((size_t)5ULL);
v___x_82_ = lean_usize_shift_right(v_x_43_, v___x_81_);
v___x_83_ = ((size_t)1ULL);
v___x_84_ = lean_usize_add(v_x_44_, v___x_83_);
v___x_85_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_node_77_, v___x_82_, v___x_84_, v_x_45_, v_x_46_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_85_);
v___x_87_ = v___x_79_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
v___y_60_ = v___x_87_;
goto v___jp_59_;
}
}
}
default: 
{
lean_object* v___x_90_; 
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v_x_45_);
lean_ctor_set(v___x_90_, 1, v_x_46_);
v___y_60_ = v___x_90_;
goto v___jp_59_;
}
}
v___jp_59_:
{
lean_object* v___x_61_; lean_object* v___x_63_; 
v___x_61_ = lean_array_fset(v_xs_x27_58_, v_j_50_, v___y_60_);
lean_dec(v_j_50_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v___x_61_);
v___x_63_ = v___x_54_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
}
else
{
lean_object* v_ks_93_; lean_object* v_vs_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_114_; 
v_ks_93_ = lean_ctor_get(v_x_42_, 0);
v_vs_94_ = lean_ctor_get(v_x_42_, 1);
v_isSharedCheck_114_ = !lean_is_exclusive(v_x_42_);
if (v_isSharedCheck_114_ == 0)
{
v___x_96_ = v_x_42_;
v_isShared_97_ = v_isSharedCheck_114_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_vs_94_);
lean_inc(v_ks_93_);
lean_dec(v_x_42_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_114_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_ks_93_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_vs_94_);
v___x_99_ = v_reuseFailAlloc_113_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v_newNode_100_; uint8_t v___y_102_; size_t v___x_108_; uint8_t v___x_109_; 
v_newNode_100_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1___redArg(v___x_99_, v_x_45_, v_x_46_);
v___x_108_ = ((size_t)7ULL);
v___x_109_ = lean_usize_dec_le(v___x_108_, v_x_44_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_110_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_100_);
v___x_111_ = lean_unsigned_to_nat(4u);
v___x_112_ = lean_nat_dec_lt(v___x_110_, v___x_111_);
lean_dec(v___x_110_);
v___y_102_ = v___x_112_;
goto v___jp_101_;
}
else
{
v___y_102_ = v___x_109_;
goto v___jp_101_;
}
v___jp_101_:
{
if (v___y_102_ == 0)
{
lean_object* v_ks_103_; lean_object* v_vs_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_ks_103_ = lean_ctor_get(v_newNode_100_, 0);
lean_inc_ref(v_ks_103_);
v_vs_104_ = lean_ctor_get(v_newNode_100_, 1);
lean_inc_ref(v_vs_104_);
lean_dec_ref(v_newNode_100_);
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0);
v___x_107_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_x_44_, v_ks_103_, v_vs_104_, v___x_105_, v___x_106_);
lean_dec_ref(v_vs_104_);
lean_dec_ref(v_ks_103_);
return v___x_107_;
}
else
{
return v_newNode_100_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(size_t v_depth_115_, lean_object* v_keys_116_, lean_object* v_vals_117_, lean_object* v_i_118_, lean_object* v_entries_119_){
_start:
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_array_get_size(v_keys_116_);
v___x_121_ = lean_nat_dec_lt(v_i_118_, v___x_120_);
if (v___x_121_ == 0)
{
lean_dec(v_i_118_);
return v_entries_119_;
}
else
{
lean_object* v_k_122_; lean_object* v_v_123_; uint64_t v___y_125_; 
v_k_122_ = lean_array_fget_borrowed(v_keys_116_, v_i_118_);
v_v_123_ = lean_array_fget_borrowed(v_vals_117_, v_i_118_);
if (lean_obj_tag(v_k_122_) == 0)
{
uint64_t v___x_136_; 
v___x_136_ = 1723ULL;
v___y_125_ = v___x_136_;
goto v___jp_124_;
}
else
{
uint64_t v_hash_137_; 
v_hash_137_ = lean_ctor_get_uint64(v_k_122_, sizeof(void*)*2);
v___y_125_ = v_hash_137_;
goto v___jp_124_;
}
v___jp_124_:
{
size_t v_h_126_; size_t v___x_127_; lean_object* v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; size_t v_h_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_h_126_ = lean_uint64_to_usize(v___y_125_);
v___x_127_ = ((size_t)5ULL);
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_sub(v_depth_115_, v___x_129_);
v___x_131_ = lean_usize_mul(v___x_127_, v___x_130_);
v_h_132_ = lean_usize_shift_right(v_h_126_, v___x_131_);
v___x_133_ = lean_nat_add(v_i_118_, v___x_128_);
lean_dec(v_i_118_);
lean_inc(v_v_123_);
lean_inc(v_k_122_);
v___x_134_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_entries_119_, v_h_132_, v_depth_115_, v_k_122_, v_v_123_);
v_i_118_ = v___x_133_;
v_entries_119_ = v___x_134_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_138_, lean_object* v_keys_139_, lean_object* v_vals_140_, lean_object* v_i_141_, lean_object* v_entries_142_){
_start:
{
size_t v_depth_boxed_143_; lean_object* v_res_144_; 
v_depth_boxed_143_ = lean_unbox_usize(v_depth_138_);
lean_dec(v_depth_138_);
v_res_144_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_143_, v_keys_139_, v_vals_140_, v_i_141_, v_entries_142_);
lean_dec_ref(v_vals_140_);
lean_dec_ref(v_keys_139_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
size_t v_x_351__boxed_150_; size_t v_x_352__boxed_151_; lean_object* v_res_152_; 
v_x_351__boxed_150_ = lean_unbox_usize(v_x_146_);
lean_dec(v_x_146_);
v_x_352__boxed_151_ = lean_unbox_usize(v_x_147_);
lean_dec(v_x_147_);
v_res_152_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_145_, v_x_351__boxed_150_, v_x_352__boxed_151_, v_x_148_, v_x_149_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(lean_object* v_x_153_, lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
uint64_t v___y_157_; 
if (lean_obj_tag(v_x_154_) == 0)
{
uint64_t v___x_161_; 
v___x_161_ = 1723ULL;
v___y_157_ = v___x_161_;
goto v___jp_156_;
}
else
{
uint64_t v_hash_162_; 
v_hash_162_ = lean_ctor_get_uint64(v_x_154_, sizeof(void*)*2);
v___y_157_ = v_hash_162_;
goto v___jp_156_;
}
v___jp_156_:
{
size_t v___x_158_; size_t v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_uint64_to_usize(v___y_157_);
v___x_159_ = ((size_t)1ULL);
v___x_160_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_153_, v___x_158_, v___x_159_, v_x_154_, v_x_155_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_insert(lean_object* v_s_163_, lean_object* v_declName_164_, uint8_t v_eager_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_box(v_eager_165_);
v___x_167_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_s_163_, v_declName_164_, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_insert___boxed(lean_object* v_s_168_, lean_object* v_declName_169_, lean_object* v_eager_170_){
_start:
{
uint8_t v_eager_boxed_171_; lean_object* v_res_172_; 
v_eager_boxed_171_ = lean_unbox(v_eager_170_);
v_res_172_ = l_Lean_Meta_Grind_CasesTypes_insert(v_s_168_, v_declName_169_, v_eager_boxed_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0(lean_object* v_00_u03b2_173_, lean_object* v_x_174_, lean_object* v_x_175_, lean_object* v_x_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_x_174_, v_x_175_, v_x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0(lean_object* v_00_u03b2_178_, lean_object* v_x_179_, size_t v_x_180_, size_t v_x_181_, lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_179_, v_x_180_, v_x_181_, v_x_182_, v_x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_185_, lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
size_t v_x_539__boxed_191_; size_t v_x_540__boxed_192_; lean_object* v_res_193_; 
v_x_539__boxed_191_ = lean_unbox_usize(v_x_187_);
lean_dec(v_x_187_);
v_x_540__boxed_192_ = lean_unbox_usize(v_x_188_);
lean_dec(v_x_188_);
v_res_193_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0(v_00_u03b2_185_, v_x_186_, v_x_539__boxed_191_, v_x_540__boxed_192_, v_x_189_, v_x_190_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_194_, lean_object* v_n_195_, lean_object* v_k_196_, lean_object* v_v_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1___redArg(v_n_195_, v_k_196_, v_v_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_199_, size_t v_depth_200_, lean_object* v_keys_201_, lean_object* v_vals_202_, lean_object* v_heq_203_, lean_object* v_i_204_, lean_object* v_entries_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_depth_200_, v_keys_201_, v_vals_202_, v_i_204_, v_entries_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_207_, lean_object* v_depth_208_, lean_object* v_keys_209_, lean_object* v_vals_210_, lean_object* v_heq_211_, lean_object* v_i_212_, lean_object* v_entries_213_){
_start:
{
size_t v_depth_boxed_214_; lean_object* v_res_215_; 
v_depth_boxed_214_ = lean_unbox_usize(v_depth_208_);
lean_dec(v_depth_208_);
v_res_215_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2(v_00_u03b2_207_, v_depth_boxed_214_, v_keys_209_, v_vals_210_, v_heq_211_, v_i_212_, v_entries_213_);
lean_dec_ref(v_vals_210_);
lean_dec_ref(v_keys_209_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_216_, lean_object* v_x_217_, lean_object* v_x_218_, lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_217_, v_x_218_, v_x_219_, v_x_220_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0(void){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0, &l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default(void){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1, &l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__1);
return v___x_225_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities(void){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default;
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SymbolPriorities_insert(lean_object* v_s_227_, lean_object* v_declName_228_, lean_object* v_prio_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_s_227_, v_declName_228_, v_prio_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(lean_object* v_x_231_){
_start:
{
switch(lean_obj_tag(v_x_231_))
{
case 0:
{
lean_object* v___x_232_; 
v___x_232_ = lean_unsigned_to_nat(0u);
return v___x_232_;
}
case 1:
{
lean_object* v___x_233_; 
v___x_233_ = lean_unsigned_to_nat(1u);
return v___x_233_;
}
case 2:
{
lean_object* v___x_234_; 
v___x_234_ = lean_unsigned_to_nat(2u);
return v___x_234_;
}
case 3:
{
lean_object* v___x_235_; 
v___x_235_ = lean_unsigned_to_nat(3u);
return v___x_235_;
}
case 4:
{
lean_object* v___x_236_; 
v___x_236_ = lean_unsigned_to_nat(4u);
return v___x_236_;
}
case 5:
{
lean_object* v___x_237_; 
v___x_237_ = lean_unsigned_to_nat(5u);
return v___x_237_;
}
case 6:
{
lean_object* v___x_238_; 
v___x_238_ = lean_unsigned_to_nat(6u);
return v___x_238_;
}
case 7:
{
lean_object* v___x_239_; 
v___x_239_ = lean_unsigned_to_nat(7u);
return v___x_239_;
}
case 8:
{
lean_object* v___x_240_; 
v___x_240_ = lean_unsigned_to_nat(8u);
return v___x_240_;
}
default: 
{
lean_object* v___x_241_; 
v___x_241_ = lean_unsigned_to_nat(9u);
return v___x_241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx___boxed(lean_object* v_x_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(v_x_242_);
lean_dec(v_x_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(lean_object* v_t_244_, lean_object* v_k_245_){
_start:
{
switch(lean_obj_tag(v_t_244_))
{
case 0:
{
uint8_t v_gen_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_gen_246_ = lean_ctor_get_uint8(v_t_244_, 0);
v___x_247_ = lean_box(v_gen_246_);
v___x_248_ = lean_apply_1(v_k_245_, v___x_247_);
return v___x_248_;
}
case 1:
{
uint8_t v_gen_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_gen_249_ = lean_ctor_get_uint8(v_t_244_, 0);
v___x_250_ = lean_box(v_gen_249_);
v___x_251_ = lean_apply_1(v_k_245_, v___x_250_);
return v___x_251_;
}
case 2:
{
uint8_t v_gen_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_gen_252_ = lean_ctor_get_uint8(v_t_244_, 0);
v___x_253_ = lean_box(v_gen_252_);
v___x_254_ = lean_apply_1(v_k_245_, v___x_253_);
return v___x_254_;
}
case 5:
{
uint8_t v_gen_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_gen_255_ = lean_ctor_get_uint8(v_t_244_, 0);
v___x_256_ = lean_box(v_gen_255_);
v___x_257_ = lean_apply_1(v_k_245_, v___x_256_);
return v___x_257_;
}
case 8:
{
uint8_t v_gen_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_gen_258_ = lean_ctor_get_uint8(v_t_244_, 0);
v___x_259_ = lean_box(v_gen_258_);
v___x_260_ = lean_apply_1(v_k_245_, v___x_259_);
return v___x_260_;
}
default: 
{
return v_k_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg___boxed(lean_object* v_t_261_, lean_object* v_k_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_261_, v_k_262_);
lean_dec(v_t_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim(lean_object* v_motive_264_, lean_object* v_ctorIdx_265_, lean_object* v_t_266_, lean_object* v_h_267_, lean_object* v_k_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_266_, v_k_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___boxed(lean_object* v_motive_270_, lean_object* v_ctorIdx_271_, lean_object* v_t_272_, lean_object* v_h_273_, lean_object* v_k_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim(v_motive_270_, v_ctorIdx_271_, v_t_272_, v_h_273_, v_k_274_);
lean_dec(v_t_272_);
lean_dec(v_ctorIdx_271_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg(lean_object* v_t_276_, lean_object* v_eqLhs_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_276_, v_eqLhs_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg___boxed(lean_object* v_t_279_, lean_object* v_eqLhs_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg(v_t_279_, v_eqLhs_280_);
lean_dec(v_t_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim(lean_object* v_motive_282_, lean_object* v_t_283_, lean_object* v_h_284_, lean_object* v_eqLhs_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_283_, v_eqLhs_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___boxed(lean_object* v_motive_287_, lean_object* v_t_288_, lean_object* v_h_289_, lean_object* v_eqLhs_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim(v_motive_287_, v_t_288_, v_h_289_, v_eqLhs_290_);
lean_dec(v_t_288_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg(lean_object* v_t_292_, lean_object* v_eqRhs_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_292_, v_eqRhs_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg___boxed(lean_object* v_t_295_, lean_object* v_eqRhs_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg(v_t_295_, v_eqRhs_296_);
lean_dec(v_t_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim(lean_object* v_motive_298_, lean_object* v_t_299_, lean_object* v_h_300_, lean_object* v_eqRhs_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_299_, v_eqRhs_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___boxed(lean_object* v_motive_303_, lean_object* v_t_304_, lean_object* v_h_305_, lean_object* v_eqRhs_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim(v_motive_303_, v_t_304_, v_h_305_, v_eqRhs_306_);
lean_dec(v_t_304_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg(lean_object* v_t_308_, lean_object* v_eqBoth_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_308_, v_eqBoth_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg___boxed(lean_object* v_t_311_, lean_object* v_eqBoth_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg(v_t_311_, v_eqBoth_312_);
lean_dec(v_t_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim(lean_object* v_motive_314_, lean_object* v_t_315_, lean_object* v_h_316_, lean_object* v_eqBoth_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_315_, v_eqBoth_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___boxed(lean_object* v_motive_319_, lean_object* v_t_320_, lean_object* v_h_321_, lean_object* v_eqBoth_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim(v_motive_319_, v_t_320_, v_h_321_, v_eqBoth_322_);
lean_dec(v_t_320_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg(lean_object* v_t_324_, lean_object* v_eqBwd_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_324_, v_eqBwd_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg___boxed(lean_object* v_t_327_, lean_object* v_eqBwd_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg(v_t_327_, v_eqBwd_328_);
lean_dec(v_t_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim(lean_object* v_motive_330_, lean_object* v_t_331_, lean_object* v_h_332_, lean_object* v_eqBwd_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_331_, v_eqBwd_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___boxed(lean_object* v_motive_335_, lean_object* v_t_336_, lean_object* v_h_337_, lean_object* v_eqBwd_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim(v_motive_335_, v_t_336_, v_h_337_, v_eqBwd_338_);
lean_dec(v_t_336_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg(lean_object* v_t_340_, lean_object* v_fwd_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_340_, v_fwd_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg___boxed(lean_object* v_t_343_, lean_object* v_fwd_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg(v_t_343_, v_fwd_344_);
lean_dec(v_t_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim(lean_object* v_motive_346_, lean_object* v_t_347_, lean_object* v_h_348_, lean_object* v_fwd_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_347_, v_fwd_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___boxed(lean_object* v_motive_351_, lean_object* v_t_352_, lean_object* v_h_353_, lean_object* v_fwd_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim(v_motive_351_, v_t_352_, v_h_353_, v_fwd_354_);
lean_dec(v_t_352_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg(lean_object* v_t_356_, lean_object* v_bwd_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_356_, v_bwd_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg___boxed(lean_object* v_t_359_, lean_object* v_bwd_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg(v_t_359_, v_bwd_360_);
lean_dec(v_t_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim(lean_object* v_motive_362_, lean_object* v_t_363_, lean_object* v_h_364_, lean_object* v_bwd_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_363_, v_bwd_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___boxed(lean_object* v_motive_367_, lean_object* v_t_368_, lean_object* v_h_369_, lean_object* v_bwd_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim(v_motive_367_, v_t_368_, v_h_369_, v_bwd_370_);
lean_dec(v_t_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg(lean_object* v_t_372_, lean_object* v_leftRight_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_372_, v_leftRight_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg___boxed(lean_object* v_t_375_, lean_object* v_leftRight_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg(v_t_375_, v_leftRight_376_);
lean_dec(v_t_375_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim(lean_object* v_motive_378_, lean_object* v_t_379_, lean_object* v_h_380_, lean_object* v_leftRight_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_379_, v_leftRight_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___boxed(lean_object* v_motive_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_leftRight_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim(v_motive_383_, v_t_384_, v_h_385_, v_leftRight_386_);
lean_dec(v_t_384_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg(lean_object* v_t_388_, lean_object* v_rightLeft_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_388_, v_rightLeft_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg___boxed(lean_object* v_t_391_, lean_object* v_rightLeft_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg(v_t_391_, v_rightLeft_392_);
lean_dec(v_t_391_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim(lean_object* v_motive_394_, lean_object* v_t_395_, lean_object* v_h_396_, lean_object* v_rightLeft_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_395_, v_rightLeft_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___boxed(lean_object* v_motive_399_, lean_object* v_t_400_, lean_object* v_h_401_, lean_object* v_rightLeft_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim(v_motive_399_, v_t_400_, v_h_401_, v_rightLeft_402_);
lean_dec(v_t_400_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg(lean_object* v_t_404_, lean_object* v_default_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_404_, v_default_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg___boxed(lean_object* v_t_407_, lean_object* v_default_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg(v_t_407_, v_default_408_);
lean_dec(v_t_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim(lean_object* v_motive_410_, lean_object* v_t_411_, lean_object* v_h_412_, lean_object* v_default_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_411_, v_default_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___boxed(lean_object* v_motive_415_, lean_object* v_t_416_, lean_object* v_h_417_, lean_object* v_default_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Meta_Grind_EMatchTheoremKind_default_elim(v_motive_415_, v_t_416_, v_h_417_, v_default_418_);
lean_dec(v_t_416_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg(lean_object* v_t_420_, lean_object* v_user_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_420_, v_user_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg___boxed(lean_object* v_t_423_, lean_object* v_user_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg(v_t_423_, v_user_424_);
lean_dec(v_t_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim(lean_object* v_motive_426_, lean_object* v_t_427_, lean_object* v_h_428_, lean_object* v_user_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_427_, v_user_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___boxed(lean_object* v_motive_431_, lean_object* v_t_432_, lean_object* v_h_433_, lean_object* v_user_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Meta_Grind_EMatchTheoremKind_user_elim(v_motive_431_, v_t_432_, v_h_433_, v_user_434_);
lean_dec(v_t_432_);
return v_res_435_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; uint8_t v_gen_446_; uint8_t v_gen_x27_447_; 
v___x_442_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(v_x_440_);
v___x_443_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(v_x_441_);
v___x_444_ = lean_nat_dec_eq(v___x_442_, v___x_443_);
lean_dec(v___x_443_);
lean_dec(v___x_442_);
if (v___x_444_ == 0)
{
return v___x_444_;
}
else
{
switch(lean_obj_tag(v_x_440_))
{
case 0:
{
uint8_t v_gen_448_; uint8_t v_gen_449_; 
v_gen_448_ = lean_ctor_get_uint8(v_x_440_, 0);
v_gen_449_ = lean_ctor_get_uint8(v_x_441_, 0);
v_gen_446_ = v_gen_448_;
v_gen_x27_447_ = v_gen_449_;
goto v___jp_445_;
}
case 1:
{
uint8_t v_gen_450_; uint8_t v_gen_451_; 
v_gen_450_ = lean_ctor_get_uint8(v_x_440_, 0);
v_gen_451_ = lean_ctor_get_uint8(v_x_441_, 0);
v_gen_446_ = v_gen_450_;
v_gen_x27_447_ = v_gen_451_;
goto v___jp_445_;
}
case 2:
{
uint8_t v_gen_452_; uint8_t v_gen_453_; 
v_gen_452_ = lean_ctor_get_uint8(v_x_440_, 0);
v_gen_453_ = lean_ctor_get_uint8(v_x_441_, 0);
v_gen_446_ = v_gen_452_;
v_gen_x27_447_ = v_gen_453_;
goto v___jp_445_;
}
case 5:
{
uint8_t v_gen_454_; uint8_t v_gen_455_; 
v_gen_454_ = lean_ctor_get_uint8(v_x_440_, 0);
v_gen_455_ = lean_ctor_get_uint8(v_x_441_, 0);
v_gen_446_ = v_gen_454_;
v_gen_x27_447_ = v_gen_455_;
goto v___jp_445_;
}
case 8:
{
uint8_t v_gen_456_; uint8_t v_gen_457_; 
v_gen_456_ = lean_ctor_get_uint8(v_x_440_, 0);
v_gen_457_ = lean_ctor_get_uint8(v_x_441_, 0);
v_gen_446_ = v_gen_456_;
v_gen_x27_447_ = v_gen_457_;
goto v___jp_445_;
}
default: 
{
return v___x_444_;
}
}
}
v___jp_445_:
{
if (v_gen_446_ == 0)
{
if (v_gen_x27_447_ == 0)
{
return v___x_444_;
}
else
{
return v_gen_446_;
}
}
else
{
return v_gen_x27_447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq___boxed(lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
uint8_t v_res_460_; lean_object* v_r_461_; 
v_res_460_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_x_458_, v_x_459_);
lean_dec(v_x_459_);
lean_dec(v_x_458_);
v_r_461_ = lean_box(v_res_460_);
return v_r_461_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(2u);
v___x_486_ = lean_nat_to_int(v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_nat_to_int(v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr(lean_object* v_x_513_, lean_object* v_prec_514_){
_start:
{
lean_object* v___y_516_; lean_object* v___y_523_; lean_object* v___y_530_; lean_object* v___y_537_; lean_object* v___y_544_; 
switch(lean_obj_tag(v_x_513_))
{
case 0:
{
uint8_t v_gen_550_; lean_object* v___y_552_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_gen_550_ = lean_ctor_get_uint8(v_x_513_, 0);
v___x_560_ = lean_unsigned_to_nat(1024u);
v___x_561_ = lean_nat_dec_le(v___x_560_, v_prec_514_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; 
v___x_562_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_552_ = v___x_562_;
goto v___jp_551_;
}
else
{
lean_object* v___x_563_; 
v___x_563_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_552_ = v___x_563_;
goto v___jp_551_;
}
v___jp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_553_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__12));
v___x_554_ = l_Bool_repr___redArg(v_gen_550_);
v___x_555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
lean_inc(v___y_552_);
v___x_556_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_556_, 0, v___y_552_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = 0;
v___x_558_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_558_, 0, v___x_556_);
lean_ctor_set_uint8(v___x_558_, sizeof(void*)*1, v___x_557_);
v___x_559_ = l_Repr_addAppParen(v___x_558_, v_prec_514_);
return v___x_559_;
}
}
case 1:
{
uint8_t v_gen_564_; lean_object* v___y_566_; lean_object* v___x_574_; uint8_t v___x_575_; 
v_gen_564_ = lean_ctor_get_uint8(v_x_513_, 0);
v___x_574_ = lean_unsigned_to_nat(1024u);
v___x_575_ = lean_nat_dec_le(v___x_574_, v_prec_514_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_566_ = v___x_576_;
goto v___jp_565_;
}
else
{
lean_object* v___x_577_; 
v___x_577_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_566_ = v___x_577_;
goto v___jp_565_;
}
v___jp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_567_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__17));
v___x_568_ = l_Bool_repr___redArg(v_gen_564_);
v___x_569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_567_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
lean_inc(v___y_566_);
v___x_570_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_570_, 0, v___y_566_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = 0;
v___x_572_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*1, v___x_571_);
v___x_573_ = l_Repr_addAppParen(v___x_572_, v_prec_514_);
return v___x_573_;
}
}
case 2:
{
uint8_t v_gen_578_; lean_object* v___y_580_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_gen_578_ = lean_ctor_get_uint8(v_x_513_, 0);
v___x_588_ = lean_unsigned_to_nat(1024u);
v___x_589_ = lean_nat_dec_le(v___x_588_, v_prec_514_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_580_ = v___x_590_;
goto v___jp_579_;
}
else
{
lean_object* v___x_591_; 
v___x_591_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_580_ = v___x_591_;
goto v___jp_579_;
}
v___jp_579_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_581_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__20));
v___x_582_ = l_Bool_repr___redArg(v_gen_578_);
v___x_583_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
lean_inc(v___y_580_);
v___x_584_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_584_, 0, v___y_580_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = 0;
v___x_586_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set_uint8(v___x_586_, sizeof(void*)*1, v___x_585_);
v___x_587_ = l_Repr_addAppParen(v___x_586_, v_prec_514_);
return v___x_587_;
}
}
case 3:
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(1024u);
v___x_593_ = lean_nat_dec_le(v___x_592_, v_prec_514_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
v___x_594_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_530_ = v___x_594_;
goto v___jp_529_;
}
else
{
lean_object* v___x_595_; 
v___x_595_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_530_ = v___x_595_;
goto v___jp_529_;
}
}
case 4:
{
lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_596_ = lean_unsigned_to_nat(1024u);
v___x_597_ = lean_nat_dec_le(v___x_596_, v_prec_514_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
v___x_598_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_537_ = v___x_598_;
goto v___jp_536_;
}
else
{
lean_object* v___x_599_; 
v___x_599_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_537_ = v___x_599_;
goto v___jp_536_;
}
}
case 5:
{
uint8_t v_gen_600_; lean_object* v___y_602_; lean_object* v___x_610_; uint8_t v___x_611_; 
v_gen_600_ = lean_ctor_get_uint8(v_x_513_, 0);
v___x_610_ = lean_unsigned_to_nat(1024u);
v___x_611_ = lean_nat_dec_le(v___x_610_, v_prec_514_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
v___x_612_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_602_ = v___x_612_;
goto v___jp_601_;
}
else
{
lean_object* v___x_613_; 
v___x_613_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_602_ = v___x_613_;
goto v___jp_601_;
}
v___jp_601_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_603_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__23));
v___x_604_ = l_Bool_repr___redArg(v_gen_600_);
v___x_605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
lean_inc(v___y_602_);
v___x_606_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_606_, 0, v___y_602_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = 0;
v___x_608_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set_uint8(v___x_608_, sizeof(void*)*1, v___x_607_);
v___x_609_ = l_Repr_addAppParen(v___x_608_, v_prec_514_);
return v___x_609_;
}
}
case 6:
{
lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_614_ = lean_unsigned_to_nat(1024u);
v___x_615_ = lean_nat_dec_le(v___x_614_, v_prec_514_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
v___x_616_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_523_ = v___x_616_;
goto v___jp_522_;
}
else
{
lean_object* v___x_617_; 
v___x_617_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_523_ = v___x_617_;
goto v___jp_522_;
}
}
case 7:
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(1024u);
v___x_619_ = lean_nat_dec_le(v___x_618_, v_prec_514_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
v___x_620_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_516_ = v___x_620_;
goto v___jp_515_;
}
else
{
lean_object* v___x_621_; 
v___x_621_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_516_ = v___x_621_;
goto v___jp_515_;
}
}
case 8:
{
uint8_t v_gen_622_; lean_object* v___y_624_; lean_object* v___x_632_; uint8_t v___x_633_; 
v_gen_622_ = lean_ctor_get_uint8(v_x_513_, 0);
v___x_632_ = lean_unsigned_to_nat(1024u);
v___x_633_ = lean_nat_dec_le(v___x_632_, v_prec_514_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
v___x_634_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_624_ = v___x_634_;
goto v___jp_623_;
}
else
{
lean_object* v___x_635_; 
v___x_635_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_624_ = v___x_635_;
goto v___jp_623_;
}
v___jp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_625_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__26));
v___x_626_ = l_Bool_repr___redArg(v_gen_622_);
v___x_627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
lean_inc(v___y_624_);
v___x_628_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_628_, 0, v___y_624_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = 0;
v___x_630_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set_uint8(v___x_630_, sizeof(void*)*1, v___x_629_);
v___x_631_ = l_Repr_addAppParen(v___x_630_, v_prec_514_);
return v___x_631_;
}
}
default: 
{
lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_636_ = lean_unsigned_to_nat(1024u);
v___x_637_ = lean_nat_dec_le(v___x_636_, v_prec_514_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
v___x_638_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_544_ = v___x_638_;
goto v___jp_543_;
}
else
{
lean_object* v___x_639_; 
v___x_639_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_544_ = v___x_639_;
goto v___jp_543_;
}
}
}
v___jp_515_:
{
lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_517_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__1));
lean_inc(v___y_516_);
v___x_518_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_518_, 0, v___y_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = 0;
v___x_520_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set_uint8(v___x_520_, sizeof(void*)*1, v___x_519_);
v___x_521_ = l_Repr_addAppParen(v___x_520_, v_prec_514_);
return v___x_521_;
}
v___jp_522_:
{
lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_524_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__3));
lean_inc(v___y_523_);
v___x_525_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_525_, 0, v___y_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = 0;
v___x_527_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*1, v___x_526_);
v___x_528_ = l_Repr_addAppParen(v___x_527_, v_prec_514_);
return v___x_528_;
}
v___jp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_531_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__5));
lean_inc(v___y_530_);
v___x_532_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_532_, 0, v___y_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = 0;
v___x_534_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*1, v___x_533_);
v___x_535_ = l_Repr_addAppParen(v___x_534_, v_prec_514_);
return v___x_535_;
}
v___jp_536_:
{
lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_538_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__7));
lean_inc(v___y_537_);
v___x_539_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_539_, 0, v___y_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = 0;
v___x_541_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set_uint8(v___x_541_, sizeof(void*)*1, v___x_540_);
v___x_542_ = l_Repr_addAppParen(v___x_541_, v_prec_514_);
return v___x_542_;
}
v___jp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_545_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__9));
lean_inc(v___y_544_);
v___x_546_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_546_, 0, v___y_544_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = 0;
v___x_548_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set_uint8(v___x_548_, sizeof(void*)*1, v___x_547_);
v___x_549_ = l_Repr_addAppParen(v___x_548_, v_prec_514_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___boxed(lean_object* v_x_640_, lean_object* v_prec_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr(v_x_640_, v_prec_641_);
lean_dec(v_prec_641_);
lean_dec(v_x_640_);
return v_res_642_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0(void){
_start:
{
uint64_t v___x_645_; uint64_t v___x_646_; uint64_t v___x_647_; 
v___x_645_ = 13ULL;
v___x_646_ = 0ULL;
v___x_647_ = lean_uint64_mix_hash(v___x_646_, v___x_645_);
return v___x_647_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1(void){
_start:
{
uint64_t v___x_648_; uint64_t v___x_649_; uint64_t v___x_650_; 
v___x_648_ = 11ULL;
v___x_649_ = 0ULL;
v___x_650_ = lean_uint64_mix_hash(v___x_649_, v___x_648_);
return v___x_650_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2(void){
_start:
{
uint64_t v___x_651_; uint64_t v___x_652_; uint64_t v___x_653_; 
v___x_651_ = 13ULL;
v___x_652_ = 1ULL;
v___x_653_ = lean_uint64_mix_hash(v___x_652_, v___x_651_);
return v___x_653_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3(void){
_start:
{
uint64_t v___x_654_; uint64_t v___x_655_; uint64_t v___x_656_; 
v___x_654_ = 11ULL;
v___x_655_ = 1ULL;
v___x_656_ = lean_uint64_mix_hash(v___x_655_, v___x_654_);
return v___x_656_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4(void){
_start:
{
uint64_t v___x_657_; uint64_t v___x_658_; uint64_t v___x_659_; 
v___x_657_ = 13ULL;
v___x_658_ = 2ULL;
v___x_659_ = lean_uint64_mix_hash(v___x_658_, v___x_657_);
return v___x_659_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5(void){
_start:
{
uint64_t v___x_660_; uint64_t v___x_661_; uint64_t v___x_662_; 
v___x_660_ = 11ULL;
v___x_661_ = 2ULL;
v___x_662_ = lean_uint64_mix_hash(v___x_661_, v___x_660_);
return v___x_662_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6(void){
_start:
{
uint64_t v___x_663_; uint64_t v___x_664_; uint64_t v___x_665_; 
v___x_663_ = 13ULL;
v___x_664_ = 5ULL;
v___x_665_ = lean_uint64_mix_hash(v___x_664_, v___x_663_);
return v___x_665_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7(void){
_start:
{
uint64_t v___x_666_; uint64_t v___x_667_; uint64_t v___x_668_; 
v___x_666_ = 11ULL;
v___x_667_ = 5ULL;
v___x_668_ = lean_uint64_mix_hash(v___x_667_, v___x_666_);
return v___x_668_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8(void){
_start:
{
uint64_t v___x_669_; uint64_t v___x_670_; uint64_t v___x_671_; 
v___x_669_ = 13ULL;
v___x_670_ = 8ULL;
v___x_671_ = lean_uint64_mix_hash(v___x_670_, v___x_669_);
return v___x_671_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9(void){
_start:
{
uint64_t v___x_672_; uint64_t v___x_673_; uint64_t v___x_674_; 
v___x_672_ = 11ULL;
v___x_673_ = 8ULL;
v___x_674_ = lean_uint64_mix_hash(v___x_673_, v___x_672_);
return v___x_674_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(lean_object* v_x_675_){
_start:
{
switch(lean_obj_tag(v_x_675_))
{
case 0:
{
uint8_t v_gen_676_; 
v_gen_676_ = lean_ctor_get_uint8(v_x_675_, 0);
if (v_gen_676_ == 0)
{
uint64_t v___x_677_; 
v___x_677_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0);
return v___x_677_;
}
else
{
uint64_t v___x_678_; 
v___x_678_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1);
return v___x_678_;
}
}
case 1:
{
uint8_t v_gen_679_; 
v_gen_679_ = lean_ctor_get_uint8(v_x_675_, 0);
if (v_gen_679_ == 0)
{
uint64_t v___x_680_; 
v___x_680_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2);
return v___x_680_;
}
else
{
uint64_t v___x_681_; 
v___x_681_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3);
return v___x_681_;
}
}
case 2:
{
uint8_t v_gen_682_; 
v_gen_682_ = lean_ctor_get_uint8(v_x_675_, 0);
if (v_gen_682_ == 0)
{
uint64_t v___x_683_; 
v___x_683_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4);
return v___x_683_;
}
else
{
uint64_t v___x_684_; 
v___x_684_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5);
return v___x_684_;
}
}
case 3:
{
uint64_t v___x_685_; 
v___x_685_ = 3ULL;
return v___x_685_;
}
case 4:
{
uint64_t v___x_686_; 
v___x_686_ = 4ULL;
return v___x_686_;
}
case 5:
{
uint8_t v_gen_687_; 
v_gen_687_ = lean_ctor_get_uint8(v_x_675_, 0);
if (v_gen_687_ == 0)
{
uint64_t v___x_688_; 
v___x_688_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6);
return v___x_688_;
}
else
{
uint64_t v___x_689_; 
v___x_689_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7);
return v___x_689_;
}
}
case 6:
{
uint64_t v___x_690_; 
v___x_690_ = 6ULL;
return v___x_690_;
}
case 7:
{
uint64_t v___x_691_; 
v___x_691_ = 7ULL;
return v___x_691_;
}
case 8:
{
uint8_t v_gen_692_; 
v_gen_692_ = lean_ctor_get_uint8(v_x_675_, 0);
if (v_gen_692_ == 0)
{
uint64_t v___x_693_; 
v___x_693_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8);
return v___x_693_;
}
else
{
uint64_t v___x_694_; 
v___x_694_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9);
return v___x_694_;
}
}
default: 
{
uint64_t v___x_695_; 
v___x_695_ = 9ULL;
return v___x_695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___boxed(lean_object* v_x_696_){
_start:
{
uint64_t v_res_697_; lean_object* v_r_698_; 
v_res_697_ = l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(v_x_696_);
lean_dec(v_x_696_);
v_r_698_ = lean_box_uint64(v_res_697_);
return v_r_698_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_706_ = lean_box(0);
v___x_707_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__2));
v___x_708_ = l_Lean_Expr_const___override(v___x_707_, v___x_706_);
return v___x_708_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_709_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_712_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v___x_710_);
lean_ctor_set(v___x_712_, 2, v___x_709_);
return v___x_712_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default(void){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4);
return v___x_713_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS(void){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default;
return v___x_714_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(lean_object* v_xs_715_, lean_object* v_ys_716_, lean_object* v_x_717_){
_start:
{
lean_object* v_zero_718_; uint8_t v_isZero_719_; 
v_zero_718_ = lean_unsigned_to_nat(0u);
v_isZero_719_ = lean_nat_dec_eq(v_x_717_, v_zero_718_);
if (v_isZero_719_ == 1)
{
lean_dec(v_x_717_);
return v_isZero_719_;
}
else
{
lean_object* v_one_720_; lean_object* v_n_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_one_720_ = lean_unsigned_to_nat(1u);
v_n_721_ = lean_nat_sub(v_x_717_, v_one_720_);
lean_dec(v_x_717_);
v___x_722_ = lean_array_fget_borrowed(v_xs_715_, v_n_721_);
v___x_723_ = lean_array_fget_borrowed(v_ys_716_, v_n_721_);
v___x_724_ = lean_name_eq(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_dec(v_n_721_);
return v___x_724_;
}
else
{
v_x_717_ = v_n_721_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg___boxed(lean_object* v_xs_726_, lean_object* v_ys_727_, lean_object* v_x_728_){
_start:
{
uint8_t v_res_729_; lean_object* v_r_730_; 
v_res_729_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_xs_726_, v_ys_727_, v_x_728_);
lean_dec_ref(v_ys_727_);
lean_dec_ref(v_xs_726_);
v_r_730_ = lean_box(v_res_729_);
return v_r_730_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqCnstrRHS_beq(lean_object* v_x_731_, lean_object* v_x_732_){
_start:
{
lean_object* v_levelNames_733_; lean_object* v_numMVars_734_; lean_object* v_expr_735_; lean_object* v_levelNames_736_; lean_object* v_numMVars_737_; lean_object* v_expr_738_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_levelNames_733_ = lean_ctor_get(v_x_731_, 0);
v_numMVars_734_ = lean_ctor_get(v_x_731_, 1);
v_expr_735_ = lean_ctor_get(v_x_731_, 2);
v_levelNames_736_ = lean_ctor_get(v_x_732_, 0);
v_numMVars_737_ = lean_ctor_get(v_x_732_, 1);
v_expr_738_ = lean_ctor_get(v_x_732_, 2);
v___x_739_ = lean_array_get_size(v_levelNames_733_);
v___x_740_ = lean_array_get_size(v_levelNames_736_);
v___x_741_ = lean_nat_dec_eq(v___x_739_, v___x_740_);
if (v___x_741_ == 0)
{
return v___x_741_;
}
else
{
uint8_t v___x_742_; 
v___x_742_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_levelNames_733_, v_levelNames_736_, v___x_739_);
if (v___x_742_ == 0)
{
return v___x_742_;
}
else
{
uint8_t v___x_743_; 
v___x_743_ = lean_nat_dec_eq(v_numMVars_734_, v_numMVars_737_);
if (v___x_743_ == 0)
{
return v___x_743_;
}
else
{
uint8_t v___x_744_; 
v___x_744_ = lean_expr_eqv(v_expr_735_, v_expr_738_);
return v___x_744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqCnstrRHS_beq___boxed(lean_object* v_x_745_, lean_object* v_x_746_){
_start:
{
uint8_t v_res_747_; lean_object* v_r_748_; 
v_res_747_ = l_Lean_Meta_Grind_instBEqCnstrRHS_beq(v_x_745_, v_x_746_);
lean_dec_ref(v_x_746_);
lean_dec_ref(v_x_745_);
v_r_748_ = lean_box(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(lean_object* v_xs_749_, lean_object* v_ys_750_, lean_object* v_hsz_751_, lean_object* v_x_752_, lean_object* v_x_753_){
_start:
{
uint8_t v___x_754_; 
v___x_754_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_xs_749_, v_ys_750_, v_x_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___boxed(lean_object* v_xs_755_, lean_object* v_ys_756_, lean_object* v_hsz_757_, lean_object* v_x_758_, lean_object* v_x_759_){
_start:
{
uint8_t v_res_760_; lean_object* v_r_761_; 
v_res_760_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(v_xs_755_, v_ys_756_, v_hsz_757_, v_x_758_, v_x_759_);
lean_dec_ref(v_ys_756_);
lean_dec_ref(v_xs_755_);
v_r_761_ = lean_box(v_res_760_);
return v_r_761_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__1(lean_object* v_a_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = lean_nat_to_int(v_a_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
if (lean_obj_tag(v_x_768_) == 0)
{
lean_dec(v_x_766_);
return v_x_767_;
}
else
{
lean_object* v_head_769_; lean_object* v_tail_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_781_; 
v_head_769_ = lean_ctor_get(v_x_768_, 0);
v_tail_770_ = lean_ctor_get(v_x_768_, 1);
v_isSharedCheck_781_ = !lean_is_exclusive(v_x_768_);
if (v_isSharedCheck_781_ == 0)
{
v___x_772_ = v_x_768_;
v_isShared_773_ = v_isSharedCheck_781_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_tail_770_);
lean_inc(v_head_769_);
lean_dec(v_x_768_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_781_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
lean_inc(v_x_766_);
if (v_isShared_773_ == 0)
{
lean_ctor_set_tag(v___x_772_, 5);
lean_ctor_set(v___x_772_, 1, v_x_766_);
lean_ctor_set(v___x_772_, 0, v_x_767_);
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_x_767_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_x_766_);
v___x_775_ = v_reuseFailAlloc_780_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = l_Lean_Name_reprPrec(v_head_769_, v___x_776_);
v___x_778_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_775_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v_x_767_ = v___x_778_;
v_x_768_ = v_tail_770_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2(lean_object* v_x_782_, lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
if (lean_obj_tag(v_x_784_) == 0)
{
lean_dec(v_x_782_);
return v_x_783_;
}
else
{
lean_object* v_head_785_; lean_object* v_tail_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_797_; 
v_head_785_ = lean_ctor_get(v_x_784_, 0);
v_tail_786_ = lean_ctor_get(v_x_784_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v_x_784_);
if (v_isSharedCheck_797_ == 0)
{
v___x_788_ = v_x_784_;
v_isShared_789_ = v_isSharedCheck_797_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_tail_786_);
lean_inc(v_head_785_);
lean_dec(v_x_784_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_797_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
lean_inc(v_x_782_);
if (v_isShared_789_ == 0)
{
lean_ctor_set_tag(v___x_788_, 5);
lean_ctor_set(v___x_788_, 1, v_x_782_);
lean_ctor_set(v___x_788_, 0, v_x_783_);
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_x_783_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_x_782_);
v___x_791_ = v_reuseFailAlloc_796_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = l_Lean_Name_reprPrec(v_head_785_, v___x_792_);
v___x_794_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_791_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2_spec__3(v_x_782_, v___x_794_, v_tail_786_);
return v___x_795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(lean_object* v___y_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = l_Lean_Name_reprPrec(v___y_798_, v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0(lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
if (lean_obj_tag(v_x_801_) == 0)
{
lean_object* v___x_803_; 
lean_dec(v_x_802_);
v___x_803_ = lean_box(0);
return v___x_803_;
}
else
{
lean_object* v_tail_804_; 
v_tail_804_ = lean_ctor_get(v_x_801_, 1);
if (lean_obj_tag(v_tail_804_) == 0)
{
lean_object* v_head_805_; lean_object* v___x_806_; 
lean_dec(v_x_802_);
v_head_805_ = lean_ctor_get(v_x_801_, 0);
lean_inc(v_head_805_);
lean_dec_ref_known(v_x_801_, 2);
v___x_806_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(v_head_805_);
return v___x_806_;
}
else
{
lean_object* v_head_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_inc(v_tail_804_);
v_head_807_ = lean_ctor_get(v_x_801_, 0);
lean_inc(v_head_807_);
lean_dec_ref_known(v_x_801_, 2);
v___x_808_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(v_head_807_);
v___x_809_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2(v_x_802_, v___x_808_, v_tail_804_);
return v___x_809_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0));
v___x_819_ = lean_string_length(v___x_818_);
return v___x_819_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5);
v___x_821_ = lean_nat_to_int(v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0(lean_object* v_xs_829_){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_830_ = lean_array_get_size(v_xs_829_);
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = lean_nat_dec_eq(v___x_830_, v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_833_ = lean_array_to_list(v_xs_829_);
v___x_834_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__3));
v___x_835_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0(v___x_833_, v___x_834_);
v___x_836_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6);
v___x_837_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__7));
v___x_838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v___x_835_);
v___x_839_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__8));
v___x_840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_836_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = l_Std_Format_fill(v___x_841_);
return v___x_842_;
}
else
{
lean_object* v___x_843_; 
lean_dec_ref(v_xs_829_);
v___x_843_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__10));
return v___x_843_;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_unsigned_to_nat(14u);
v___x_858_ = lean_nat_to_int(v___x_857_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_unsigned_to_nat(12u);
v___x_863_ = lean_nat_to_int(v___x_862_);
return v___x_863_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = lean_unsigned_to_nat(8u);
v___x_868_ = lean_nat_to_int(v___x_867_);
return v___x_868_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0));
v___x_871_ = lean_string_length(v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15);
v___x_873_ = lean_nat_to_int(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(lean_object* v_x_878_){
_start:
{
lean_object* v_levelNames_879_; lean_object* v_numMVars_880_; lean_object* v_expr_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_levelNames_879_ = lean_ctor_get(v_x_878_, 0);
lean_inc_ref(v_levelNames_879_);
v_numMVars_880_ = lean_ctor_get(v_x_878_, 1);
lean_inc(v_numMVars_880_);
v_expr_881_ = lean_ctor_get(v_x_878_, 2);
lean_inc_ref(v_expr_881_);
lean_dec_ref(v_x_878_);
v___x_882_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5));
v___x_883_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__6));
v___x_884_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7);
v___x_885_ = l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0(v_levelNames_879_);
v___x_886_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = 0;
v___x_888_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set_uint8(v___x_888_, sizeof(void*)*1, v___x_887_);
v___x_889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_883_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2));
v___x_891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = lean_box(1);
v___x_893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__9));
v___x_895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v___x_882_);
v___x_897_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10);
v___x_898_ = l_Nat_reprFast(v_numMVars_880_);
v___x_899_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
v___x_900_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_897_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set_uint8(v___x_901_, sizeof(void*)*1, v___x_887_);
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_896_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v___x_890_);
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_892_);
v___x_905_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__12));
v___x_906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v___x_882_);
v___x_908_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13);
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = l_Lean_instReprExpr_repr(v_expr_881_, v___x_909_);
v___x_911_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_908_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*1, v___x_887_);
v___x_913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_907_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16);
v___x_915_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__17));
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v___x_913_);
v___x_917_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__18));
v___x_918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_914_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set_uint8(v___x_920_, sizeof(void*)*1, v___x_887_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr(lean_object* v_x_921_, lean_object* v_prec_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_x_921_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___boxed(lean_object* v_x_924_, lean_object* v_prec_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr(v_x_924_, v_prec_925_);
lean_dec(v_prec_925_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(lean_object* v_x_929_){
_start:
{
switch(lean_obj_tag(v_x_929_))
{
case 0:
{
lean_object* v___x_930_; 
v___x_930_ = lean_unsigned_to_nat(0u);
return v___x_930_;
}
case 1:
{
lean_object* v___x_931_; 
v___x_931_ = lean_unsigned_to_nat(1u);
return v___x_931_;
}
case 2:
{
lean_object* v___x_932_; 
v___x_932_ = lean_unsigned_to_nat(2u);
return v___x_932_;
}
case 3:
{
lean_object* v___x_933_; 
v___x_933_ = lean_unsigned_to_nat(3u);
return v___x_933_;
}
case 4:
{
lean_object* v___x_934_; 
v___x_934_ = lean_unsigned_to_nat(4u);
return v___x_934_;
}
case 5:
{
lean_object* v___x_935_; 
v___x_935_ = lean_unsigned_to_nat(5u);
return v___x_935_;
}
case 6:
{
lean_object* v___x_936_; 
v___x_936_ = lean_unsigned_to_nat(6u);
return v___x_936_;
}
case 7:
{
lean_object* v___x_937_; 
v___x_937_ = lean_unsigned_to_nat(7u);
return v___x_937_;
}
case 8:
{
lean_object* v___x_938_; 
v___x_938_ = lean_unsigned_to_nat(8u);
return v___x_938_;
}
case 9:
{
lean_object* v___x_939_; 
v___x_939_ = lean_unsigned_to_nat(9u);
return v___x_939_;
}
default: 
{
lean_object* v___x_940_; 
v___x_940_ = lean_unsigned_to_nat(10u);
return v___x_940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx___boxed(lean_object* v_x_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_941_);
lean_dec_ref(v_x_941_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(lean_object* v_t_943_, lean_object* v_k_944_){
_start:
{
switch(lean_obj_tag(v_t_943_))
{
case 0:
{
lean_object* v_lhs_945_; lean_object* v_rhs_946_; lean_object* v___x_947_; 
v_lhs_945_ = lean_ctor_get(v_t_943_, 0);
lean_inc(v_lhs_945_);
v_rhs_946_ = lean_ctor_get(v_t_943_, 1);
lean_inc_ref(v_rhs_946_);
lean_dec_ref_known(v_t_943_, 2);
v___x_947_ = lean_apply_2(v_k_944_, v_lhs_945_, v_rhs_946_);
return v___x_947_;
}
case 1:
{
lean_object* v_lhs_948_; lean_object* v_rhs_949_; lean_object* v___x_950_; 
v_lhs_948_ = lean_ctor_get(v_t_943_, 0);
lean_inc(v_lhs_948_);
v_rhs_949_ = lean_ctor_get(v_t_943_, 1);
lean_inc_ref(v_rhs_949_);
lean_dec_ref_known(v_t_943_, 2);
v___x_950_ = lean_apply_2(v_k_944_, v_lhs_948_, v_rhs_949_);
return v___x_950_;
}
case 2:
{
lean_object* v_lhs_951_; lean_object* v_n_952_; lean_object* v___x_953_; 
v_lhs_951_ = lean_ctor_get(v_t_943_, 0);
lean_inc(v_lhs_951_);
v_n_952_ = lean_ctor_get(v_t_943_, 1);
lean_inc(v_n_952_);
lean_dec_ref_known(v_t_943_, 2);
v___x_953_ = lean_apply_2(v_k_944_, v_lhs_951_, v_n_952_);
return v___x_953_;
}
case 3:
{
lean_object* v_lhs_954_; lean_object* v_n_955_; lean_object* v___x_956_; 
v_lhs_954_ = lean_ctor_get(v_t_943_, 0);
lean_inc(v_lhs_954_);
v_n_955_ = lean_ctor_get(v_t_943_, 1);
lean_inc(v_n_955_);
lean_dec_ref_known(v_t_943_, 2);
v___x_956_ = lean_apply_2(v_k_944_, v_lhs_954_, v_n_955_);
return v___x_956_;
}
case 6:
{
lean_object* v_bvarIdx_957_; uint8_t v_strict_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_bvarIdx_957_ = lean_ctor_get(v_t_943_, 0);
lean_inc(v_bvarIdx_957_);
v_strict_958_ = lean_ctor_get_uint8(v_t_943_, sizeof(void*)*1);
lean_dec_ref_known(v_t_943_, 1);
v___x_959_ = lean_box(v_strict_958_);
v___x_960_ = lean_apply_2(v_k_944_, v_bvarIdx_957_, v___x_959_);
return v___x_960_;
}
case 8:
{
lean_object* v_e_961_; lean_object* v___x_962_; 
v_e_961_ = lean_ctor_get(v_t_943_, 0);
lean_inc_ref(v_e_961_);
lean_dec_ref_known(v_t_943_, 1);
v___x_962_ = lean_apply_1(v_k_944_, v_e_961_);
return v___x_962_;
}
case 9:
{
lean_object* v_e_963_; lean_object* v___x_964_; 
v_e_963_ = lean_ctor_get(v_t_943_, 0);
lean_inc_ref(v_e_963_);
lean_dec_ref_known(v_t_943_, 1);
v___x_964_ = lean_apply_1(v_k_944_, v_e_963_);
return v___x_964_;
}
case 10:
{
lean_object* v_bvarIdx_965_; uint8_t v_strict_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_bvarIdx_965_ = lean_ctor_get(v_t_943_, 0);
lean_inc(v_bvarIdx_965_);
v_strict_966_ = lean_ctor_get_uint8(v_t_943_, sizeof(void*)*1);
lean_dec_ref_known(v_t_943_, 1);
v___x_967_ = lean_box(v_strict_966_);
v___x_968_ = lean_apply_2(v_k_944_, v_bvarIdx_965_, v___x_967_);
return v___x_968_;
}
default: 
{
lean_object* v_n_969_; lean_object* v___x_970_; 
v_n_969_ = lean_ctor_get(v_t_943_, 0);
lean_inc(v_n_969_);
lean_dec_ref(v_t_943_);
v___x_970_ = lean_apply_1(v_k_944_, v_n_969_);
return v___x_970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim(lean_object* v_motive_971_, lean_object* v_ctorIdx_972_, lean_object* v_t_973_, lean_object* v_h_974_, lean_object* v_k_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_973_, v_k_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___boxed(lean_object* v_motive_977_, lean_object* v_ctorIdx_978_, lean_object* v_t_979_, lean_object* v_h_980_, lean_object* v_k_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim(v_motive_977_, v_ctorIdx_978_, v_t_979_, v_h_980_, v_k_981_);
lean_dec(v_ctorIdx_978_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim___redArg(lean_object* v_t_983_, lean_object* v_notDefEq_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_983_, v_notDefEq_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim(lean_object* v_motive_986_, lean_object* v_t_987_, lean_object* v_h_988_, lean_object* v_notDefEq_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_987_, v_notDefEq_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim___redArg(lean_object* v_t_991_, lean_object* v_defEq_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_991_, v_defEq_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim(lean_object* v_motive_994_, lean_object* v_t_995_, lean_object* v_h_996_, lean_object* v_defEq_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_995_, v_defEq_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim___redArg(lean_object* v_t_999_, lean_object* v_sizeLt_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_999_, v_sizeLt_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim(lean_object* v_motive_1002_, lean_object* v_t_1003_, lean_object* v_h_1004_, lean_object* v_sizeLt_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1003_, v_sizeLt_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim___redArg(lean_object* v_t_1007_, lean_object* v_depthLt_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1007_, v_depthLt_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim(lean_object* v_motive_1010_, lean_object* v_t_1011_, lean_object* v_h_1012_, lean_object* v_depthLt_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1011_, v_depthLt_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim___redArg(lean_object* v_t_1015_, lean_object* v_genLt_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1015_, v_genLt_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim(lean_object* v_motive_1018_, lean_object* v_t_1019_, lean_object* v_h_1020_, lean_object* v_genLt_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1019_, v_genLt_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim___redArg(lean_object* v_t_1023_, lean_object* v_isGround_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1023_, v_isGround_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim(lean_object* v_motive_1026_, lean_object* v_t_1027_, lean_object* v_h_1028_, lean_object* v_isGround_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1027_, v_isGround_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim___redArg(lean_object* v_t_1031_, lean_object* v_isValue_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1031_, v_isValue_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim(lean_object* v_motive_1034_, lean_object* v_t_1035_, lean_object* v_h_1036_, lean_object* v_isValue_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1035_, v_isValue_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim___redArg(lean_object* v_t_1039_, lean_object* v_maxInsts_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1039_, v_maxInsts_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim(lean_object* v_motive_1042_, lean_object* v_t_1043_, lean_object* v_h_1044_, lean_object* v_maxInsts_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1043_, v_maxInsts_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim___redArg(lean_object* v_t_1047_, lean_object* v_guard_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1047_, v_guard_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim(lean_object* v_motive_1050_, lean_object* v_t_1051_, lean_object* v_h_1052_, lean_object* v_guard_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1051_, v_guard_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim___redArg(lean_object* v_t_1055_, lean_object* v_check_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1055_, v_check_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim(lean_object* v_motive_1058_, lean_object* v_t_1059_, lean_object* v_h_1060_, lean_object* v_check_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1059_, v_check_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim___redArg(lean_object* v_t_1063_, lean_object* v_notValue_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1063_, v_notValue_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim(lean_object* v_motive_1066_, lean_object* v_t_1067_, lean_object* v_h_1068_, lean_object* v_notValue_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1067_, v_notValue_1069_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default;
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v___x_1071_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default(void){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0, &l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint(void){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default;
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr(lean_object* v_x_1142_, lean_object* v_prec_1143_){
_start:
{
switch(lean_obj_tag(v_x_1142_))
{
case 0:
{
lean_object* v_lhs_1144_; lean_object* v_rhs_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1169_; 
v_lhs_1144_ = lean_ctor_get(v_x_1142_, 0);
v_rhs_1145_ = lean_ctor_get(v_x_1142_, 1);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_x_1142_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1147_ = v_x_1142_;
v_isShared_1148_ = v_isSharedCheck_1169_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_rhs_1145_);
lean_inc(v_lhs_1144_);
lean_dec(v_x_1142_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1169_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___y_1150_; lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = lean_unsigned_to_nat(1024u);
v___x_1166_ = lean_nat_dec_le(v___x_1165_, v_prec_1143_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1150_ = v___x_1167_;
goto v___jp_1149_;
}
else
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1150_ = v___x_1168_;
goto v___jp_1149_;
}
v___jp_1149_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1151_ = lean_box(1);
v___x_1152_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__2));
v___x_1153_ = l_Nat_reprFast(v_lhs_1144_);
v___x_1154_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set_tag(v___x_1147_, 5);
lean_ctor_set(v___x_1147_, 1, v___x_1154_);
lean_ctor_set(v___x_1147_, 0, v___x_1152_);
v___x_1156_ = v___x_1147_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v___x_1151_);
v___x_1158_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_rhs_1145_);
v___x_1159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
lean_inc(v___y_1150_);
v___x_1160_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___y_1150_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = 0;
v___x_1162_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*1, v___x_1161_);
v___x_1163_ = l_Repr_addAppParen(v___x_1162_, v_prec_1143_);
return v___x_1163_;
}
}
}
}
case 1:
{
lean_object* v_lhs_1170_; lean_object* v_rhs_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1195_; 
v_lhs_1170_ = lean_ctor_get(v_x_1142_, 0);
v_rhs_1171_ = lean_ctor_get(v_x_1142_, 1);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_x_1142_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1173_ = v_x_1142_;
v_isShared_1174_ = v_isSharedCheck_1195_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_rhs_1171_);
lean_inc(v_lhs_1170_);
lean_dec(v_x_1142_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1195_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___y_1176_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = lean_unsigned_to_nat(1024u);
v___x_1192_ = lean_nat_dec_le(v___x_1191_, v_prec_1143_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1176_ = v___x_1193_;
goto v___jp_1175_;
}
else
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1176_ = v___x_1194_;
goto v___jp_1175_;
}
v___jp_1175_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1177_ = lean_box(1);
v___x_1178_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__5));
v___x_1179_ = l_Nat_reprFast(v_lhs_1170_);
v___x_1180_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set_tag(v___x_1173_, 5);
lean_ctor_set(v___x_1173_, 1, v___x_1180_);
lean_ctor_set(v___x_1173_, 0, v___x_1178_);
v___x_1182_ = v___x_1173_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
lean_ctor_set(v___x_1183_, 1, v___x_1177_);
v___x_1184_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_rhs_1171_);
v___x_1185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
lean_inc(v___y_1176_);
v___x_1186_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___y_1176_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = 0;
v___x_1188_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set_uint8(v___x_1188_, sizeof(void*)*1, v___x_1187_);
v___x_1189_ = l_Repr_addAppParen(v___x_1188_, v_prec_1143_);
return v___x_1189_;
}
}
}
}
case 2:
{
lean_object* v_lhs_1196_; lean_object* v_n_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1222_; 
v_lhs_1196_ = lean_ctor_get(v_x_1142_, 0);
v_n_1197_ = lean_ctor_get(v_x_1142_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_x_1142_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1199_ = v_x_1142_;
v_isShared_1200_ = v_isSharedCheck_1222_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_n_1197_);
lean_inc(v_lhs_1196_);
lean_dec(v_x_1142_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1222_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___y_1202_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = lean_unsigned_to_nat(1024u);
v___x_1219_ = lean_nat_dec_le(v___x_1218_, v_prec_1143_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1202_ = v___x_1220_;
goto v___jp_1201_;
}
else
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1202_ = v___x_1221_;
goto v___jp_1201_;
}
v___jp_1201_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1203_ = lean_box(1);
v___x_1204_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__8));
v___x_1205_ = l_Nat_reprFast(v_lhs_1196_);
v___x_1206_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set_tag(v___x_1199_, 5);
lean_ctor_set(v___x_1199_, 1, v___x_1206_);
lean_ctor_set(v___x_1199_, 0, v___x_1204_);
v___x_1208_ = v___x_1199_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1203_);
v___x_1210_ = l_Nat_reprFast(v_n_1197_);
v___x_1211_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
v___x_1212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1209_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
lean_inc(v___y_1202_);
v___x_1213_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___y_1202_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = 0;
v___x_1215_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1215_, 0, v___x_1213_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*1, v___x_1214_);
v___x_1216_ = l_Repr_addAppParen(v___x_1215_, v_prec_1143_);
return v___x_1216_;
}
}
}
}
case 3:
{
lean_object* v_lhs_1223_; lean_object* v_n_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1249_; 
v_lhs_1223_ = lean_ctor_get(v_x_1142_, 0);
v_n_1224_ = lean_ctor_get(v_x_1142_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_x_1142_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1226_ = v_x_1142_;
v_isShared_1227_ = v_isSharedCheck_1249_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_n_1224_);
lean_inc(v_lhs_1223_);
lean_dec(v_x_1142_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1249_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___y_1229_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = lean_unsigned_to_nat(1024u);
v___x_1246_ = lean_nat_dec_le(v___x_1245_, v_prec_1143_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; 
v___x_1247_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1229_ = v___x_1247_;
goto v___jp_1228_;
}
else
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1229_ = v___x_1248_;
goto v___jp_1228_;
}
v___jp_1228_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1230_ = lean_box(1);
v___x_1231_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__11));
v___x_1232_ = l_Nat_reprFast(v_lhs_1223_);
v___x_1233_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set_tag(v___x_1226_, 5);
lean_ctor_set(v___x_1226_, 1, v___x_1233_);
lean_ctor_set(v___x_1226_, 0, v___x_1231_);
v___x_1235_ = v___x_1226_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set(v___x_1236_, 1, v___x_1230_);
v___x_1237_ = l_Nat_reprFast(v_n_1224_);
v___x_1238_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
v___x_1239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1236_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
lean_inc(v___y_1229_);
v___x_1240_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___y_1229_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = 0;
v___x_1242_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1242_, 0, v___x_1240_);
lean_ctor_set_uint8(v___x_1242_, sizeof(void*)*1, v___x_1241_);
v___x_1243_ = l_Repr_addAppParen(v___x_1242_, v_prec_1143_);
return v___x_1243_;
}
}
}
}
case 4:
{
lean_object* v_n_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1270_; 
v_n_1250_ = lean_ctor_get(v_x_1142_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_x_1142_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1252_ = v_x_1142_;
v_isShared_1253_ = v_isSharedCheck_1270_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_n_1250_);
lean_dec(v_x_1142_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1270_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___y_1255_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1266_ = lean_unsigned_to_nat(1024u);
v___x_1267_ = lean_nat_dec_le(v___x_1266_, v_prec_1143_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1255_ = v___x_1268_;
goto v___jp_1254_;
}
else
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1255_ = v___x_1269_;
goto v___jp_1254_;
}
v___jp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1256_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__14));
v___x_1257_ = l_Nat_reprFast(v_n_1250_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set_tag(v___x_1252_, 3);
lean_ctor_set(v___x_1252_, 0, v___x_1257_);
v___x_1259_ = v___x_1252_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1256_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
lean_inc(v___y_1255_);
v___x_1261_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___y_1255_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = 0;
v___x_1263_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1263_, 0, v___x_1261_);
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*1, v___x_1262_);
v___x_1264_ = l_Repr_addAppParen(v___x_1263_, v_prec_1143_);
return v___x_1264_;
}
}
}
}
case 5:
{
lean_object* v_bvarIdx_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1291_; 
v_bvarIdx_1271_ = lean_ctor_get(v_x_1142_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_x_1142_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1273_ = v_x_1142_;
v_isShared_1274_ = v_isSharedCheck_1291_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_bvarIdx_1271_);
lean_dec(v_x_1142_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1291_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___y_1276_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = lean_unsigned_to_nat(1024u);
v___x_1288_ = lean_nat_dec_le(v___x_1287_, v_prec_1143_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1276_ = v___x_1289_;
goto v___jp_1275_;
}
else
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1276_ = v___x_1290_;
goto v___jp_1275_;
}
v___jp_1275_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1277_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__17));
v___x_1278_ = l_Nat_reprFast(v_bvarIdx_1271_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set_tag(v___x_1273_, 3);
lean_ctor_set(v___x_1273_, 0, v___x_1278_);
v___x_1280_ = v___x_1273_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1277_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
lean_inc(v___y_1276_);
v___x_1282_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___y_1276_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = 0;
v___x_1284_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set_uint8(v___x_1284_, sizeof(void*)*1, v___x_1283_);
v___x_1285_ = l_Repr_addAppParen(v___x_1284_, v_prec_1143_);
return v___x_1285_;
}
}
}
}
case 6:
{
lean_object* v_bvarIdx_1292_; uint8_t v_strict_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1317_; 
v_bvarIdx_1292_ = lean_ctor_get(v_x_1142_, 0);
v_strict_1293_ = lean_ctor_get_uint8(v_x_1142_, sizeof(void*)*1);
v_isSharedCheck_1317_ = !lean_is_exclusive(v_x_1142_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1295_ = v_x_1142_;
v_isShared_1296_ = v_isSharedCheck_1317_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_bvarIdx_1292_);
lean_dec(v_x_1142_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1317_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___y_1298_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = lean_unsigned_to_nat(1024u);
v___x_1314_ = lean_nat_dec_le(v___x_1313_, v_prec_1143_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1298_ = v___x_1315_;
goto v___jp_1297_;
}
else
{
lean_object* v___x_1316_; 
v___x_1316_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1298_ = v___x_1316_;
goto v___jp_1297_;
}
v___jp_1297_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; lean_object* v___x_1310_; 
v___x_1299_ = lean_box(1);
v___x_1300_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__20));
v___x_1301_ = l_Nat_reprFast(v_bvarIdx_1292_);
v___x_1302_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
v___x_1303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1300_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
v___x_1304_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v___x_1299_);
v___x_1305_ = l_Bool_repr___redArg(v_strict_1293_);
v___x_1306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1304_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
lean_inc(v___y_1298_);
v___x_1307_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___y_1298_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___x_1308_ = 0;
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1307_);
v___x_1310_ = v___x_1295_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1307_);
v___x_1310_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1311_; 
lean_ctor_set_uint8(v___x_1310_, sizeof(void*)*1, v___x_1308_);
v___x_1311_ = l_Repr_addAppParen(v___x_1310_, v_prec_1143_);
return v___x_1311_;
}
}
}
}
case 7:
{
lean_object* v_n_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1338_; 
v_n_1318_ = lean_ctor_get(v_x_1142_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_x_1142_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1320_ = v_x_1142_;
v_isShared_1321_ = v_isSharedCheck_1338_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_n_1318_);
lean_dec(v_x_1142_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1338_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___y_1323_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = lean_unsigned_to_nat(1024u);
v___x_1335_ = lean_nat_dec_le(v___x_1334_, v_prec_1143_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1323_ = v___x_1336_;
goto v___jp_1322_;
}
else
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1323_ = v___x_1337_;
goto v___jp_1322_;
}
v___jp_1322_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
v___x_1324_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__23));
v___x_1325_ = l_Nat_reprFast(v_n_1318_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set_tag(v___x_1320_, 3);
lean_ctor_set(v___x_1320_, 0, v___x_1325_);
v___x_1327_ = v___x_1320_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1324_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
lean_inc(v___y_1323_);
v___x_1329_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___y_1323_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = 0;
v___x_1331_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1331_, 0, v___x_1329_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*1, v___x_1330_);
v___x_1332_ = l_Repr_addAppParen(v___x_1331_, v_prec_1143_);
return v___x_1332_;
}
}
}
}
case 8:
{
lean_object* v_e_1339_; lean_object* v___y_1341_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v_e_1339_ = lean_ctor_get(v_x_1142_, 0);
lean_inc_ref(v_e_1339_);
lean_dec_ref_known(v_x_1142_, 1);
v___x_1350_ = lean_unsigned_to_nat(1024u);
v___x_1351_ = lean_nat_dec_le(v___x_1350_, v_prec_1143_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1341_ = v___x_1352_;
goto v___jp_1340_;
}
else
{
lean_object* v___x_1353_; 
v___x_1353_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1341_ = v___x_1353_;
goto v___jp_1340_;
}
v___jp_1340_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1342_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__26));
v___x_1343_ = lean_unsigned_to_nat(1024u);
v___x_1344_ = l_Lean_instReprExpr_repr(v_e_1339_, v___x_1343_);
v___x_1345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1342_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
lean_inc(v___y_1341_);
v___x_1346_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___y_1341_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = 0;
v___x_1348_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set_uint8(v___x_1348_, sizeof(void*)*1, v___x_1347_);
v___x_1349_ = l_Repr_addAppParen(v___x_1348_, v_prec_1143_);
return v___x_1349_;
}
}
case 9:
{
lean_object* v_e_1354_; lean_object* v___y_1356_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v_e_1354_ = lean_ctor_get(v_x_1142_, 0);
lean_inc_ref(v_e_1354_);
lean_dec_ref_known(v_x_1142_, 1);
v___x_1365_ = lean_unsigned_to_nat(1024u);
v___x_1366_ = lean_nat_dec_le(v___x_1365_, v_prec_1143_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1356_ = v___x_1367_;
goto v___jp_1355_;
}
else
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1356_ = v___x_1368_;
goto v___jp_1355_;
}
v___jp_1355_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1357_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__29));
v___x_1358_ = lean_unsigned_to_nat(1024u);
v___x_1359_ = l_Lean_instReprExpr_repr(v_e_1354_, v___x_1358_);
v___x_1360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1357_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
lean_inc(v___y_1356_);
v___x_1361_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___y_1356_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v___x_1362_ = 0;
v___x_1363_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set_uint8(v___x_1363_, sizeof(void*)*1, v___x_1362_);
v___x_1364_ = l_Repr_addAppParen(v___x_1363_, v_prec_1143_);
return v___x_1364_;
}
}
default: 
{
lean_object* v_bvarIdx_1369_; uint8_t v_strict_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1394_; 
v_bvarIdx_1369_ = lean_ctor_get(v_x_1142_, 0);
v_strict_1370_ = lean_ctor_get_uint8(v_x_1142_, sizeof(void*)*1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_x_1142_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1372_ = v_x_1142_;
v_isShared_1373_ = v_isSharedCheck_1394_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_bvarIdx_1369_);
lean_dec(v_x_1142_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1394_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___y_1375_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1390_ = lean_unsigned_to_nat(1024u);
v___x_1391_ = lean_nat_dec_le(v___x_1390_, v_prec_1143_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1375_ = v___x_1392_;
goto v___jp_1374_;
}
else
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1375_ = v___x_1393_;
goto v___jp_1374_;
}
v___jp_1374_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; lean_object* v___x_1387_; 
v___x_1376_ = lean_box(1);
v___x_1377_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__32));
v___x_1378_ = l_Nat_reprFast(v_bvarIdx_1369_);
v___x_1379_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
v___x_1380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1377_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
v___x_1381_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
lean_ctor_set(v___x_1381_, 1, v___x_1376_);
v___x_1382_ = l_Bool_repr___redArg(v_strict_1370_);
v___x_1383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1381_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
lean_inc(v___y_1375_);
v___x_1384_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___y_1375_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
v___x_1385_ = 0;
if (v_isShared_1373_ == 0)
{
lean_ctor_set_tag(v___x_1372_, 6);
lean_ctor_set(v___x_1372_, 0, v___x_1384_);
v___x_1387_ = v___x_1372_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1384_);
v___x_1387_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; 
lean_ctor_set_uint8(v___x_1387_, sizeof(void*)*1, v___x_1385_);
v___x_1388_ = l_Repr_addAppParen(v___x_1387_, v_prec_1143_);
return v___x_1388_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___boxed(lean_object* v_x_1395_, lean_object* v_prec_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr(v_x_1395_, v_prec_1396_);
lean_dec(v_prec_1396_);
return v_res_1397_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
lean_object* v_lhs_1403_; lean_object* v_rhs_1404_; lean_object* v_lhs_x27_1405_; lean_object* v_rhs_x27_1406_; lean_object* v_lhs_1410_; lean_object* v_n_1411_; lean_object* v_lhs_x27_1412_; lean_object* v_n_x27_1413_; lean_object* v_bvarIdx_1417_; uint8_t v_strict_1418_; lean_object* v_bvarIdx_x27_1419_; uint8_t v_strict_x27_1420_; lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1422_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_1400_);
v___x_1423_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_1401_);
v___x_1424_ = lean_nat_dec_eq(v___x_1422_, v___x_1423_);
lean_dec(v___x_1423_);
lean_dec(v___x_1422_);
if (v___x_1424_ == 0)
{
return v___x_1424_;
}
else
{
switch(lean_obj_tag(v_x_1400_))
{
case 0:
{
lean_object* v_lhs_1425_; lean_object* v_rhs_1426_; lean_object* v_lhs_1427_; lean_object* v_rhs_1428_; 
v_lhs_1425_ = lean_ctor_get(v_x_1400_, 0);
v_rhs_1426_ = lean_ctor_get(v_x_1400_, 1);
v_lhs_1427_ = lean_ctor_get(v_x_1401_, 0);
v_rhs_1428_ = lean_ctor_get(v_x_1401_, 1);
v_lhs_1403_ = v_lhs_1425_;
v_rhs_1404_ = v_rhs_1426_;
v_lhs_x27_1405_ = v_lhs_1427_;
v_rhs_x27_1406_ = v_rhs_1428_;
goto v___jp_1402_;
}
case 1:
{
lean_object* v_lhs_1429_; lean_object* v_rhs_1430_; lean_object* v_lhs_1431_; lean_object* v_rhs_1432_; 
v_lhs_1429_ = lean_ctor_get(v_x_1400_, 0);
v_rhs_1430_ = lean_ctor_get(v_x_1400_, 1);
v_lhs_1431_ = lean_ctor_get(v_x_1401_, 0);
v_rhs_1432_ = lean_ctor_get(v_x_1401_, 1);
v_lhs_1403_ = v_lhs_1429_;
v_rhs_1404_ = v_rhs_1430_;
v_lhs_x27_1405_ = v_lhs_1431_;
v_rhs_x27_1406_ = v_rhs_1432_;
goto v___jp_1402_;
}
case 2:
{
lean_object* v_lhs_1433_; lean_object* v_n_1434_; lean_object* v_lhs_1435_; lean_object* v_n_1436_; 
v_lhs_1433_ = lean_ctor_get(v_x_1400_, 0);
v_n_1434_ = lean_ctor_get(v_x_1400_, 1);
v_lhs_1435_ = lean_ctor_get(v_x_1401_, 0);
v_n_1436_ = lean_ctor_get(v_x_1401_, 1);
v_lhs_1410_ = v_lhs_1433_;
v_n_1411_ = v_n_1434_;
v_lhs_x27_1412_ = v_lhs_1435_;
v_n_x27_1413_ = v_n_1436_;
goto v___jp_1409_;
}
case 3:
{
lean_object* v_lhs_1437_; lean_object* v_n_1438_; lean_object* v_lhs_1439_; lean_object* v_n_1440_; 
v_lhs_1437_ = lean_ctor_get(v_x_1400_, 0);
v_n_1438_ = lean_ctor_get(v_x_1400_, 1);
v_lhs_1439_ = lean_ctor_get(v_x_1401_, 0);
v_n_1440_ = lean_ctor_get(v_x_1401_, 1);
v_lhs_1410_ = v_lhs_1437_;
v_n_1411_ = v_n_1438_;
v_lhs_x27_1412_ = v_lhs_1439_;
v_n_x27_1413_ = v_n_1440_;
goto v___jp_1409_;
}
case 6:
{
lean_object* v_bvarIdx_1441_; uint8_t v_strict_1442_; lean_object* v_bvarIdx_1443_; uint8_t v_strict_1444_; 
v_bvarIdx_1441_ = lean_ctor_get(v_x_1400_, 0);
v_strict_1442_ = lean_ctor_get_uint8(v_x_1400_, sizeof(void*)*1);
v_bvarIdx_1443_ = lean_ctor_get(v_x_1401_, 0);
v_strict_1444_ = lean_ctor_get_uint8(v_x_1401_, sizeof(void*)*1);
v_bvarIdx_1417_ = v_bvarIdx_1441_;
v_strict_1418_ = v_strict_1442_;
v_bvarIdx_x27_1419_ = v_bvarIdx_1443_;
v_strict_x27_1420_ = v_strict_1444_;
goto v___jp_1416_;
}
case 8:
{
lean_object* v_e_1445_; lean_object* v_e_1446_; uint8_t v___x_1447_; 
v_e_1445_ = lean_ctor_get(v_x_1400_, 0);
v_e_1446_ = lean_ctor_get(v_x_1401_, 0);
v___x_1447_ = lean_expr_eqv(v_e_1445_, v_e_1446_);
return v___x_1447_;
}
case 9:
{
lean_object* v_e_1448_; lean_object* v_e_1449_; uint8_t v___x_1450_; 
v_e_1448_ = lean_ctor_get(v_x_1400_, 0);
v_e_1449_ = lean_ctor_get(v_x_1401_, 0);
v___x_1450_ = lean_expr_eqv(v_e_1448_, v_e_1449_);
return v___x_1450_;
}
case 10:
{
lean_object* v_bvarIdx_1451_; uint8_t v_strict_1452_; lean_object* v_bvarIdx_1453_; uint8_t v_strict_1454_; 
v_bvarIdx_1451_ = lean_ctor_get(v_x_1400_, 0);
v_strict_1452_ = lean_ctor_get_uint8(v_x_1400_, sizeof(void*)*1);
v_bvarIdx_1453_ = lean_ctor_get(v_x_1401_, 0);
v_strict_1454_ = lean_ctor_get_uint8(v_x_1401_, sizeof(void*)*1);
v_bvarIdx_1417_ = v_bvarIdx_1451_;
v_strict_1418_ = v_strict_1452_;
v_bvarIdx_x27_1419_ = v_bvarIdx_1453_;
v_strict_x27_1420_ = v_strict_1454_;
goto v___jp_1416_;
}
default: 
{
lean_object* v_n_1455_; lean_object* v_n_1456_; uint8_t v___x_1457_; 
v_n_1455_ = lean_ctor_get(v_x_1400_, 0);
v_n_1456_ = lean_ctor_get(v_x_1401_, 0);
v___x_1457_ = lean_nat_dec_eq(v_n_1455_, v_n_1456_);
return v___x_1457_;
}
}
}
v___jp_1402_:
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_nat_dec_eq(v_lhs_1403_, v_lhs_x27_1405_);
if (v___x_1407_ == 0)
{
return v___x_1407_;
}
else
{
uint8_t v___x_1408_; 
v___x_1408_ = l_Lean_Meta_Grind_instBEqCnstrRHS_beq(v_rhs_1404_, v_rhs_x27_1406_);
return v___x_1408_;
}
}
v___jp_1409_:
{
uint8_t v___x_1414_; 
v___x_1414_ = lean_nat_dec_eq(v_lhs_1410_, v_lhs_x27_1412_);
if (v___x_1414_ == 0)
{
return v___x_1414_;
}
else
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_nat_dec_eq(v_n_1411_, v_n_x27_1413_);
return v___x_1415_;
}
}
v___jp_1416_:
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_nat_dec_eq(v_bvarIdx_1417_, v_bvarIdx_x27_1419_);
if (v___x_1421_ == 0)
{
return v___x_1421_;
}
else
{
if (v_strict_1418_ == 0)
{
if (v_strict_x27_1420_ == 0)
{
return v___x_1421_;
}
else
{
return v_strict_1418_;
}
}
else
{
return v_strict_x27_1420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq___boxed(lean_object* v_x_1458_, lean_object* v_x_1459_){
_start:
{
uint8_t v_res_1460_; lean_object* v_r_1461_; 
v_res_1460_ = l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(v_x_1458_, v_x_1459_);
lean_dec_ref(v_x_1459_);
lean_dec_ref(v_x_1458_);
v_r_1461_ = lean_box(v_res_1460_);
return v_r_1461_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0(void){
_start:
{
uint8_t v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1464_ = 0;
v___x_1465_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default));
v___x_1466_ = l_Lean_Meta_Grind_instInhabitedOrigin_default;
v___x_1467_ = lean_box(0);
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_1470_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_1471_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
lean_ctor_set(v___x_1471_, 1, v___x_1469_);
lean_ctor_set(v___x_1471_, 2, v___x_1468_);
lean_ctor_set(v___x_1471_, 3, v___x_1467_);
lean_ctor_set(v___x_1471_, 4, v___x_1467_);
lean_ctor_set(v___x_1471_, 5, v___x_1466_);
lean_ctor_set(v___x_1471_, 6, v___x_1465_);
lean_ctor_set(v___x_1471_, 7, v___x_1467_);
lean_ctor_set_uint8(v___x_1471_, sizeof(void*)*8, v___x_1464_);
return v___x_1471_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default(void){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0, &l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0);
return v___x_1472_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem(void){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default;
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0(lean_object* v_thm_1474_){
_start:
{
lean_object* v_symbols_1475_; 
v_symbols_1475_ = lean_ctor_get(v_thm_1474_, 4);
lean_inc(v_symbols_1475_);
return v_symbols_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0___boxed(lean_object* v_thm_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0(v_thm_1476_);
lean_dec_ref(v_thm_1476_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__1(lean_object* v_thm_1478_, lean_object* v_symbols_1479_){
_start:
{
lean_object* v_levelParams_1480_; lean_object* v_proof_1481_; lean_object* v_numParams_1482_; lean_object* v_patterns_1483_; lean_object* v_origin_1484_; lean_object* v_kind_1485_; uint8_t v_minIndexable_1486_; lean_object* v_cnstrs_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v_levelParams_1480_ = lean_ctor_get(v_thm_1478_, 0);
v_proof_1481_ = lean_ctor_get(v_thm_1478_, 1);
v_numParams_1482_ = lean_ctor_get(v_thm_1478_, 2);
v_patterns_1483_ = lean_ctor_get(v_thm_1478_, 3);
v_origin_1484_ = lean_ctor_get(v_thm_1478_, 5);
v_kind_1485_ = lean_ctor_get(v_thm_1478_, 6);
v_minIndexable_1486_ = lean_ctor_get_uint8(v_thm_1478_, sizeof(void*)*8);
v_cnstrs_1487_ = lean_ctor_get(v_thm_1478_, 7);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_thm_1478_);
if (v_isSharedCheck_1494_ == 0)
{
lean_object* v_unused_1495_; 
v_unused_1495_ = lean_ctor_get(v_thm_1478_, 4);
lean_dec(v_unused_1495_);
v___x_1489_ = v_thm_1478_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_cnstrs_1487_);
lean_inc(v_kind_1485_);
lean_inc(v_origin_1484_);
lean_inc(v_patterns_1483_);
lean_inc(v_numParams_1482_);
lean_inc(v_proof_1481_);
lean_inc(v_levelParams_1480_);
lean_dec(v_thm_1478_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 4, v_symbols_1479_);
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_levelParams_1480_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_proof_1481_);
lean_ctor_set(v_reuseFailAlloc_1493_, 2, v_numParams_1482_);
lean_ctor_set(v_reuseFailAlloc_1493_, 3, v_patterns_1483_);
lean_ctor_set(v_reuseFailAlloc_1493_, 4, v_symbols_1479_);
lean_ctor_set(v_reuseFailAlloc_1493_, 5, v_origin_1484_);
lean_ctor_set(v_reuseFailAlloc_1493_, 6, v_kind_1485_);
lean_ctor_set(v_reuseFailAlloc_1493_, 7, v_cnstrs_1487_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, sizeof(void*)*8, v_minIndexable_1486_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2(lean_object* v_thm_1496_){
_start:
{
lean_object* v_origin_1497_; 
v_origin_1497_ = lean_ctor_get(v_thm_1496_, 5);
lean_inc_ref(v_origin_1497_);
return v_origin_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2___boxed(lean_object* v_thm_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2(v_thm_1498_);
lean_dec_ref(v_thm_1498_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3(lean_object* v_thm_1500_){
_start:
{
lean_object* v_proof_1501_; 
v_proof_1501_ = lean_ctor_get(v_thm_1500_, 1);
lean_inc_ref(v_proof_1501_);
return v_proof_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3___boxed(lean_object* v_thm_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3(v_thm_1502_);
lean_dec_ref(v_thm_1502_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4(lean_object* v_thm_1504_){
_start:
{
lean_object* v_levelParams_1505_; 
v_levelParams_1505_ = lean_ctor_get(v_thm_1504_, 0);
lean_inc_ref(v_levelParams_1505_);
return v_levelParams_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4___boxed(lean_object* v_thm_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4(v_thm_1506_);
lean_dec_ref(v_thm_1506_);
return v_res_1507_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1520_ = l_Lean_Meta_Grind_instInhabitedOrigin_default;
v___x_1521_ = lean_box(0);
v___x_1522_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_1523_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_1524_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
lean_ctor_set(v___x_1524_, 1, v___x_1522_);
lean_ctor_set(v___x_1524_, 2, v___x_1521_);
lean_ctor_set(v___x_1524_, 3, v___x_1520_);
return v___x_1524_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default(void){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0, &l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0);
return v___x_1525_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem(void){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default;
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0(lean_object* v_thm_1527_){
_start:
{
lean_object* v_symbols_1528_; 
v_symbols_1528_ = lean_ctor_get(v_thm_1527_, 2);
lean_inc(v_symbols_1528_);
return v_symbols_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0___boxed(lean_object* v_thm_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0(v_thm_1529_);
lean_dec_ref(v_thm_1529_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__1(lean_object* v_thm_1531_, lean_object* v_symbols_1532_){
_start:
{
lean_object* v_levelParams_1533_; lean_object* v_proof_1534_; lean_object* v_origin_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
v_levelParams_1533_ = lean_ctor_get(v_thm_1531_, 0);
v_proof_1534_ = lean_ctor_get(v_thm_1531_, 1);
v_origin_1535_ = lean_ctor_get(v_thm_1531_, 3);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_thm_1531_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; 
v_unused_1543_ = lean_ctor_get(v_thm_1531_, 2);
lean_dec(v_unused_1543_);
v___x_1537_ = v_thm_1531_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_origin_1535_);
lean_inc(v_proof_1534_);
lean_inc(v_levelParams_1533_);
lean_dec(v_thm_1531_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 2, v_symbols_1532_);
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_levelParams_1533_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_proof_1534_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_symbols_1532_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v_origin_1535_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2(lean_object* v_thm_1544_){
_start:
{
lean_object* v_origin_1545_; 
v_origin_1545_ = lean_ctor_get(v_thm_1544_, 3);
lean_inc_ref(v_origin_1545_);
return v_origin_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2___boxed(lean_object* v_thm_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2(v_thm_1546_);
lean_dec_ref(v_thm_1546_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3(lean_object* v_thm_1548_){
_start:
{
lean_object* v_proof_1549_; 
v_proof_1549_ = lean_ctor_get(v_thm_1548_, 1);
lean_inc_ref(v_proof_1549_);
return v_proof_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3___boxed(lean_object* v_thm_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3(v_thm_1550_);
lean_dec_ref(v_thm_1550_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4(lean_object* v_thm_1552_){
_start:
{
lean_object* v_levelParams_1553_; 
v_levelParams_1553_ = lean_ctor_get(v_thm_1552_, 0);
lean_inc_ref(v_levelParams_1553_);
return v_levelParams_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4___boxed(lean_object* v_thm_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4(v_thm_1554_);
lean_dec_ref(v_thm_1554_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorIdx(lean_object* v_x_1568_){
_start:
{
switch(lean_obj_tag(v_x_1568_))
{
case 0:
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_unsigned_to_nat(0u);
return v___x_1569_;
}
case 1:
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_unsigned_to_nat(1u);
return v___x_1570_;
}
case 2:
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_unsigned_to_nat(2u);
return v___x_1571_;
}
case 3:
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_unsigned_to_nat(3u);
return v___x_1572_;
}
default: 
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_unsigned_to_nat(4u);
return v___x_1573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorIdx___boxed(lean_object* v_x_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_Meta_Grind_Entry_ctorIdx(v_x_1574_);
lean_dec_ref(v_x_1574_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim___redArg(lean_object* v_t_1576_, lean_object* v_k_1577_){
_start:
{
switch(lean_obj_tag(v_t_1576_))
{
case 2:
{
lean_object* v_declName_1578_; uint8_t v_eager_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v_declName_1578_ = lean_ctor_get(v_t_1576_, 0);
lean_inc(v_declName_1578_);
v_eager_1579_ = lean_ctor_get_uint8(v_t_1576_, sizeof(void*)*1);
lean_dec_ref_known(v_t_1576_, 1);
v___x_1580_ = lean_box(v_eager_1579_);
v___x_1581_ = lean_apply_2(v_k_1577_, v_declName_1578_, v___x_1580_);
return v___x_1581_;
}
case 3:
{
lean_object* v_thm_1582_; lean_object* v___x_1583_; 
v_thm_1582_ = lean_ctor_get(v_t_1576_, 0);
lean_inc_ref(v_thm_1582_);
lean_dec_ref_known(v_t_1576_, 1);
v___x_1583_ = lean_apply_1(v_k_1577_, v_thm_1582_);
return v___x_1583_;
}
case 4:
{
lean_object* v_thm_1584_; lean_object* v___x_1585_; 
v_thm_1584_ = lean_ctor_get(v_t_1576_, 0);
lean_inc_ref(v_thm_1584_);
lean_dec_ref_known(v_t_1576_, 1);
v___x_1585_ = lean_apply_1(v_k_1577_, v_thm_1584_);
return v___x_1585_;
}
default: 
{
lean_object* v_declName_1586_; lean_object* v___x_1587_; 
v_declName_1586_ = lean_ctor_get(v_t_1576_, 0);
lean_inc(v_declName_1586_);
lean_dec_ref(v_t_1576_);
v___x_1587_ = lean_apply_1(v_k_1577_, v_declName_1586_);
return v___x_1587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim(lean_object* v_motive_1588_, lean_object* v_ctorIdx_1589_, lean_object* v_t_1590_, lean_object* v_h_1591_, lean_object* v_k_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1590_, v_k_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim___boxed(lean_object* v_motive_1594_, lean_object* v_ctorIdx_1595_, lean_object* v_t_1596_, lean_object* v_h_1597_, lean_object* v_k_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_Meta_Grind_Entry_ctorElim(v_motive_1594_, v_ctorIdx_1595_, v_t_1596_, v_h_1597_, v_k_1598_);
lean_dec(v_ctorIdx_1595_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ext_elim___redArg(lean_object* v_t_1600_, lean_object* v_ext_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1600_, v_ext_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ext_elim(lean_object* v_motive_1603_, lean_object* v_t_1604_, lean_object* v_h_1605_, lean_object* v_ext_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1604_, v_ext_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_funCC_elim___redArg(lean_object* v_t_1608_, lean_object* v_funCC_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1608_, v_funCC_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_funCC_elim(lean_object* v_motive_1611_, lean_object* v_t_1612_, lean_object* v_h_1613_, lean_object* v_funCC_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1612_, v_funCC_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_cases_elim___redArg(lean_object* v_t_1616_, lean_object* v_cases_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1616_, v_cases_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_cases_elim(lean_object* v_motive_1619_, lean_object* v_t_1620_, lean_object* v_h_1621_, lean_object* v_cases_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1620_, v_cases_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ematch_elim___redArg(lean_object* v_t_1624_, lean_object* v_ematch_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1624_, v_ematch_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ematch_elim(lean_object* v_motive_1627_, lean_object* v_t_1628_, lean_object* v_h_1629_, lean_object* v_ematch_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1628_, v_ematch_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_inj_elim___redArg(lean_object* v_t_1632_, lean_object* v_inj_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1632_, v_inj_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_inj_elim(lean_object* v_motive_1635_, lean_object* v_t_1636_, lean_object* v_h_1637_, lean_object* v_inj_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1636_, v_inj_1638_);
return v___x_1639_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1644_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0);
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0(lean_object* v_00_u03b2_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__1);
return v___x_1648_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0(lean_box(0));
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1(void){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Meta_Grind_Theorems_mkEmpty(lean_box(0));
return v___x_1650_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1651_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1);
v___x_1652_ = l_Lean_NameSet_empty;
v___x_1653_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0);
v___x_1654_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1, &l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1);
v___x_1655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set(v___x_1655_, 1, v___x_1653_);
lean_ctor_set(v___x_1655_, 2, v___x_1652_);
lean_ctor_set(v___x_1655_, 3, v___x_1651_);
lean_ctor_set(v___x_1655_, 4, v___x_1651_);
return v___x_1655_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default(void){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2);
return v___x_1656_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState(void){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_x_1658_, lean_object* v_x_1659_, lean_object* v_x_1660_, lean_object* v_x_1661_){
_start:
{
lean_object* v_ks_1662_; lean_object* v_vs_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1689_; 
v_ks_1662_ = lean_ctor_get(v_x_1658_, 0);
v_vs_1663_ = lean_ctor_get(v_x_1658_, 1);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_x_1658_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1665_ = v_x_1658_;
v_isShared_1666_ = v_isSharedCheck_1689_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_vs_1663_);
lean_inc(v_ks_1662_);
lean_dec(v_x_1658_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1689_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; uint8_t v___x_1668_; 
v___x_1667_ = lean_array_get_size(v_ks_1662_);
v___x_1668_ = lean_nat_dec_lt(v_x_1659_, v___x_1667_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1672_; 
lean_dec(v_x_1659_);
v___x_1669_ = lean_array_push(v_ks_1662_, v_x_1660_);
v___x_1670_ = lean_array_push(v_vs_1663_, v_x_1661_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 1, v___x_1670_);
lean_ctor_set(v___x_1665_, 0, v___x_1669_);
v___x_1672_ = v___x_1665_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
else
{
lean_object* v_k_x27_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v_k_x27_1674_ = lean_array_fget_borrowed(v_ks_1662_, v_x_1659_);
v___x_1675_ = l_Lean_Meta_Grind_Origin_key(v_x_1660_);
v___x_1676_ = l_Lean_Meta_Grind_Origin_key(v_k_x27_1674_);
v___x_1677_ = lean_name_eq(v___x_1675_, v___x_1676_);
lean_dec(v___x_1676_);
lean_dec(v___x_1675_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1679_; 
if (v_isShared_1666_ == 0)
{
v___x_1679_ = v___x_1665_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_ks_1662_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_vs_1663_);
v___x_1679_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = lean_unsigned_to_nat(1u);
v___x_1681_ = lean_nat_add(v_x_1659_, v___x_1680_);
lean_dec(v_x_1659_);
v_x_1658_ = v___x_1679_;
v_x_1659_ = v___x_1681_;
goto _start;
}
}
else
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1684_ = lean_array_fset(v_ks_1662_, v_x_1659_, v_x_1660_);
v___x_1685_ = lean_array_fset(v_vs_1663_, v_x_1659_, v_x_1661_);
lean_dec(v_x_1659_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 1, v___x_1685_);
lean_ctor_set(v___x_1665_, 0, v___x_1684_);
v___x_1687_ = v___x_1665_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_n_1690_, lean_object* v_k_1691_, lean_object* v_v_1692_){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_unsigned_to_nat(0u);
v___x_1694_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(v_n_1690_, v___x_1693_, v_k_1691_, v_v_1692_);
return v___x_1694_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1696_, size_t v_x_1697_, size_t v_x_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_){
_start:
{
if (lean_obj_tag(v_x_1696_) == 0)
{
lean_object* v_es_1701_; size_t v___x_1702_; size_t v___x_1703_; lean_object* v_j_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; 
v_es_1701_ = lean_ctor_get(v_x_1696_, 0);
v___x_1702_ = ((size_t)31ULL);
v___x_1703_ = lean_usize_land(v_x_1697_, v___x_1702_);
v_j_1704_ = lean_usize_to_nat(v___x_1703_);
v___x_1705_ = lean_array_get_size(v_es_1701_);
v___x_1706_ = lean_nat_dec_lt(v_j_1704_, v___x_1705_);
if (v___x_1706_ == 0)
{
lean_dec(v_j_1704_);
lean_dec(v_x_1700_);
lean_dec_ref(v_x_1699_);
return v_x_1696_;
}
else
{
lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1747_; 
lean_inc_ref(v_es_1701_);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_x_1696_);
if (v_isSharedCheck_1747_ == 0)
{
lean_object* v_unused_1748_; 
v_unused_1748_ = lean_ctor_get(v_x_1696_, 0);
lean_dec(v_unused_1748_);
v___x_1708_ = v_x_1696_;
v_isShared_1709_ = v_isSharedCheck_1747_;
goto v_resetjp_1707_;
}
else
{
lean_dec(v_x_1696_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1747_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v_v_1710_; lean_object* v___x_1711_; lean_object* v_xs_x27_1712_; lean_object* v___y_1714_; 
v_v_1710_ = lean_array_fget(v_es_1701_, v_j_1704_);
v___x_1711_ = lean_box(0);
v_xs_x27_1712_ = lean_array_fset(v_es_1701_, v_j_1704_, v___x_1711_);
switch(lean_obj_tag(v_v_1710_))
{
case 0:
{
lean_object* v_key_1719_; lean_object* v_val_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1732_; 
v_key_1719_ = lean_ctor_get(v_v_1710_, 0);
v_val_1720_ = lean_ctor_get(v_v_1710_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_v_1710_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1722_ = v_v_1710_;
v_isShared_1723_ = v_isSharedCheck_1732_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_val_1720_);
lean_inc(v_key_1719_);
lean_dec(v_v_1710_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1732_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1724_ = l_Lean_Meta_Grind_Origin_key(v_x_1699_);
v___x_1725_ = l_Lean_Meta_Grind_Origin_key(v_key_1719_);
v___x_1726_ = lean_name_eq(v___x_1724_, v___x_1725_);
lean_dec(v___x_1725_);
lean_dec(v___x_1724_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
lean_del_object(v___x_1722_);
v___x_1727_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1719_, v_val_1720_, v_x_1699_, v_x_1700_);
v___x_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
v___y_1714_ = v___x_1728_;
goto v___jp_1713_;
}
else
{
lean_object* v___x_1730_; 
lean_dec(v_val_1720_);
lean_dec(v_key_1719_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 1, v_x_1700_);
lean_ctor_set(v___x_1722_, 0, v_x_1699_);
v___x_1730_ = v___x_1722_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_x_1699_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_x_1700_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
v___y_1714_ = v___x_1730_;
goto v___jp_1713_;
}
}
}
}
case 1:
{
lean_object* v_node_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1745_; 
v_node_1733_ = lean_ctor_get(v_v_1710_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_v_1710_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1735_ = v_v_1710_;
v_isShared_1736_ = v_isSharedCheck_1745_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_node_1733_);
lean_dec(v_v_1710_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1745_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
size_t v___x_1737_; size_t v___x_1738_; size_t v___x_1739_; size_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1743_; 
v___x_1737_ = ((size_t)5ULL);
v___x_1738_ = lean_usize_shift_right(v_x_1697_, v___x_1737_);
v___x_1739_ = ((size_t)1ULL);
v___x_1740_ = lean_usize_add(v_x_1698_, v___x_1739_);
v___x_1741_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_node_1733_, v___x_1738_, v___x_1740_, v_x_1699_, v_x_1700_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1741_);
v___x_1743_ = v___x_1735_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
v___y_1714_ = v___x_1743_;
goto v___jp_1713_;
}
}
}
default: 
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v_x_1699_);
lean_ctor_set(v___x_1746_, 1, v_x_1700_);
v___y_1714_ = v___x_1746_;
goto v___jp_1713_;
}
}
v___jp_1713_:
{
lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1715_ = lean_array_fset(v_xs_x27_1712_, v_j_1704_, v___y_1714_);
lean_dec(v_j_1704_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v___x_1715_);
v___x_1717_ = v___x_1708_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
else
{
lean_object* v_ks_1749_; lean_object* v_vs_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1770_; 
v_ks_1749_ = lean_ctor_get(v_x_1696_, 0);
v_vs_1750_ = lean_ctor_get(v_x_1696_, 1);
v_isSharedCheck_1770_ = !lean_is_exclusive(v_x_1696_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1752_ = v_x_1696_;
v_isShared_1753_ = v_isSharedCheck_1770_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_vs_1750_);
lean_inc(v_ks_1749_);
lean_dec(v_x_1696_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1770_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_ks_1749_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_vs_1750_);
v___x_1755_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v_newNode_1756_; uint8_t v___y_1758_; size_t v___x_1764_; uint8_t v___x_1765_; 
v_newNode_1756_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(v___x_1755_, v_x_1699_, v_x_1700_);
v___x_1764_ = ((size_t)7ULL);
v___x_1765_ = lean_usize_dec_le(v___x_1764_, v_x_1698_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1766_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1756_);
v___x_1767_ = lean_unsigned_to_nat(4u);
v___x_1768_ = lean_nat_dec_lt(v___x_1766_, v___x_1767_);
lean_dec(v___x_1766_);
v___y_1758_ = v___x_1768_;
goto v___jp_1757_;
}
else
{
v___y_1758_ = v___x_1765_;
goto v___jp_1757_;
}
v___jp_1757_:
{
if (v___y_1758_ == 0)
{
lean_object* v_ks_1759_; lean_object* v_vs_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v_ks_1759_ = lean_ctor_get(v_newNode_1756_, 0);
lean_inc_ref(v_ks_1759_);
v_vs_1760_ = lean_ctor_get(v_newNode_1756_, 1);
lean_inc_ref(v_vs_1760_);
lean_dec_ref(v_newNode_1756_);
v___x_1761_ = lean_unsigned_to_nat(0u);
v___x_1762_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___closed__0);
v___x_1763_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_x_1698_, v_ks_1759_, v_vs_1760_, v___x_1761_, v___x_1762_);
lean_dec_ref(v_vs_1760_);
lean_dec_ref(v_ks_1759_);
return v___x_1763_;
}
else
{
return v_newNode_1756_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(size_t v_depth_1771_, lean_object* v_keys_1772_, lean_object* v_vals_1773_, lean_object* v_i_1774_, lean_object* v_entries_1775_){
_start:
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = lean_array_get_size(v_keys_1772_);
v___x_1777_ = lean_nat_dec_lt(v_i_1774_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_dec(v_i_1774_);
return v_entries_1775_;
}
else
{
lean_object* v_k_1778_; lean_object* v_v_1779_; uint64_t v___y_1781_; lean_object* v___x_1792_; 
v_k_1778_ = lean_array_fget_borrowed(v_keys_1772_, v_i_1774_);
v_v_1779_ = lean_array_fget_borrowed(v_vals_1773_, v_i_1774_);
v___x_1792_ = l_Lean_Meta_Grind_Origin_key(v_k_1778_);
if (lean_obj_tag(v___x_1792_) == 0)
{
uint64_t v___x_1793_; 
v___x_1793_ = 1723ULL;
v___y_1781_ = v___x_1793_;
goto v___jp_1780_;
}
else
{
uint64_t v_hash_1794_; 
v_hash_1794_ = lean_ctor_get_uint64(v___x_1792_, sizeof(void*)*2);
lean_dec(v___x_1792_);
v___y_1781_ = v_hash_1794_;
goto v___jp_1780_;
}
v___jp_1780_:
{
size_t v_h_1782_; size_t v___x_1783_; lean_object* v___x_1784_; size_t v___x_1785_; size_t v___x_1786_; size_t v___x_1787_; size_t v_h_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_h_1782_ = lean_uint64_to_usize(v___y_1781_);
v___x_1783_ = ((size_t)5ULL);
v___x_1784_ = lean_unsigned_to_nat(1u);
v___x_1785_ = ((size_t)1ULL);
v___x_1786_ = lean_usize_sub(v_depth_1771_, v___x_1785_);
v___x_1787_ = lean_usize_mul(v___x_1783_, v___x_1786_);
v_h_1788_ = lean_usize_shift_right(v_h_1782_, v___x_1787_);
v___x_1789_ = lean_nat_add(v_i_1774_, v___x_1784_);
lean_dec(v_i_1774_);
lean_inc(v_v_1779_);
lean_inc(v_k_1778_);
v___x_1790_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_entries_1775_, v_h_1788_, v_depth_1771_, v_k_1778_, v_v_1779_);
v_i_1774_ = v___x_1789_;
v_entries_1775_ = v___x_1790_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_depth_1795_, lean_object* v_keys_1796_, lean_object* v_vals_1797_, lean_object* v_i_1798_, lean_object* v_entries_1799_){
_start:
{
size_t v_depth_boxed_1800_; lean_object* v_res_1801_; 
v_depth_boxed_1800_ = lean_unbox_usize(v_depth_1795_);
lean_dec(v_depth_1795_);
v_res_1801_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_depth_boxed_1800_, v_keys_1796_, v_vals_1797_, v_i_1798_, v_entries_1799_);
lean_dec_ref(v_vals_1797_);
lean_dec_ref(v_keys_1796_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_x_1802_, lean_object* v_x_1803_, lean_object* v_x_1804_, lean_object* v_x_1805_, lean_object* v_x_1806_){
_start:
{
size_t v_x_1236__boxed_1807_; size_t v_x_1237__boxed_1808_; lean_object* v_res_1809_; 
v_x_1236__boxed_1807_ = lean_unbox_usize(v_x_1803_);
lean_dec(v_x_1803_);
v_x_1237__boxed_1808_ = lean_unbox_usize(v_x_1804_);
lean_dec(v_x_1804_);
v_res_1809_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_1802_, v_x_1236__boxed_1807_, v_x_1237__boxed_1808_, v_x_1805_, v_x_1806_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(lean_object* v_x_1810_, lean_object* v_x_1811_, lean_object* v_x_1812_){
_start:
{
uint64_t v___y_1814_; lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_Meta_Grind_Origin_key(v_x_1811_);
if (lean_obj_tag(v___x_1818_) == 0)
{
uint64_t v___x_1819_; 
v___x_1819_ = 1723ULL;
v___y_1814_ = v___x_1819_;
goto v___jp_1813_;
}
else
{
uint64_t v_hash_1820_; 
v_hash_1820_ = lean_ctor_get_uint64(v___x_1818_, sizeof(void*)*2);
lean_dec(v___x_1818_);
v___y_1814_ = v_hash_1820_;
goto v___jp_1813_;
}
v___jp_1813_:
{
size_t v___x_1815_; size_t v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = lean_uint64_to_usize(v___y_1814_);
v___x_1816_ = ((size_t)1ULL);
v___x_1817_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_1810_, v___x_1815_, v___x_1816_, v_x_1811_, v_x_1812_);
return v___x_1817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(lean_object* v_keys_1821_, lean_object* v_vals_1822_, lean_object* v_i_1823_, lean_object* v_k_1824_){
_start:
{
lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = lean_array_get_size(v_keys_1821_);
v___x_1826_ = lean_nat_dec_lt(v_i_1823_, v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; 
lean_dec(v_i_1823_);
v___x_1827_ = lean_box(0);
return v___x_1827_;
}
else
{
lean_object* v_k_x27_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v_k_x27_1828_ = lean_array_fget_borrowed(v_keys_1821_, v_i_1823_);
v___x_1829_ = l_Lean_Meta_Grind_Origin_key(v_k_1824_);
v___x_1830_ = l_Lean_Meta_Grind_Origin_key(v_k_x27_1828_);
v___x_1831_ = lean_name_eq(v___x_1829_, v___x_1830_);
lean_dec(v___x_1830_);
lean_dec(v___x_1829_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = lean_unsigned_to_nat(1u);
v___x_1833_ = lean_nat_add(v_i_1823_, v___x_1832_);
lean_dec(v_i_1823_);
v_i_1823_ = v___x_1833_;
goto _start;
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = lean_array_fget_borrowed(v_vals_1822_, v_i_1823_);
lean_dec(v_i_1823_);
lean_inc(v___x_1835_);
v___x_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
return v___x_1836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg___boxed(lean_object* v_keys_1837_, lean_object* v_vals_1838_, lean_object* v_i_1839_, lean_object* v_k_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_keys_1837_, v_vals_1838_, v_i_1839_, v_k_1840_);
lean_dec_ref(v_k_1840_);
lean_dec_ref(v_vals_1838_);
lean_dec_ref(v_keys_1837_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(lean_object* v_x_1842_, size_t v_x_1843_, lean_object* v_x_1844_){
_start:
{
if (lean_obj_tag(v_x_1842_) == 0)
{
lean_object* v_es_1845_; lean_object* v___x_1846_; size_t v___x_1847_; size_t v___x_1848_; lean_object* v_j_1849_; lean_object* v___x_1850_; 
v_es_1845_ = lean_ctor_get(v_x_1842_, 0);
v___x_1846_ = lean_box(2);
v___x_1847_ = ((size_t)31ULL);
v___x_1848_ = lean_usize_land(v_x_1843_, v___x_1847_);
v_j_1849_ = lean_usize_to_nat(v___x_1848_);
v___x_1850_ = lean_array_get_borrowed(v___x_1846_, v_es_1845_, v_j_1849_);
lean_dec(v_j_1849_);
switch(lean_obj_tag(v___x_1850_))
{
case 0:
{
lean_object* v_key_1851_; lean_object* v_val_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v_key_1851_ = lean_ctor_get(v___x_1850_, 0);
v_val_1852_ = lean_ctor_get(v___x_1850_, 1);
v___x_1853_ = l_Lean_Meta_Grind_Origin_key(v_x_1844_);
v___x_1854_ = l_Lean_Meta_Grind_Origin_key(v_key_1851_);
v___x_1855_ = lean_name_eq(v___x_1853_, v___x_1854_);
lean_dec(v___x_1854_);
lean_dec(v___x_1853_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_box(0);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; 
lean_inc(v_val_1852_);
v___x_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1857_, 0, v_val_1852_);
return v___x_1857_;
}
}
case 1:
{
lean_object* v_node_1858_; size_t v___x_1859_; size_t v___x_1860_; 
v_node_1858_ = lean_ctor_get(v___x_1850_, 0);
v___x_1859_ = ((size_t)5ULL);
v___x_1860_ = lean_usize_shift_right(v_x_1843_, v___x_1859_);
v_x_1842_ = v_node_1858_;
v_x_1843_ = v___x_1860_;
goto _start;
}
default: 
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_box(0);
return v___x_1862_;
}
}
}
else
{
lean_object* v_ks_1863_; lean_object* v_vs_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v_ks_1863_ = lean_ctor_get(v_x_1842_, 0);
v_vs_1864_ = lean_ctor_get(v_x_1842_, 1);
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_ks_1863_, v_vs_1864_, v___x_1865_, v_x_1844_);
return v___x_1866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_x_1867_, lean_object* v_x_1868_, lean_object* v_x_1869_){
_start:
{
size_t v_x_1441__boxed_1870_; lean_object* v_res_1871_; 
v_x_1441__boxed_1870_ = lean_unbox_usize(v_x_1868_);
lean_dec(v_x_1868_);
v_res_1871_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_1867_, v_x_1441__boxed_1870_, v_x_1869_);
lean_dec_ref(v_x_1869_);
lean_dec_ref(v_x_1867_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(lean_object* v_x_1872_, lean_object* v_x_1873_){
_start:
{
uint64_t v___y_1875_; lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_Meta_Grind_Origin_key(v_x_1873_);
if (lean_obj_tag(v___x_1878_) == 0)
{
uint64_t v___x_1879_; 
v___x_1879_ = 1723ULL;
v___y_1875_ = v___x_1879_;
goto v___jp_1874_;
}
else
{
uint64_t v_hash_1880_; 
v_hash_1880_ = lean_ctor_get_uint64(v___x_1878_, sizeof(void*)*2);
lean_dec(v___x_1878_);
v___y_1875_ = v_hash_1880_;
goto v___jp_1874_;
}
v___jp_1874_:
{
size_t v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_uint64_to_usize(v___y_1875_);
v___x_1877_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_1872_, v___x_1876_, v_x_1873_);
return v___x_1877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg___boxed(lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_x_1881_, v_x_1882_);
lean_dec_ref(v_x_1882_);
lean_dec_ref(v_x_1881_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(lean_object* v_keys_1884_, lean_object* v_vals_1885_, lean_object* v_i_1886_, lean_object* v_k_1887_){
_start:
{
lean_object* v___x_1888_; uint8_t v___x_1889_; 
v___x_1888_ = lean_array_get_size(v_keys_1884_);
v___x_1889_ = lean_nat_dec_lt(v_i_1886_, v___x_1888_);
if (v___x_1889_ == 0)
{
lean_object* v___x_1890_; 
lean_dec(v_i_1886_);
v___x_1890_ = lean_box(0);
return v___x_1890_;
}
else
{
lean_object* v_k_x27_1891_; uint8_t v___x_1892_; 
v_k_x27_1891_ = lean_array_fget_borrowed(v_keys_1884_, v_i_1886_);
v___x_1892_ = lean_name_eq(v_k_1887_, v_k_x27_1891_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_unsigned_to_nat(1u);
v___x_1894_ = lean_nat_add(v_i_1886_, v___x_1893_);
lean_dec(v_i_1886_);
v_i_1886_ = v___x_1894_;
goto _start;
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_array_fget_borrowed(v_vals_1885_, v_i_1886_);
lean_dec(v_i_1886_);
lean_inc(v___x_1896_);
v___x_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg___boxed(lean_object* v_keys_1898_, lean_object* v_vals_1899_, lean_object* v_i_1900_, lean_object* v_k_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_keys_1898_, v_vals_1899_, v_i_1900_, v_k_1901_);
lean_dec(v_k_1901_);
lean_dec_ref(v_vals_1899_);
lean_dec_ref(v_keys_1898_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(lean_object* v_x_1903_, size_t v_x_1904_, lean_object* v_x_1905_){
_start:
{
if (lean_obj_tag(v_x_1903_) == 0)
{
lean_object* v_es_1906_; lean_object* v___x_1907_; size_t v___x_1908_; size_t v___x_1909_; lean_object* v_j_1910_; lean_object* v___x_1911_; 
v_es_1906_ = lean_ctor_get(v_x_1903_, 0);
v___x_1907_ = lean_box(2);
v___x_1908_ = ((size_t)31ULL);
v___x_1909_ = lean_usize_land(v_x_1904_, v___x_1908_);
v_j_1910_ = lean_usize_to_nat(v___x_1909_);
v___x_1911_ = lean_array_get_borrowed(v___x_1907_, v_es_1906_, v_j_1910_);
lean_dec(v_j_1910_);
switch(lean_obj_tag(v___x_1911_))
{
case 0:
{
lean_object* v_key_1912_; lean_object* v_val_1913_; uint8_t v___x_1914_; 
v_key_1912_ = lean_ctor_get(v___x_1911_, 0);
v_val_1913_ = lean_ctor_get(v___x_1911_, 1);
v___x_1914_ = lean_name_eq(v_x_1905_, v_key_1912_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_box(0);
return v___x_1915_;
}
else
{
lean_object* v___x_1916_; 
lean_inc(v_val_1913_);
v___x_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_val_1913_);
return v___x_1916_;
}
}
case 1:
{
lean_object* v_node_1917_; size_t v___x_1918_; size_t v___x_1919_; 
v_node_1917_ = lean_ctor_get(v___x_1911_, 0);
v___x_1918_ = ((size_t)5ULL);
v___x_1919_ = lean_usize_shift_right(v_x_1904_, v___x_1918_);
v_x_1903_ = v_node_1917_;
v_x_1904_ = v___x_1919_;
goto _start;
}
default: 
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_box(0);
return v___x_1921_;
}
}
}
else
{
lean_object* v_ks_1922_; lean_object* v_vs_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_ks_1922_ = lean_ctor_get(v_x_1903_, 0);
v_vs_1923_ = lean_ctor_get(v_x_1903_, 1);
v___x_1924_ = lean_unsigned_to_nat(0u);
v___x_1925_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_ks_1922_, v_vs_1923_, v___x_1924_, v_x_1905_);
return v___x_1925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg___boxed(lean_object* v_x_1926_, lean_object* v_x_1927_, lean_object* v_x_1928_){
_start:
{
size_t v_x_1528__boxed_1929_; lean_object* v_res_1930_; 
v_x_1528__boxed_1929_ = lean_unbox_usize(v_x_1927_);
lean_dec(v_x_1927_);
v_res_1930_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_1926_, v_x_1528__boxed_1929_, v_x_1928_);
lean_dec(v_x_1928_);
lean_dec_ref(v_x_1926_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(lean_object* v_x_1931_, lean_object* v_x_1932_){
_start:
{
uint64_t v___y_1934_; 
if (lean_obj_tag(v_x_1932_) == 0)
{
uint64_t v___x_1937_; 
v___x_1937_ = 1723ULL;
v___y_1934_ = v___x_1937_;
goto v___jp_1933_;
}
else
{
uint64_t v_hash_1938_; 
v_hash_1938_ = lean_ctor_get_uint64(v_x_1932_, sizeof(void*)*2);
v___y_1934_ = v_hash_1938_;
goto v___jp_1933_;
}
v___jp_1933_:
{
size_t v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_uint64_to_usize(v___y_1934_);
v___x_1936_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_1931_, v___x_1935_, v_x_1932_);
return v___x_1936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg___boxed(lean_object* v_x_1939_, lean_object* v_x_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_x_1939_, v_x_1940_);
lean_dec(v_x_1940_);
lean_dec_ref(v_x_1939_);
return v_res_1941_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_Meta_Grind_instInhabitedTheorems_default(lean_box(0));
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0(lean_object* v_msg_1950_){
_start:
{
lean_object* v___f_1951_; lean_object* v___f_1952_; lean_object* v___f_1953_; lean_object* v___f_1954_; lean_object* v___f_1955_; lean_object* v___f_1956_; lean_object* v___f_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___f_1951_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0));
v___f_1952_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1));
v___f_1953_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2));
v___f_1954_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3));
v___f_1955_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4));
v___f_1956_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5));
v___f_1957_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6));
v___x_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___f_1951_);
lean_ctor_set(v___x_1958_, 1, v___f_1952_);
v___x_1959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
lean_ctor_set(v___x_1959_, 1, v___f_1953_);
lean_ctor_set(v___x_1959_, 2, v___f_1954_);
lean_ctor_set(v___x_1959_, 3, v___f_1955_);
lean_ctor_set(v___x_1959_, 4, v___f_1956_);
v___x_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
lean_ctor_set(v___x_1960_, 1, v___f_1957_);
v___x_1961_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7, &l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once, _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7);
v___x_1962_ = l_instInhabitedOfMonad___redArg(v___x_1960_, v___x_1961_);
v___x_1963_ = lean_panic_fn_borrowed(v___x_1962_, v_msg_1950_);
lean_dec(v___x_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(lean_object* v_xs_1964_, lean_object* v_v_1965_, lean_object* v_i_1966_){
_start:
{
lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = lean_array_get_size(v_xs_1964_);
v___x_1968_ = lean_nat_dec_lt(v_i_1966_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; 
lean_dec(v_i_1966_);
v___x_1969_ = lean_box(0);
return v___x_1969_;
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; 
v___x_1970_ = lean_array_fget_borrowed(v_xs_1964_, v_i_1966_);
v___x_1971_ = l_Lean_Meta_Grind_Origin_key(v___x_1970_);
v___x_1972_ = l_Lean_Meta_Grind_Origin_key(v_v_1965_);
v___x_1973_ = lean_name_eq(v___x_1971_, v___x_1972_);
lean_dec(v___x_1972_);
lean_dec(v___x_1971_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = lean_unsigned_to_nat(1u);
v___x_1975_ = lean_nat_add(v_i_1966_, v___x_1974_);
lean_dec(v_i_1966_);
v_i_1966_ = v___x_1975_;
goto _start;
}
else
{
lean_object* v___x_1977_; 
v___x_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1977_, 0, v_i_1966_);
return v___x_1977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13___boxed(lean_object* v_xs_1978_, lean_object* v_v_1979_, lean_object* v_i_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(v_xs_1978_, v_v_1979_, v_i_1980_);
lean_dec_ref(v_v_1979_);
lean_dec_ref(v_xs_1978_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(lean_object* v_xs_1982_, lean_object* v_v_1983_){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = lean_unsigned_to_nat(0u);
v___x_1985_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(v_xs_1982_, v_v_1983_, v___x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9___boxed(lean_object* v_xs_1986_, lean_object* v_v_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(v_xs_1986_, v_v_1987_);
lean_dec_ref(v_v_1987_);
lean_dec_ref(v_xs_1986_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(lean_object* v_x_1989_, size_t v_x_1990_, lean_object* v_x_1991_){
_start:
{
if (lean_obj_tag(v_x_1989_) == 0)
{
lean_object* v_es_1992_; lean_object* v___x_1993_; size_t v___x_1994_; size_t v___x_1995_; lean_object* v_j_1996_; lean_object* v_entry_1997_; 
v_es_1992_ = lean_ctor_get(v_x_1989_, 0);
v___x_1993_ = lean_box(2);
v___x_1994_ = ((size_t)31ULL);
v___x_1995_ = lean_usize_land(v_x_1990_, v___x_1994_);
v_j_1996_ = lean_usize_to_nat(v___x_1995_);
v_entry_1997_ = lean_array_get(v___x_1993_, v_es_1992_, v_j_1996_);
switch(lean_obj_tag(v_entry_1997_))
{
case 0:
{
lean_object* v_key_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v_key_1998_ = lean_ctor_get(v_entry_1997_, 0);
lean_inc(v_key_1998_);
lean_dec_ref_known(v_entry_1997_, 2);
v___x_1999_ = l_Lean_Meta_Grind_Origin_key(v_x_1991_);
v___x_2000_ = l_Lean_Meta_Grind_Origin_key(v_key_1998_);
lean_dec(v_key_1998_);
v___x_2001_ = lean_name_eq(v___x_1999_, v___x_2000_);
lean_dec(v___x_2000_);
lean_dec(v___x_1999_);
if (v___x_2001_ == 0)
{
lean_dec(v_j_1996_);
return v_x_1989_;
}
else
{
lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2009_; 
lean_inc_ref(v_es_1992_);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_x_1989_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; 
v_unused_2010_ = lean_ctor_get(v_x_1989_, 0);
lean_dec(v_unused_2010_);
v___x_2003_ = v_x_1989_;
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
else
{
lean_dec(v_x_1989_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_array_set(v_es_1992_, v_j_1996_, v___x_1993_);
lean_dec(v_j_1996_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2005_);
v___x_2007_ = v___x_2003_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
case 1:
{
lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2045_; 
lean_inc_ref(v_es_1992_);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_x_1989_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v_x_1989_, 0);
lean_dec(v_unused_2046_);
v___x_2012_ = v_x_1989_;
v_isShared_2013_ = v_isSharedCheck_2045_;
goto v_resetjp_2011_;
}
else
{
lean_dec(v_x_1989_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2045_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v_node_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2044_; 
v_node_2014_ = lean_ctor_get(v_entry_1997_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_entry_1997_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2016_ = v_entry_1997_;
v_isShared_2017_ = v_isSharedCheck_2044_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_node_2014_);
lean_dec(v_entry_1997_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2044_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
size_t v___x_2018_; lean_object* v_entries_2019_; size_t v___x_2020_; lean_object* v_newNode_2021_; lean_object* v___x_2022_; 
v___x_2018_ = ((size_t)5ULL);
v_entries_2019_ = lean_array_set(v_es_1992_, v_j_1996_, v___x_1993_);
v___x_2020_ = lean_usize_shift_right(v_x_1990_, v___x_2018_);
v_newNode_2021_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_node_2014_, v___x_2020_, v_x_1991_);
lean_inc_ref(v_newNode_2021_);
v___x_2022_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2021_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v___x_2024_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v_newNode_2021_);
v___x_2024_ = v___x_2016_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_newNode_2021_);
v___x_2024_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2025_ = lean_array_set(v_entries_2019_, v_j_1996_, v___x_2024_);
lean_dec(v_j_1996_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2025_);
v___x_2027_ = v___x_2012_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
else
{
lean_object* v_val_2030_; lean_object* v_fst_2031_; lean_object* v_snd_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2043_; 
lean_dec_ref(v_newNode_2021_);
lean_del_object(v___x_2016_);
v_val_2030_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_val_2030_);
lean_dec_ref_known(v___x_2022_, 1);
v_fst_2031_ = lean_ctor_get(v_val_2030_, 0);
v_snd_2032_ = lean_ctor_get(v_val_2030_, 1);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_val_2030_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2034_ = v_val_2030_;
v_isShared_2035_ = v_isSharedCheck_2043_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_snd_2032_);
lean_inc(v_fst_2031_);
lean_dec(v_val_2030_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2043_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_fst_2031_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_snd_2032_);
v___x_2037_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2038_ = lean_array_set(v_entries_2019_, v_j_1996_, v___x_2037_);
lean_dec(v_j_1996_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2038_);
v___x_2040_ = v___x_2012_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_1996_);
return v_x_1989_;
}
}
}
else
{
lean_object* v_ks_2047_; lean_object* v_vs_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2062_; 
v_ks_2047_ = lean_ctor_get(v_x_1989_, 0);
v_vs_2048_ = lean_ctor_get(v_x_1989_, 1);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_x_1989_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2050_ = v_x_1989_;
v_isShared_2051_ = v_isSharedCheck_2062_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_vs_2048_);
lean_inc(v_ks_2047_);
lean_dec(v_x_1989_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2062_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(v_ks_2047_, v_x_1991_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v___x_2054_; 
if (v_isShared_2051_ == 0)
{
v___x_2054_ = v___x_2050_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_ks_2047_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_vs_2048_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
else
{
lean_object* v_val_2056_; lean_object* v_keys_x27_2057_; lean_object* v_vals_x27_2058_; lean_object* v___x_2060_; 
v_val_2056_ = lean_ctor_get(v___x_2052_, 0);
lean_inc_n(v_val_2056_, 2);
lean_dec_ref_known(v___x_2052_, 1);
v_keys_x27_2057_ = l_Array_eraseIdx___redArg(v_ks_2047_, v_val_2056_);
v_vals_x27_2058_ = l_Array_eraseIdx___redArg(v_vs_2048_, v_val_2056_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 1, v_vals_x27_2058_);
lean_ctor_set(v___x_2050_, 0, v_keys_x27_2057_);
v___x_2060_ = v___x_2050_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_keys_x27_2057_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_vals_x27_2058_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2063_, lean_object* v_x_2064_, lean_object* v_x_2065_){
_start:
{
size_t v_x_1667__boxed_2066_; lean_object* v_res_2067_; 
v_x_1667__boxed_2066_ = lean_unbox_usize(v_x_2064_);
lean_dec(v_x_2064_);
v_res_2067_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2063_, v_x_1667__boxed_2066_, v_x_2065_);
lean_dec_ref(v_x_2065_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(lean_object* v_x_2068_, lean_object* v_x_2069_){
_start:
{
uint64_t v___y_2071_; lean_object* v___x_2074_; 
v___x_2074_ = l_Lean_Meta_Grind_Origin_key(v_x_2069_);
if (lean_obj_tag(v___x_2074_) == 0)
{
uint64_t v___x_2075_; 
v___x_2075_ = 1723ULL;
v___y_2071_ = v___x_2075_;
goto v___jp_2070_;
}
else
{
uint64_t v_hash_2076_; 
v_hash_2076_ = lean_ctor_get_uint64(v___x_2074_, sizeof(void*)*2);
lean_dec(v___x_2074_);
v___y_2071_ = v_hash_2076_;
goto v___jp_2070_;
}
v___jp_2070_:
{
size_t v_h_2072_; lean_object* v___x_2073_; 
v_h_2072_ = lean_uint64_to_usize(v___y_2071_);
v___x_2073_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2068_, v_h_2072_, v_x_2069_);
return v___x_2073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg___boxed(lean_object* v_x_2077_, lean_object* v_x_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_x_2077_, v_x_2078_);
lean_dec_ref(v_x_2078_);
return v_res_2079_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2083_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2));
v___x_2084_ = lean_unsigned_to_nat(6u);
v___x_2085_ = lean_unsigned_to_nat(82u);
v___x_2086_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__1));
v___x_2087_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__0));
v___x_2088_ = l_mkPanicMessageWithDecl(v___x_2087_, v___x_2086_, v___x_2085_, v___x_2084_, v___x_2083_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0(lean_object* v_s_2089_, lean_object* v_thm_2090_){
_start:
{
lean_object* v_symbols_2094_; 
v_symbols_2094_ = lean_ctor_get(v_thm_2090_, 4);
lean_inc(v_symbols_2094_);
if (lean_obj_tag(v_symbols_2094_) == 1)
{
lean_object* v_head_2095_; 
v_head_2095_ = lean_ctor_get(v_symbols_2094_, 0);
lean_inc(v_head_2095_);
if (lean_obj_tag(v_head_2095_) == 2)
{
lean_object* v_levelParams_2096_; lean_object* v_proof_2097_; lean_object* v_numParams_2098_; lean_object* v_patterns_2099_; lean_object* v_origin_2100_; lean_object* v_kind_2101_; uint8_t v_minIndexable_2102_; lean_object* v_cnstrs_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2154_; 
v_levelParams_2096_ = lean_ctor_get(v_thm_2090_, 0);
v_proof_2097_ = lean_ctor_get(v_thm_2090_, 1);
v_numParams_2098_ = lean_ctor_get(v_thm_2090_, 2);
v_patterns_2099_ = lean_ctor_get(v_thm_2090_, 3);
v_origin_2100_ = lean_ctor_get(v_thm_2090_, 5);
v_kind_2101_ = lean_ctor_get(v_thm_2090_, 6);
v_minIndexable_2102_ = lean_ctor_get_uint8(v_thm_2090_, sizeof(void*)*8);
v_cnstrs_2103_ = lean_ctor_get(v_thm_2090_, 7);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_thm_2090_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v_thm_2090_, 4);
lean_dec(v_unused_2155_);
v___x_2105_ = v_thm_2090_;
v_isShared_2106_ = v_isSharedCheck_2154_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_cnstrs_2103_);
lean_inc(v_kind_2101_);
lean_inc(v_origin_2100_);
lean_inc(v_patterns_2099_);
lean_inc(v_numParams_2098_);
lean_inc(v_proof_2097_);
lean_inc(v_levelParams_2096_);
lean_dec(v_thm_2090_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2154_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v_tail_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2152_; 
v_tail_2107_ = lean_ctor_get(v_symbols_2094_, 1);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_symbols_2094_);
if (v_isSharedCheck_2152_ == 0)
{
lean_object* v_unused_2153_; 
v_unused_2153_ = lean_ctor_get(v_symbols_2094_, 0);
lean_dec(v_unused_2153_);
v___x_2109_ = v_symbols_2094_;
v_isShared_2110_ = v_isSharedCheck_2152_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_tail_2107_);
lean_dec(v_symbols_2094_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2152_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v_constName_2111_; lean_object* v_smap_2112_; lean_object* v_origins_2113_; lean_object* v_erased_2114_; lean_object* v_omap_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2151_; 
v_constName_2111_ = lean_ctor_get(v_head_2095_, 0);
lean_inc(v_constName_2111_);
lean_dec_ref_known(v_head_2095_, 1);
v_smap_2112_ = lean_ctor_get(v_s_2089_, 0);
v_origins_2113_ = lean_ctor_get(v_s_2089_, 1);
v_erased_2114_ = lean_ctor_get(v_s_2089_, 2);
v_omap_2115_ = lean_ctor_get(v_s_2089_, 3);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_s_2089_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2117_ = v_s_2089_;
v_isShared_2118_ = v_isSharedCheck_2151_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_omap_2115_);
lean_inc(v_erased_2114_);
lean_inc(v_origins_2113_);
lean_inc(v_smap_2112_);
lean_dec(v_s_2089_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2151_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v_thm_2120_; 
lean_inc_ref(v_origin_2100_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 4, v_tail_2107_);
v_thm_2120_ = v___x_2105_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_levelParams_2096_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v_proof_2097_);
lean_ctor_set(v_reuseFailAlloc_2150_, 2, v_numParams_2098_);
lean_ctor_set(v_reuseFailAlloc_2150_, 3, v_patterns_2099_);
lean_ctor_set(v_reuseFailAlloc_2150_, 4, v_tail_2107_);
lean_ctor_set(v_reuseFailAlloc_2150_, 5, v_origin_2100_);
lean_ctor_set(v_reuseFailAlloc_2150_, 6, v_kind_2101_);
lean_ctor_set(v_reuseFailAlloc_2150_, 7, v_cnstrs_2103_);
lean_ctor_set_uint8(v_reuseFailAlloc_2150_, sizeof(void*)*8, v_minIndexable_2102_);
v_thm_2120_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
lean_object* v___x_2121_; lean_object* v_origins_2122_; lean_object* v_erased_2123_; lean_object* v___y_2125_; lean_object* v___x_2143_; 
v___x_2121_ = lean_box(0);
lean_inc_ref(v_origin_2100_);
v_origins_2122_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_origins_2113_, v_origin_2100_, v___x_2121_);
v_erased_2123_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_erased_2114_, v_origin_2100_);
v___x_2143_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_smap_2112_, v_constName_2111_);
if (lean_obj_tag(v___x_2143_) == 1)
{
lean_object* v_val_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v_val_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_val_2144_);
lean_dec_ref_known(v___x_2143_, 1);
lean_inc_ref(v_thm_2120_);
v___x_2145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2145_, 0, v_thm_2120_);
lean_ctor_set(v___x_2145_, 1, v_val_2144_);
v___x_2146_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2112_, v_constName_2111_, v___x_2145_);
v___y_2125_ = v___x_2146_;
goto v___jp_2124_;
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
lean_dec(v___x_2143_);
v___x_2147_ = lean_box(0);
lean_inc_ref(v_thm_2120_);
v___x_2148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2148_, 0, v_thm_2120_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
v___x_2149_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2112_, v_constName_2111_, v___x_2148_);
v___y_2125_ = v___x_2149_;
goto v___jp_2124_;
}
v___jp_2124_:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_omap_2115_, v_origin_2100_);
if (lean_obj_tag(v___x_2126_) == 1)
{
lean_object* v_val_2127_; lean_object* v___x_2129_; 
v_val_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_val_2127_);
lean_dec_ref_known(v___x_2126_, 1);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 1, v_val_2127_);
lean_ctor_set(v___x_2109_, 0, v_thm_2120_);
v___x_2129_ = v___x_2109_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_thm_2120_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_val_2127_);
v___x_2129_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2115_, v_origin_2100_, v___x_2129_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 3, v___x_2130_);
lean_ctor_set(v___x_2117_, 2, v_erased_2123_);
lean_ctor_set(v___x_2117_, 1, v_origins_2122_);
lean_ctor_set(v___x_2117_, 0, v___y_2125_);
v___x_2132_ = v___x_2117_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___y_2125_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_origins_2122_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v_erased_2123_);
lean_ctor_set(v_reuseFailAlloc_2133_, 3, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
lean_dec(v___x_2126_);
v___x_2135_ = lean_box(0);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 1, v___x_2135_);
lean_ctor_set(v___x_2109_, 0, v_thm_2120_);
v___x_2137_ = v___x_2109_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_thm_2120_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2138_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2115_, v_origin_2100_, v___x_2137_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 3, v___x_2138_);
lean_ctor_set(v___x_2117_, 2, v_erased_2123_);
lean_ctor_set(v___x_2117_, 1, v_origins_2122_);
lean_ctor_set(v___x_2117_, 0, v___y_2125_);
v___x_2140_ = v___x_2117_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___y_2125_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_origins_2122_);
lean_ctor_set(v_reuseFailAlloc_2141_, 2, v_erased_2123_);
lean_ctor_set(v_reuseFailAlloc_2141_, 3, v___x_2138_);
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
}
}
}
}
}
else
{
lean_dec_ref_known(v_symbols_2094_, 2);
lean_dec(v_head_2095_);
lean_dec_ref(v_thm_2090_);
lean_dec_ref(v_s_2089_);
goto v___jp_2091_;
}
}
else
{
lean_dec(v_symbols_2094_);
lean_dec_ref(v_thm_2090_);
lean_dec_ref(v_s_2089_);
goto v___jp_2091_;
}
v___jp_2091_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3, &l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3);
v___x_2093_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0(v___x_2092_);
return v___x_2093_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1_spec__6(lean_object* v_msg_2156_){
_start:
{
lean_object* v___f_2157_; lean_object* v___f_2158_; lean_object* v___f_2159_; lean_object* v___f_2160_; lean_object* v___f_2161_; lean_object* v___f_2162_; lean_object* v___f_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___f_2157_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0));
v___f_2158_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1));
v___f_2159_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2));
v___f_2160_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3));
v___f_2161_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4));
v___f_2162_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5));
v___f_2163_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6));
v___x_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___f_2157_);
lean_ctor_set(v___x_2164_, 1, v___f_2158_);
v___x_2165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
lean_ctor_set(v___x_2165_, 1, v___f_2159_);
lean_ctor_set(v___x_2165_, 2, v___f_2160_);
lean_ctor_set(v___x_2165_, 3, v___f_2161_);
lean_ctor_set(v___x_2165_, 4, v___f_2162_);
v___x_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set(v___x_2166_, 1, v___f_2163_);
v___x_2167_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7, &l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once, _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7);
v___x_2168_ = l_instInhabitedOfMonad___redArg(v___x_2166_, v___x_2167_);
v___x_2169_ = lean_panic_fn_borrowed(v___x_2168_, v_msg_2156_);
lean_dec(v___x_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1(lean_object* v_s_2170_, lean_object* v_thm_2171_){
_start:
{
lean_object* v_symbols_2175_; 
v_symbols_2175_ = lean_ctor_get(v_thm_2171_, 2);
lean_inc(v_symbols_2175_);
if (lean_obj_tag(v_symbols_2175_) == 1)
{
lean_object* v_head_2176_; 
v_head_2176_ = lean_ctor_get(v_symbols_2175_, 0);
lean_inc(v_head_2176_);
if (lean_obj_tag(v_head_2176_) == 2)
{
lean_object* v_levelParams_2177_; lean_object* v_proof_2178_; lean_object* v_origin_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2230_; 
v_levelParams_2177_ = lean_ctor_get(v_thm_2171_, 0);
v_proof_2178_ = lean_ctor_get(v_thm_2171_, 1);
v_origin_2179_ = lean_ctor_get(v_thm_2171_, 3);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_thm_2171_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v_thm_2171_, 2);
lean_dec(v_unused_2231_);
v___x_2181_ = v_thm_2171_;
v_isShared_2182_ = v_isSharedCheck_2230_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_origin_2179_);
lean_inc(v_proof_2178_);
lean_inc(v_levelParams_2177_);
lean_dec(v_thm_2171_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2230_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v_tail_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2228_; 
v_tail_2183_ = lean_ctor_get(v_symbols_2175_, 1);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_symbols_2175_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; 
v_unused_2229_ = lean_ctor_get(v_symbols_2175_, 0);
lean_dec(v_unused_2229_);
v___x_2185_ = v_symbols_2175_;
v_isShared_2186_ = v_isSharedCheck_2228_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_tail_2183_);
lean_dec(v_symbols_2175_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2228_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v_constName_2187_; lean_object* v_smap_2188_; lean_object* v_origins_2189_; lean_object* v_erased_2190_; lean_object* v_omap_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2227_; 
v_constName_2187_ = lean_ctor_get(v_head_2176_, 0);
lean_inc(v_constName_2187_);
lean_dec_ref_known(v_head_2176_, 1);
v_smap_2188_ = lean_ctor_get(v_s_2170_, 0);
v_origins_2189_ = lean_ctor_get(v_s_2170_, 1);
v_erased_2190_ = lean_ctor_get(v_s_2170_, 2);
v_omap_2191_ = lean_ctor_get(v_s_2170_, 3);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_s_2170_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2193_ = v_s_2170_;
v_isShared_2194_ = v_isSharedCheck_2227_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_omap_2191_);
lean_inc(v_erased_2190_);
lean_inc(v_origins_2189_);
lean_inc(v_smap_2188_);
lean_dec(v_s_2170_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2227_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v_thm_2196_; 
lean_inc_ref(v_origin_2179_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 2, v_tail_2183_);
v_thm_2196_ = v___x_2181_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_levelParams_2177_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_proof_2178_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_tail_2183_);
lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_origin_2179_);
v_thm_2196_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2197_; lean_object* v_origins_2198_; lean_object* v_erased_2199_; lean_object* v___y_2201_; lean_object* v___x_2219_; 
v___x_2197_ = lean_box(0);
lean_inc_ref(v_origin_2179_);
v_origins_2198_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_origins_2189_, v_origin_2179_, v___x_2197_);
v_erased_2199_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_erased_2190_, v_origin_2179_);
v___x_2219_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_smap_2188_, v_constName_2187_);
if (lean_obj_tag(v___x_2219_) == 1)
{
lean_object* v_val_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v_val_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_val_2220_);
lean_dec_ref_known(v___x_2219_, 1);
lean_inc_ref(v_thm_2196_);
v___x_2221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2221_, 0, v_thm_2196_);
lean_ctor_set(v___x_2221_, 1, v_val_2220_);
v___x_2222_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2188_, v_constName_2187_, v___x_2221_);
v___y_2201_ = v___x_2222_;
goto v___jp_2200_;
}
else
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_dec(v___x_2219_);
v___x_2223_ = lean_box(0);
lean_inc_ref(v_thm_2196_);
v___x_2224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2224_, 0, v_thm_2196_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
v___x_2225_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2188_, v_constName_2187_, v___x_2224_);
v___y_2201_ = v___x_2225_;
goto v___jp_2200_;
}
v___jp_2200_:
{
lean_object* v___x_2202_; 
v___x_2202_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_omap_2191_, v_origin_2179_);
if (lean_obj_tag(v___x_2202_) == 1)
{
lean_object* v_val_2203_; lean_object* v___x_2205_; 
v_val_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_val_2203_);
lean_dec_ref_known(v___x_2202_, 1);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 1, v_val_2203_);
lean_ctor_set(v___x_2185_, 0, v_thm_2196_);
v___x_2205_ = v___x_2185_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_thm_2196_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_val_2203_);
v___x_2205_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
lean_object* v___x_2206_; lean_object* v___x_2208_; 
v___x_2206_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2191_, v_origin_2179_, v___x_2205_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 3, v___x_2206_);
lean_ctor_set(v___x_2193_, 2, v_erased_2199_);
lean_ctor_set(v___x_2193_, 1, v_origins_2198_);
lean_ctor_set(v___x_2193_, 0, v___y_2201_);
v___x_2208_ = v___x_2193_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___y_2201_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_origins_2198_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_erased_2199_);
lean_ctor_set(v_reuseFailAlloc_2209_, 3, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
else
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
lean_dec(v___x_2202_);
v___x_2211_ = lean_box(0);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 1, v___x_2211_);
lean_ctor_set(v___x_2185_, 0, v_thm_2196_);
v___x_2213_ = v___x_2185_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_thm_2196_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2214_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2191_, v_origin_2179_, v___x_2213_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 3, v___x_2214_);
lean_ctor_set(v___x_2193_, 2, v_erased_2199_);
lean_ctor_set(v___x_2193_, 1, v_origins_2198_);
lean_ctor_set(v___x_2193_, 0, v___y_2201_);
v___x_2216_ = v___x_2193_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___y_2201_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v_origins_2198_);
lean_ctor_set(v_reuseFailAlloc_2217_, 2, v_erased_2199_);
lean_ctor_set(v_reuseFailAlloc_2217_, 3, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
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
lean_dec_ref_known(v_symbols_2175_, 2);
lean_dec(v_head_2176_);
lean_dec_ref(v_thm_2171_);
lean_dec_ref(v_s_2170_);
goto v___jp_2172_;
}
}
else
{
lean_dec(v_symbols_2175_);
lean_dec_ref(v_thm_2171_);
lean_dec_ref(v_s_2170_);
goto v___jp_2172_;
}
v___jp_2172_:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3, &l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3);
v___x_2174_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1_spec__6(v___x_2173_);
return v___x_2174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionState_addEntry(lean_object* v_s_2232_, lean_object* v_e_2233_){
_start:
{
switch(lean_obj_tag(v_e_2233_))
{
case 0:
{
lean_object* v_declName_2234_; lean_object* v_casesTypes_2235_; lean_object* v_extThms_2236_; lean_object* v_funCC_2237_; lean_object* v_ematch_2238_; lean_object* v_inj_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2248_; 
v_declName_2234_ = lean_ctor_get(v_e_2233_, 0);
lean_inc(v_declName_2234_);
lean_dec_ref_known(v_e_2233_, 1);
v_casesTypes_2235_ = lean_ctor_get(v_s_2232_, 0);
v_extThms_2236_ = lean_ctor_get(v_s_2232_, 1);
v_funCC_2237_ = lean_ctor_get(v_s_2232_, 2);
v_ematch_2238_ = lean_ctor_get(v_s_2232_, 3);
v_inj_2239_ = lean_ctor_get(v_s_2232_, 4);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_s_2232_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2241_ = v_s_2232_;
v_isShared_2242_ = v_isSharedCheck_2248_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_inj_2239_);
lean_inc(v_ematch_2238_);
lean_inc(v_funCC_2237_);
lean_inc(v_extThms_2236_);
lean_inc(v_casesTypes_2235_);
lean_dec(v_s_2232_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2248_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2246_; 
v___x_2243_ = lean_box(0);
v___x_2244_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_extThms_2236_, v_declName_2234_, v___x_2243_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 1, v___x_2244_);
v___x_2246_ = v___x_2241_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_casesTypes_2235_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v___x_2244_);
lean_ctor_set(v_reuseFailAlloc_2247_, 2, v_funCC_2237_);
lean_ctor_set(v_reuseFailAlloc_2247_, 3, v_ematch_2238_);
lean_ctor_set(v_reuseFailAlloc_2247_, 4, v_inj_2239_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
case 1:
{
lean_object* v_declName_2249_; lean_object* v_casesTypes_2250_; lean_object* v_extThms_2251_; lean_object* v_funCC_2252_; lean_object* v_ematch_2253_; lean_object* v_inj_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2262_; 
v_declName_2249_ = lean_ctor_get(v_e_2233_, 0);
lean_inc(v_declName_2249_);
lean_dec_ref_known(v_e_2233_, 1);
v_casesTypes_2250_ = lean_ctor_get(v_s_2232_, 0);
v_extThms_2251_ = lean_ctor_get(v_s_2232_, 1);
v_funCC_2252_ = lean_ctor_get(v_s_2232_, 2);
v_ematch_2253_ = lean_ctor_get(v_s_2232_, 3);
v_inj_2254_ = lean_ctor_get(v_s_2232_, 4);
v_isSharedCheck_2262_ = !lean_is_exclusive(v_s_2232_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2256_ = v_s_2232_;
v_isShared_2257_ = v_isSharedCheck_2262_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_inj_2254_);
lean_inc(v_ematch_2253_);
lean_inc(v_funCC_2252_);
lean_inc(v_extThms_2251_);
lean_inc(v_casesTypes_2250_);
lean_dec(v_s_2232_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2262_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2258_ = l_Lean_NameSet_insert(v_funCC_2252_, v_declName_2249_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 2, v___x_2258_);
v___x_2260_ = v___x_2256_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_casesTypes_2250_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v_extThms_2251_);
lean_ctor_set(v_reuseFailAlloc_2261_, 2, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2261_, 3, v_ematch_2253_);
lean_ctor_set(v_reuseFailAlloc_2261_, 4, v_inj_2254_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
case 2:
{
lean_object* v_declName_2263_; uint8_t v_eager_2264_; lean_object* v_casesTypes_2265_; lean_object* v_extThms_2266_; lean_object* v_funCC_2267_; lean_object* v_ematch_2268_; lean_object* v_inj_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2278_; 
v_declName_2263_ = lean_ctor_get(v_e_2233_, 0);
lean_inc(v_declName_2263_);
v_eager_2264_ = lean_ctor_get_uint8(v_e_2233_, sizeof(void*)*1);
lean_dec_ref_known(v_e_2233_, 1);
v_casesTypes_2265_ = lean_ctor_get(v_s_2232_, 0);
v_extThms_2266_ = lean_ctor_get(v_s_2232_, 1);
v_funCC_2267_ = lean_ctor_get(v_s_2232_, 2);
v_ematch_2268_ = lean_ctor_get(v_s_2232_, 3);
v_inj_2269_ = lean_ctor_get(v_s_2232_, 4);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_s_2232_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2271_ = v_s_2232_;
v_isShared_2272_ = v_isSharedCheck_2278_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_inj_2269_);
lean_inc(v_ematch_2268_);
lean_inc(v_funCC_2267_);
lean_inc(v_extThms_2266_);
lean_inc(v_casesTypes_2265_);
lean_dec(v_s_2232_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2278_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2273_ = lean_box(v_eager_2264_);
v___x_2274_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_casesTypes_2265_, v_declName_2263_, v___x_2273_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2274_);
v___x_2276_ = v___x_2271_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_extThms_2266_);
lean_ctor_set(v_reuseFailAlloc_2277_, 2, v_funCC_2267_);
lean_ctor_set(v_reuseFailAlloc_2277_, 3, v_ematch_2268_);
lean_ctor_set(v_reuseFailAlloc_2277_, 4, v_inj_2269_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
case 3:
{
lean_object* v_thm_2279_; lean_object* v_casesTypes_2280_; lean_object* v_extThms_2281_; lean_object* v_funCC_2282_; lean_object* v_ematch_2283_; lean_object* v_inj_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2292_; 
v_thm_2279_ = lean_ctor_get(v_e_2233_, 0);
lean_inc_ref(v_thm_2279_);
lean_dec_ref_known(v_e_2233_, 1);
v_casesTypes_2280_ = lean_ctor_get(v_s_2232_, 0);
v_extThms_2281_ = lean_ctor_get(v_s_2232_, 1);
v_funCC_2282_ = lean_ctor_get(v_s_2232_, 2);
v_ematch_2283_ = lean_ctor_get(v_s_2232_, 3);
v_inj_2284_ = lean_ctor_get(v_s_2232_, 4);
v_isSharedCheck_2292_ = !lean_is_exclusive(v_s_2232_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2286_ = v_s_2232_;
v_isShared_2287_ = v_isSharedCheck_2292_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_inj_2284_);
lean_inc(v_ematch_2283_);
lean_inc(v_funCC_2282_);
lean_inc(v_extThms_2281_);
lean_inc(v_casesTypes_2280_);
lean_dec(v_s_2232_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2292_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2288_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0(v_ematch_2283_, v_thm_2279_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 3, v___x_2288_);
v___x_2290_ = v___x_2286_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_casesTypes_2280_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v_extThms_2281_);
lean_ctor_set(v_reuseFailAlloc_2291_, 2, v_funCC_2282_);
lean_ctor_set(v_reuseFailAlloc_2291_, 3, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2291_, 4, v_inj_2284_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
default: 
{
lean_object* v_thm_2293_; lean_object* v_casesTypes_2294_; lean_object* v_extThms_2295_; lean_object* v_funCC_2296_; lean_object* v_ematch_2297_; lean_object* v_inj_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2306_; 
v_thm_2293_ = lean_ctor_get(v_e_2233_, 0);
lean_inc_ref(v_thm_2293_);
lean_dec_ref_known(v_e_2233_, 1);
v_casesTypes_2294_ = lean_ctor_get(v_s_2232_, 0);
v_extThms_2295_ = lean_ctor_get(v_s_2232_, 1);
v_funCC_2296_ = lean_ctor_get(v_s_2232_, 2);
v_ematch_2297_ = lean_ctor_get(v_s_2232_, 3);
v_inj_2298_ = lean_ctor_get(v_s_2232_, 4);
v_isSharedCheck_2306_ = !lean_is_exclusive(v_s_2232_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2300_ = v_s_2232_;
v_isShared_2301_ = v_isSharedCheck_2306_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_inj_2298_);
lean_inc(v_ematch_2297_);
lean_inc(v_funCC_2296_);
lean_inc(v_extThms_2295_);
lean_inc(v_casesTypes_2294_);
lean_dec(v_s_2232_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2306_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2302_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1(v_inj_2298_, v_thm_2293_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 4, v___x_2302_);
v___x_2304_ = v___x_2300_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_casesTypes_2294_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_extThms_2295_);
lean_ctor_set(v_reuseFailAlloc_2305_, 2, v_funCC_2296_);
lean_ctor_set(v_reuseFailAlloc_2305_, 3, v_ematch_2297_);
lean_ctor_set(v_reuseFailAlloc_2305_, 4, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1(lean_object* v_00_u03b2_2307_, lean_object* v_x_2308_, lean_object* v_x_2309_, lean_object* v_x_2310_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_x_2308_, v_x_2309_, v_x_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2(lean_object* v_00_u03b2_2312_, lean_object* v_x_2313_, lean_object* v_x_2314_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_x_2313_, v_x_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2316_, lean_object* v_x_2317_, lean_object* v_x_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2(v_00_u03b2_2316_, v_x_2317_, v_x_2318_);
lean_dec_ref(v_x_2318_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3(lean_object* v_00_u03b2_2320_, lean_object* v_x_2321_, lean_object* v_x_2322_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_x_2321_, v_x_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2324_, lean_object* v_x_2325_, lean_object* v_x_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3(v_00_u03b2_2324_, v_x_2325_, v_x_2326_);
lean_dec_ref(v_x_2326_);
lean_dec_ref(v_x_2325_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4(lean_object* v_00_u03b2_2328_, lean_object* v_x_2329_, lean_object* v_x_2330_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_x_2329_, v_x_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___boxed(lean_object* v_00_u03b2_2332_, lean_object* v_x_2333_, lean_object* v_x_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4(v_00_u03b2_2332_, v_x_2333_, v_x_2334_);
lean_dec(v_x_2334_);
lean_dec_ref(v_x_2333_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2336_, lean_object* v_x_2337_, size_t v_x_2338_, size_t v_x_2339_, lean_object* v_x_2340_, lean_object* v_x_2341_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_2337_, v_x_2338_, v_x_2339_, v_x_2340_, v_x_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2343_, lean_object* v_x_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_){
_start:
{
size_t v_x_2238__boxed_2349_; size_t v_x_2239__boxed_2350_; lean_object* v_res_2351_; 
v_x_2238__boxed_2349_ = lean_unbox_usize(v_x_2345_);
lean_dec(v_x_2345_);
v_x_2239__boxed_2350_ = lean_unbox_usize(v_x_2346_);
lean_dec(v_x_2346_);
v_res_2351_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(v_00_u03b2_2343_, v_x_2344_, v_x_2238__boxed_2349_, v_x_2239__boxed_2350_, v_x_2347_, v_x_2348_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2352_, lean_object* v_x_2353_, size_t v_x_2354_, lean_object* v_x_2355_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2353_, v_x_2354_, v_x_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2357_, lean_object* v_x_2358_, lean_object* v_x_2359_, lean_object* v_x_2360_){
_start:
{
size_t v_x_2255__boxed_2361_; lean_object* v_res_2362_; 
v_x_2255__boxed_2361_ = lean_unbox_usize(v_x_2359_);
lean_dec(v_x_2359_);
v_res_2362_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(v_00_u03b2_2357_, v_x_2358_, v_x_2255__boxed_2361_, v_x_2360_);
lean_dec_ref(v_x_2360_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(lean_object* v_00_u03b2_2363_, lean_object* v_x_2364_, size_t v_x_2365_, lean_object* v_x_2366_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_2364_, v_x_2365_, v_x_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2368_, lean_object* v_x_2369_, lean_object* v_x_2370_, lean_object* v_x_2371_){
_start:
{
size_t v_x_2266__boxed_2372_; lean_object* v_res_2373_; 
v_x_2266__boxed_2372_ = lean_unbox_usize(v_x_2370_);
lean_dec(v_x_2370_);
v_res_2373_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(v_00_u03b2_2368_, v_x_2369_, v_x_2266__boxed_2372_, v_x_2371_);
lean_dec_ref(v_x_2371_);
lean_dec_ref(v_x_2369_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(lean_object* v_00_u03b2_2374_, lean_object* v_x_2375_, size_t v_x_2376_, lean_object* v_x_2377_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_2375_, v_x_2376_, v_x_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2379_, lean_object* v_x_2380_, lean_object* v_x_2381_, lean_object* v_x_2382_){
_start:
{
size_t v_x_2277__boxed_2383_; lean_object* v_res_2384_; 
v_x_2277__boxed_2383_ = lean_unbox_usize(v_x_2381_);
lean_dec(v_x_2381_);
v_res_2384_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(v_00_u03b2_2379_, v_x_2380_, v_x_2277__boxed_2383_, v_x_2382_);
lean_dec(v_x_2382_);
lean_dec_ref(v_x_2380_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2385_, lean_object* v_n_2386_, lean_object* v_k_2387_, lean_object* v_v_2388_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(v_n_2386_, v_k_2387_, v_v_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2390_, size_t v_depth_2391_, lean_object* v_keys_2392_, lean_object* v_vals_2393_, lean_object* v_heq_2394_, lean_object* v_i_2395_, lean_object* v_entries_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_depth_2391_, v_keys_2392_, v_vals_2393_, v_i_2395_, v_entries_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2398_, lean_object* v_depth_2399_, lean_object* v_keys_2400_, lean_object* v_vals_2401_, lean_object* v_heq_2402_, lean_object* v_i_2403_, lean_object* v_entries_2404_){
_start:
{
size_t v_depth_boxed_2405_; lean_object* v_res_2406_; 
v_depth_boxed_2405_ = lean_unbox_usize(v_depth_2399_);
lean_dec(v_depth_2399_);
v_res_2406_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(v_00_u03b2_2398_, v_depth_boxed_2405_, v_keys_2400_, v_vals_2401_, v_heq_2402_, v_i_2403_, v_entries_2404_);
lean_dec_ref(v_vals_2401_);
lean_dec_ref(v_keys_2400_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12(lean_object* v_00_u03b2_2407_, lean_object* v_keys_2408_, lean_object* v_vals_2409_, lean_object* v_heq_2410_, lean_object* v_i_2411_, lean_object* v_k_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_keys_2408_, v_vals_2409_, v_i_2411_, v_k_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___boxed(lean_object* v_00_u03b2_2414_, lean_object* v_keys_2415_, lean_object* v_vals_2416_, lean_object* v_heq_2417_, lean_object* v_i_2418_, lean_object* v_k_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12(v_00_u03b2_2414_, v_keys_2415_, v_vals_2416_, v_heq_2417_, v_i_2418_, v_k_2419_);
lean_dec_ref(v_k_2419_);
lean_dec_ref(v_vals_2416_);
lean_dec_ref(v_keys_2415_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15(lean_object* v_00_u03b2_2421_, lean_object* v_keys_2422_, lean_object* v_vals_2423_, lean_object* v_heq_2424_, lean_object* v_i_2425_, lean_object* v_k_2426_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_keys_2422_, v_vals_2423_, v_i_2425_, v_k_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___boxed(lean_object* v_00_u03b2_2428_, lean_object* v_keys_2429_, lean_object* v_vals_2430_, lean_object* v_heq_2431_, lean_object* v_i_2432_, lean_object* v_k_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15(v_00_u03b2_2428_, v_keys_2429_, v_vals_2430_, v_heq_2431_, v_i_2432_, v_k_2433_);
lean_dec(v_k_2433_);
lean_dec_ref(v_vals_2430_);
lean_dec_ref(v_keys_2429_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_2435_, lean_object* v_x_2436_, lean_object* v_x_2437_, lean_object* v_x_2438_, lean_object* v_x_2439_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(v_x_2436_, v_x_2437_, v_x_2438_, v_x_2439_);
return v___x_2440_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__10));
v___x_2468_ = l_Lean_mkAtom(v___x_2467_);
return v___x_2468_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2469_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__12, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__12_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__12);
v___x_2470_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2471_ = lean_array_push(v___x_2470_, v___x_2469_);
return v___x_2471_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2480_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__17));
v___x_2481_ = l_Lean_mkAtom(v___x_2480_);
return v___x_2481_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2482_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__18, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__18_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__18);
v___x_2483_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2484_ = lean_array_push(v___x_2483_, v___x_2482_);
return v___x_2484_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__20(void){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2485_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__19, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__19_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__19);
v___x_2486_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__16));
v___x_2487_ = lean_box(2);
v___x_2488_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
lean_ctor_set(v___x_2488_, 1, v___x_2486_);
lean_ctor_set(v___x_2488_, 2, v___x_2485_);
return v___x_2488_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__21(void){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2489_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__20, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__20_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__20);
v___x_2490_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__13, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__13_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__13);
v___x_2491_ = lean_array_push(v___x_2490_, v___x_2489_);
return v___x_2491_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__22(void){
_start:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2492_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__21, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__21_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__21);
v___x_2493_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__11));
v___x_2494_ = lean_box(2);
v___x_2495_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
lean_ctor_set(v___x_2495_, 1, v___x_2493_);
lean_ctor_set(v___x_2495_, 2, v___x_2492_);
return v___x_2495_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2496_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__22, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__22_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__22);
v___x_2497_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2498_ = lean_array_push(v___x_2497_, v___x_2496_);
return v___x_2498_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2499_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__23, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__23_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__23);
v___x_2500_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__9));
v___x_2501_ = lean_box(2);
v___x_2502_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
lean_ctor_set(v___x_2502_, 1, v___x_2500_);
lean_ctor_set(v___x_2502_, 2, v___x_2499_);
return v___x_2502_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__25(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__24, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__24_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__24);
v___x_2504_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2505_ = lean_array_push(v___x_2504_, v___x_2503_);
return v___x_2505_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__26(void){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2506_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__25, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__25_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__25);
v___x_2507_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__7));
v___x_2508_ = lean_box(2);
v___x_2509_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
lean_ctor_set(v___x_2509_, 1, v___x_2507_);
lean_ctor_set(v___x_2509_, 2, v___x_2506_);
return v___x_2509_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__27(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__26, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__26_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__26);
v___x_2511_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2512_ = lean_array_push(v___x_2511_, v___x_2510_);
return v___x_2512_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__28(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2513_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__27, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__27_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__27);
v___x_2514_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__4));
v___x_2515_ = lean_box(2);
v___x_2516_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
lean_ctor_set(v___x_2516_, 1, v___x_2514_);
lean_ctor_set(v___x_2516_, 2, v___x_2513_);
return v___x_2516_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1(void){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__28, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__28_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__28);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(lean_object* v_msg_2518_){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = lean_box(0);
v___x_2520_ = lean_panic_fn_borrowed(v___x_2519_, v_msg_2518_);
return v___x_2520_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2523_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2));
v___x_2524_ = lean_unsigned_to_nat(17u);
v___x_2525_ = lean_unsigned_to_nat(203u);
v___x_2526_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___lam__0___closed__1));
v___x_2527_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___lam__0___closed__0));
v___x_2528_ = l_mkPanicMessageWithDecl(v___x_2527_, v___x_2526_, v___x_2525_, v___x_2524_, v___x_2523_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__0(lean_object* v_x_2529_, lean_object* v_e_2530_){
_start:
{
lean_object* v___y_2532_; 
switch(lean_obj_tag(v_e_2530_))
{
case 3:
{
lean_object* v_thm_2539_; lean_object* v_origin_2540_; 
v_thm_2539_ = lean_ctor_get(v_e_2530_, 0);
v_origin_2540_ = lean_ctor_get(v_thm_2539_, 5);
if (lean_obj_tag(v_origin_2540_) == 0)
{
lean_object* v_declName_2541_; 
v_declName_2541_ = lean_ctor_get(v_origin_2540_, 0);
lean_inc(v_declName_2541_);
v___y_2532_ = v_declName_2541_;
goto v___jp_2531_;
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___lam__0___closed__2, &l_Lean_Meta_Grind_mkExtension___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2);
v___x_2543_ = l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(v___x_2542_);
v___y_2532_ = v___x_2543_;
goto v___jp_2531_;
}
}
case 4:
{
lean_object* v_thm_2544_; lean_object* v_origin_2545_; 
v_thm_2544_ = lean_ctor_get(v_e_2530_, 0);
v_origin_2545_ = lean_ctor_get(v_thm_2544_, 3);
if (lean_obj_tag(v_origin_2545_) == 0)
{
lean_object* v_declName_2546_; 
v_declName_2546_ = lean_ctor_get(v_origin_2545_, 0);
lean_inc(v_declName_2546_);
v___y_2532_ = v_declName_2546_;
goto v___jp_2531_;
}
else
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___lam__0___closed__2, &l_Lean_Meta_Grind_mkExtension___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2);
v___x_2548_ = l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(v___x_2547_);
v___y_2532_ = v___x_2548_;
goto v___jp_2531_;
}
}
default: 
{
lean_object* v_declName_2549_; 
v_declName_2549_ = lean_ctor_get(v_e_2530_, 0);
lean_inc(v_declName_2549_);
v___y_2532_ = v_declName_2549_;
goto v___jp_2531_;
}
}
v___jp_2531_:
{
uint8_t v___x_2533_; 
v___x_2533_ = l_Lean_isPrivateName(v___y_2532_);
lean_dec(v___y_2532_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2534_, 0, v_e_2530_);
lean_inc_ref_n(v___x_2534_, 2);
v___x_2535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
lean_ctor_set(v___x_2535_, 2, v___x_2534_);
return v___x_2535_;
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2536_ = lean_box(0);
v___x_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2537_, 0, v_e_2530_);
v___x_2538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2536_);
lean_ctor_set(v___x_2538_, 1, v___x_2536_);
lean_ctor_set(v___x_2538_, 2, v___x_2537_);
return v___x_2538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__0___boxed(lean_object* v_x_2550_, lean_object* v_e_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_Meta_Grind_mkExtension___lam__0(v_x_2550_, v_e_2551_);
lean_dec_ref(v_x_2550_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__1(lean_object* v___y_2553_){
_start:
{
lean_inc_ref(v___y_2553_);
return v___y_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__1___boxed(lean_object* v___y_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_Meta_Grind_mkExtension___lam__1(v___y_2554_);
lean_dec_ref(v___y_2554_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension(lean_object* v_name_2559_){
_start:
{
lean_object* v___f_2561_; lean_object* v___f_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___f_2561_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__0));
v___f_2562_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__1));
v___x_2563_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__2));
v___x_2564_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__2);
v___x_2565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2565_, 0, v_name_2559_);
lean_ctor_set(v___x_2565_, 1, v___x_2563_);
lean_ctor_set(v___x_2565_, 2, v___x_2564_);
lean_ctor_set(v___x_2565_, 3, v___f_2562_);
lean_ctor_set(v___x_2565_, 4, v___f_2561_);
v___x_2566_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___boxed(lean_object* v_name_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_Meta_Grind_mkExtension(v_name_2567_);
return v_res_2569_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2570_; 
v___x_2570_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2570_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0);
v___x_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
return v___x_2572_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1);
v___x_2574_ = lean_unsigned_to_nat(0u);
v___x_2575_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
lean_ctor_set(v___x_2575_, 2, v___x_2574_);
lean_ctor_set(v___x_2575_, 3, v___x_2574_);
lean_ctor_set(v___x_2575_, 4, v___x_2573_);
lean_ctor_set(v___x_2575_, 5, v___x_2573_);
lean_ctor_set(v___x_2575_, 6, v___x_2573_);
lean_ctor_set(v___x_2575_, 7, v___x_2573_);
lean_ctor_set(v___x_2575_, 8, v___x_2573_);
lean_ctor_set(v___x_2575_, 9, v___x_2573_);
return v___x_2575_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = lean_unsigned_to_nat(32u);
v___x_2577_ = lean_mk_empty_array_with_capacity(v___x_2576_);
v___x_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
return v___x_2578_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2579_ = ((size_t)5ULL);
v___x_2580_ = lean_unsigned_to_nat(0u);
v___x_2581_ = lean_unsigned_to_nat(32u);
v___x_2582_ = lean_mk_empty_array_with_capacity(v___x_2581_);
v___x_2583_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3);
v___x_2584_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v___x_2582_);
lean_ctor_set(v___x_2584_, 2, v___x_2580_);
lean_ctor_set(v___x_2584_, 3, v___x_2580_);
lean_ctor_set_usize(v___x_2584_, 4, v___x_2579_);
return v___x_2584_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2585_ = lean_box(1);
v___x_2586_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4);
v___x_2587_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1);
v___x_2588_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
lean_ctor_set(v___x_2588_, 1, v___x_2586_);
lean_ctor_set(v___x_2588_, 2, v___x_2585_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(lean_object* v_msgData_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v___x_2593_; lean_object* v_env_2594_; lean_object* v_options_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2593_ = lean_st_ref_get(v___y_2591_);
v_env_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc_ref(v_env_2594_);
lean_dec(v___x_2593_);
v_options_2595_ = lean_ctor_get(v___y_2590_, 2);
v___x_2596_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2);
v___x_2597_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2595_);
v___x_2598_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2598_, 0, v_env_2594_);
lean_ctor_set(v___x_2598_, 1, v___x_2596_);
lean_ctor_set(v___x_2598_, 2, v___x_2597_);
lean_ctor_set(v___x_2598_, 3, v_options_2595_);
v___x_2599_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
lean_ctor_set(v___x_2599_, 1, v_msgData_2589_);
v___x_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___boxed(lean_object* v_msgData_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(v_msgData_2601_, v___y_2602_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(lean_object* v_msg_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_ref_2610_; lean_object* v___x_2611_; lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2620_; 
v_ref_2610_ = lean_ctor_get(v___y_2607_, 5);
v___x_2611_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(v_msg_2606_, v___y_2607_, v___y_2608_);
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2620_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2620_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2616_; lean_object* v___x_2618_; 
lean_inc(v_ref_2610_);
v___x_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2616_, 0, v_ref_2610_);
lean_ctor_set(v___x_2616_, 1, v_a_2612_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set_tag(v___x_2614_, 1);
lean_ctor_set(v___x_2614_, 0, v___x_2616_);
v___x_2618_ = v___x_2614_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg___boxed(lean_object* v_msg_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v_msg_2621_, v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
return v_res_2625_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = ((lean_object*)(l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__0));
v___x_2628_ = l_Lean_stringToMessageData(v___x_2627_);
return v___x_2628_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3(void){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = ((lean_object*)(l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__2));
v___x_2631_ = l_Lean_stringToMessageData(v___x_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object* v_declName_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v___x_2636_; uint8_t v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2636_ = lean_obj_once(&l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1, &l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1);
v___x_2637_ = 0;
v___x_2638_ = l_Lean_MessageData_ofConstName(v_declName_2632_, v___x_2637_);
v___x_2639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2636_);
lean_ctor_set(v___x_2639_, 1, v___x_2638_);
v___x_2640_ = lean_obj_once(&l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3, &l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3_once, _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3);
v___x_2641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2639_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
v___x_2642_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v___x_2641_, v_a_2633_, v_a_2634_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___boxed(lean_object* v_declName_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2643_, v_a_2644_, v_a_2645_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(lean_object* v_00_u03b1_2648_, lean_object* v_declName_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2649_, v_a_2650_, v_a_2651_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___boxed(lean_object* v_00_u03b1_2654_, lean_object* v_declName_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(v_00_u03b1_2654_, v_declName_2655_, v_a_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(lean_object* v_00_u03b1_2660_, lean_object* v_msg_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v_msg_2661_, v___y_2662_, v___y_2663_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___boxed(lean_object* v_00_u03b1_2666_, lean_object* v_msg_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(v_00_u03b1_2666_, v_msg_2667_, v___y_2668_, v___y_2669_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
return v_res_2671_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Theorems(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Extension(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
