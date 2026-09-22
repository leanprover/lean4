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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg();
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
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
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
v___x_41_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* v_ks_93_; lean_object* v_vs_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_112_; 
v_ks_93_ = lean_ctor_get(v_x_42_, 0);
v_vs_94_ = lean_ctor_get(v_x_42_, 1);
v_isSharedCheck_112_ = !lean_is_exclusive(v_x_42_);
if (v_isSharedCheck_112_ == 0)
{
v___x_96_ = v_x_42_;
v_isShared_97_ = v_isSharedCheck_112_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_vs_94_);
lean_inc(v_ks_93_);
lean_dec(v_x_42_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_112_;
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
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_ks_93_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v_vs_94_);
v___x_99_ = v_reuseFailAlloc_111_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v_newNode_100_; size_t v___x_101_; uint8_t v___x_102_; 
v_newNode_100_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1___redArg(v___x_99_, v_x_45_, v_x_46_);
v___x_101_ = ((size_t)7ULL);
v___x_102_ = lean_usize_dec_le(v___x_101_, v_x_44_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_103_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_100_);
v___x_104_ = lean_unsigned_to_nat(4u);
v___x_105_ = lean_nat_dec_lt(v___x_103_, v___x_104_);
lean_dec(v___x_103_);
if (v___x_105_ == 0)
{
lean_object* v_ks_106_; lean_object* v_vs_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_ks_106_ = lean_ctor_get(v_newNode_100_, 0);
lean_inc_ref(v_ks_106_);
v_vs_107_ = lean_ctor_get(v_newNode_100_, 1);
lean_inc_ref(v_vs_107_);
lean_dec_ref(v_newNode_100_);
v___x_108_ = lean_unsigned_to_nat(0u);
v___x_109_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0);
v___x_110_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_x_44_, v_ks_106_, v_vs_107_, v___x_108_, v___x_109_);
lean_dec_ref(v_vs_107_);
lean_dec_ref(v_ks_106_);
return v___x_110_;
}
else
{
return v_newNode_100_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(size_t v_depth_113_, lean_object* v_keys_114_, lean_object* v_vals_115_, lean_object* v_i_116_, lean_object* v_entries_117_){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_array_get_size(v_keys_114_);
v___x_119_ = lean_nat_dec_lt(v_i_116_, v___x_118_);
if (v___x_119_ == 0)
{
lean_dec(v_i_116_);
return v_entries_117_;
}
else
{
lean_object* v_k_120_; lean_object* v_v_121_; uint64_t v___y_123_; 
v_k_120_ = lean_array_fget_borrowed(v_keys_114_, v_i_116_);
v_v_121_ = lean_array_fget_borrowed(v_vals_115_, v_i_116_);
if (lean_obj_tag(v_k_120_) == 0)
{
uint64_t v___x_134_; 
v___x_134_ = 1723ULL;
v___y_123_ = v___x_134_;
goto v___jp_122_;
}
else
{
uint64_t v_hash_135_; 
v_hash_135_ = lean_ctor_get_uint64(v_k_120_, sizeof(void*)*2);
v___y_123_ = v_hash_135_;
goto v___jp_122_;
}
v___jp_122_:
{
size_t v_h_124_; size_t v___x_125_; lean_object* v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v_h_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_h_124_ = lean_uint64_to_usize(v___y_123_);
v___x_125_ = ((size_t)5ULL);
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = ((size_t)1ULL);
v___x_128_ = lean_usize_sub(v_depth_113_, v___x_127_);
v___x_129_ = lean_usize_mul(v___x_125_, v___x_128_);
v_h_130_ = lean_usize_shift_right(v_h_124_, v___x_129_);
v___x_131_ = lean_nat_add(v_i_116_, v___x_126_);
lean_dec(v_i_116_);
lean_inc(v_v_121_);
lean_inc(v_k_120_);
v___x_132_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_entries_117_, v_h_130_, v_depth_113_, v_k_120_, v_v_121_);
v_i_116_ = v___x_131_;
v_entries_117_ = v___x_132_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_136_, lean_object* v_keys_137_, lean_object* v_vals_138_, lean_object* v_i_139_, lean_object* v_entries_140_){
_start:
{
size_t v_depth_boxed_141_; lean_object* v_res_142_; 
v_depth_boxed_141_ = lean_unbox_usize(v_depth_136_);
lean_dec(v_depth_136_);
v_res_142_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_141_, v_keys_137_, v_vals_138_, v_i_139_, v_entries_140_);
lean_dec_ref(v_vals_138_);
lean_dec_ref(v_keys_137_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_143_, lean_object* v_x_144_, lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
size_t v_x_358__boxed_148_; size_t v_x_359__boxed_149_; lean_object* v_res_150_; 
v_x_358__boxed_148_ = lean_unbox_usize(v_x_144_);
lean_dec(v_x_144_);
v_x_359__boxed_149_ = lean_unbox_usize(v_x_145_);
lean_dec(v_x_145_);
v_res_150_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_143_, v_x_358__boxed_148_, v_x_359__boxed_149_, v_x_146_, v_x_147_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(lean_object* v_x_151_, lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
uint64_t v___y_155_; 
if (lean_obj_tag(v_x_152_) == 0)
{
uint64_t v___x_159_; 
v___x_159_ = 1723ULL;
v___y_155_ = v___x_159_;
goto v___jp_154_;
}
else
{
uint64_t v_hash_160_; 
v_hash_160_ = lean_ctor_get_uint64(v_x_152_, sizeof(void*)*2);
v___y_155_ = v_hash_160_;
goto v___jp_154_;
}
v___jp_154_:
{
size_t v___x_156_; size_t v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_uint64_to_usize(v___y_155_);
v___x_157_ = ((size_t)1ULL);
v___x_158_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_151_, v___x_156_, v___x_157_, v_x_152_, v_x_153_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_insert(lean_object* v_s_161_, lean_object* v_declName_162_, uint8_t v_eager_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_box(v_eager_163_);
v___x_165_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_s_161_, v_declName_162_, v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_insert___boxed(lean_object* v_s_166_, lean_object* v_declName_167_, lean_object* v_eager_168_){
_start:
{
uint8_t v_eager_boxed_169_; lean_object* v_res_170_; 
v_eager_boxed_169_ = lean_unbox(v_eager_168_);
v_res_170_ = l_Lean_Meta_Grind_CasesTypes_insert(v_s_166_, v_declName_167_, v_eager_boxed_169_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0(lean_object* v_00_u03b2_171_, lean_object* v_x_172_, lean_object* v_x_173_, lean_object* v_x_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_x_172_, v_x_173_, v_x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0(lean_object* v_00_u03b2_176_, lean_object* v_x_177_, size_t v_x_178_, size_t v_x_179_, lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_177_, v_x_178_, v_x_179_, v_x_180_, v_x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_183_, lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_x_188_){
_start:
{
size_t v_x_542__boxed_189_; size_t v_x_543__boxed_190_; lean_object* v_res_191_; 
v_x_542__boxed_189_ = lean_unbox_usize(v_x_185_);
lean_dec(v_x_185_);
v_x_543__boxed_190_ = lean_unbox_usize(v_x_186_);
lean_dec(v_x_186_);
v_res_191_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0(v_00_u03b2_183_, v_x_184_, v_x_542__boxed_189_, v_x_543__boxed_190_, v_x_187_, v_x_188_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_192_, lean_object* v_n_193_, lean_object* v_k_194_, lean_object* v_v_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1___redArg(v_n_193_, v_k_194_, v_v_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_197_, size_t v_depth_198_, lean_object* v_keys_199_, lean_object* v_vals_200_, lean_object* v_heq_201_, lean_object* v_i_202_, lean_object* v_entries_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_depth_198_, v_keys_199_, v_vals_200_, v_i_202_, v_entries_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_205_, lean_object* v_depth_206_, lean_object* v_keys_207_, lean_object* v_vals_208_, lean_object* v_heq_209_, lean_object* v_i_210_, lean_object* v_entries_211_){
_start:
{
size_t v_depth_boxed_212_; lean_object* v_res_213_; 
v_depth_boxed_212_ = lean_unbox_usize(v_depth_206_);
lean_dec(v_depth_206_);
v_res_213_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2(v_00_u03b2_205_, v_depth_boxed_212_, v_keys_207_, v_vals_208_, v_heq_209_, v_i_210_, v_entries_211_);
lean_dec_ref(v_vals_208_);
lean_dec_ref(v_keys_207_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_214_, lean_object* v_x_215_, lean_object* v_x_216_, lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_215_, v_x_216_, v_x_217_, v_x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0, &l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0);
v___x_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default(void){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0, &l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default;
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SymbolPriorities_insert(lean_object* v_s_224_, lean_object* v_declName_225_, lean_object* v_prio_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_s_224_, v_declName_225_, v_prio_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(lean_object* v_x_228_){
_start:
{
switch(lean_obj_tag(v_x_228_))
{
case 0:
{
lean_object* v___x_229_; 
v___x_229_ = lean_unsigned_to_nat(0u);
return v___x_229_;
}
case 1:
{
lean_object* v___x_230_; 
v___x_230_ = lean_unsigned_to_nat(1u);
return v___x_230_;
}
case 2:
{
lean_object* v___x_231_; 
v___x_231_ = lean_unsigned_to_nat(2u);
return v___x_231_;
}
case 3:
{
lean_object* v___x_232_; 
v___x_232_ = lean_unsigned_to_nat(3u);
return v___x_232_;
}
case 4:
{
lean_object* v___x_233_; 
v___x_233_ = lean_unsigned_to_nat(4u);
return v___x_233_;
}
case 5:
{
lean_object* v___x_234_; 
v___x_234_ = lean_unsigned_to_nat(5u);
return v___x_234_;
}
case 6:
{
lean_object* v___x_235_; 
v___x_235_ = lean_unsigned_to_nat(6u);
return v___x_235_;
}
case 7:
{
lean_object* v___x_236_; 
v___x_236_ = lean_unsigned_to_nat(7u);
return v___x_236_;
}
case 8:
{
lean_object* v___x_237_; 
v___x_237_ = lean_unsigned_to_nat(8u);
return v___x_237_;
}
default: 
{
lean_object* v___x_238_; 
v___x_238_ = lean_unsigned_to_nat(9u);
return v___x_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx___boxed(lean_object* v_x_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(v_x_239_);
lean_dec(v_x_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(lean_object* v_t_241_, lean_object* v_k_242_){
_start:
{
switch(lean_obj_tag(v_t_241_))
{
case 0:
{
uint8_t v_gen_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_gen_243_ = lean_ctor_get_uint8(v_t_241_, 0);
v___x_244_ = lean_box(v_gen_243_);
v___x_245_ = lean_apply_1(v_k_242_, v___x_244_);
return v___x_245_;
}
case 1:
{
uint8_t v_gen_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_gen_246_ = lean_ctor_get_uint8(v_t_241_, 0);
v___x_247_ = lean_box(v_gen_246_);
v___x_248_ = lean_apply_1(v_k_242_, v___x_247_);
return v___x_248_;
}
case 2:
{
uint8_t v_gen_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_gen_249_ = lean_ctor_get_uint8(v_t_241_, 0);
v___x_250_ = lean_box(v_gen_249_);
v___x_251_ = lean_apply_1(v_k_242_, v___x_250_);
return v___x_251_;
}
case 5:
{
uint8_t v_gen_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_gen_252_ = lean_ctor_get_uint8(v_t_241_, 0);
v___x_253_ = lean_box(v_gen_252_);
v___x_254_ = lean_apply_1(v_k_242_, v___x_253_);
return v___x_254_;
}
case 8:
{
uint8_t v_gen_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_gen_255_ = lean_ctor_get_uint8(v_t_241_, 0);
v___x_256_ = lean_box(v_gen_255_);
v___x_257_ = lean_apply_1(v_k_242_, v___x_256_);
return v___x_257_;
}
default: 
{
return v_k_242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg___boxed(lean_object* v_t_258_, lean_object* v_k_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_258_, v_k_259_);
lean_dec(v_t_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim(lean_object* v_motive_261_, lean_object* v_ctorIdx_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_k_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_263_, v_k_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___boxed(lean_object* v_motive_267_, lean_object* v_ctorIdx_268_, lean_object* v_t_269_, lean_object* v_h_270_, lean_object* v_k_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim(v_motive_267_, v_ctorIdx_268_, v_t_269_, v_h_270_, v_k_271_);
lean_dec(v_t_269_);
lean_dec(v_ctorIdx_268_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg(lean_object* v_t_273_, lean_object* v_eqLhs_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_273_, v_eqLhs_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg___boxed(lean_object* v_t_276_, lean_object* v_eqLhs_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg(v_t_276_, v_eqLhs_277_);
lean_dec(v_t_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim(lean_object* v_motive_279_, lean_object* v_t_280_, lean_object* v_h_281_, lean_object* v_eqLhs_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_280_, v_eqLhs_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___boxed(lean_object* v_motive_284_, lean_object* v_t_285_, lean_object* v_h_286_, lean_object* v_eqLhs_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim(v_motive_284_, v_t_285_, v_h_286_, v_eqLhs_287_);
lean_dec(v_t_285_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg(lean_object* v_t_289_, lean_object* v_eqRhs_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_289_, v_eqRhs_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg___boxed(lean_object* v_t_292_, lean_object* v_eqRhs_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg(v_t_292_, v_eqRhs_293_);
lean_dec(v_t_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim(lean_object* v_motive_295_, lean_object* v_t_296_, lean_object* v_h_297_, lean_object* v_eqRhs_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_296_, v_eqRhs_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___boxed(lean_object* v_motive_300_, lean_object* v_t_301_, lean_object* v_h_302_, lean_object* v_eqRhs_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim(v_motive_300_, v_t_301_, v_h_302_, v_eqRhs_303_);
lean_dec(v_t_301_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg(lean_object* v_t_305_, lean_object* v_eqBoth_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_305_, v_eqBoth_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg___boxed(lean_object* v_t_308_, lean_object* v_eqBoth_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg(v_t_308_, v_eqBoth_309_);
lean_dec(v_t_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim(lean_object* v_motive_311_, lean_object* v_t_312_, lean_object* v_h_313_, lean_object* v_eqBoth_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_312_, v_eqBoth_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___boxed(lean_object* v_motive_316_, lean_object* v_t_317_, lean_object* v_h_318_, lean_object* v_eqBoth_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim(v_motive_316_, v_t_317_, v_h_318_, v_eqBoth_319_);
lean_dec(v_t_317_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg(lean_object* v_t_321_, lean_object* v_eqBwd_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_321_, v_eqBwd_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg___boxed(lean_object* v_t_324_, lean_object* v_eqBwd_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg(v_t_324_, v_eqBwd_325_);
lean_dec(v_t_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim(lean_object* v_motive_327_, lean_object* v_t_328_, lean_object* v_h_329_, lean_object* v_eqBwd_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_328_, v_eqBwd_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___boxed(lean_object* v_motive_332_, lean_object* v_t_333_, lean_object* v_h_334_, lean_object* v_eqBwd_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim(v_motive_332_, v_t_333_, v_h_334_, v_eqBwd_335_);
lean_dec(v_t_333_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg(lean_object* v_t_337_, lean_object* v_fwd_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_337_, v_fwd_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg___boxed(lean_object* v_t_340_, lean_object* v_fwd_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg(v_t_340_, v_fwd_341_);
lean_dec(v_t_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim(lean_object* v_motive_343_, lean_object* v_t_344_, lean_object* v_h_345_, lean_object* v_fwd_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_344_, v_fwd_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___boxed(lean_object* v_motive_348_, lean_object* v_t_349_, lean_object* v_h_350_, lean_object* v_fwd_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim(v_motive_348_, v_t_349_, v_h_350_, v_fwd_351_);
lean_dec(v_t_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg(lean_object* v_t_353_, lean_object* v_bwd_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_353_, v_bwd_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg___boxed(lean_object* v_t_356_, lean_object* v_bwd_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg(v_t_356_, v_bwd_357_);
lean_dec(v_t_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim(lean_object* v_motive_359_, lean_object* v_t_360_, lean_object* v_h_361_, lean_object* v_bwd_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_360_, v_bwd_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___boxed(lean_object* v_motive_364_, lean_object* v_t_365_, lean_object* v_h_366_, lean_object* v_bwd_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim(v_motive_364_, v_t_365_, v_h_366_, v_bwd_367_);
lean_dec(v_t_365_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg(lean_object* v_t_369_, lean_object* v_leftRight_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_369_, v_leftRight_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg___boxed(lean_object* v_t_372_, lean_object* v_leftRight_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg(v_t_372_, v_leftRight_373_);
lean_dec(v_t_372_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim(lean_object* v_motive_375_, lean_object* v_t_376_, lean_object* v_h_377_, lean_object* v_leftRight_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_376_, v_leftRight_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___boxed(lean_object* v_motive_380_, lean_object* v_t_381_, lean_object* v_h_382_, lean_object* v_leftRight_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim(v_motive_380_, v_t_381_, v_h_382_, v_leftRight_383_);
lean_dec(v_t_381_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg(lean_object* v_t_385_, lean_object* v_rightLeft_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_385_, v_rightLeft_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg___boxed(lean_object* v_t_388_, lean_object* v_rightLeft_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg(v_t_388_, v_rightLeft_389_);
lean_dec(v_t_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim(lean_object* v_motive_391_, lean_object* v_t_392_, lean_object* v_h_393_, lean_object* v_rightLeft_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_392_, v_rightLeft_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___boxed(lean_object* v_motive_396_, lean_object* v_t_397_, lean_object* v_h_398_, lean_object* v_rightLeft_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim(v_motive_396_, v_t_397_, v_h_398_, v_rightLeft_399_);
lean_dec(v_t_397_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg(lean_object* v_t_401_, lean_object* v_default_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_401_, v_default_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg___boxed(lean_object* v_t_404_, lean_object* v_default_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg(v_t_404_, v_default_405_);
lean_dec(v_t_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim(lean_object* v_motive_407_, lean_object* v_t_408_, lean_object* v_h_409_, lean_object* v_default_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_408_, v_default_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___boxed(lean_object* v_motive_412_, lean_object* v_t_413_, lean_object* v_h_414_, lean_object* v_default_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Meta_Grind_EMatchTheoremKind_default_elim(v_motive_412_, v_t_413_, v_h_414_, v_default_415_);
lean_dec(v_t_413_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg(lean_object* v_t_417_, lean_object* v_user_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_417_, v_user_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg___boxed(lean_object* v_t_420_, lean_object* v_user_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg(v_t_420_, v_user_421_);
lean_dec(v_t_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim(lean_object* v_motive_423_, lean_object* v_t_424_, lean_object* v_h_425_, lean_object* v_user_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_424_, v_user_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___boxed(lean_object* v_motive_428_, lean_object* v_t_429_, lean_object* v_h_430_, lean_object* v_user_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Meta_Grind_EMatchTheoremKind_user_elim(v_motive_428_, v_t_429_, v_h_430_, v_user_431_);
lean_dec(v_t_429_);
return v_res_432_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(lean_object* v_x_437_, lean_object* v_x_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v_decide_441_; uint8_t v_gen_443_; uint8_t v_gen_x27_444_; 
v___x_439_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(v_x_437_);
v___x_440_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx(v_x_438_);
v_decide_441_ = lean_nat_dec_eq(v___x_439_, v___x_440_);
lean_dec(v___x_440_);
lean_dec(v___x_439_);
if (v_decide_441_ == 0)
{
return v_decide_441_;
}
else
{
switch(lean_obj_tag(v_x_437_))
{
case 0:
{
uint8_t v_gen_445_; uint8_t v_gen_446_; 
v_gen_445_ = lean_ctor_get_uint8(v_x_437_, 0);
v_gen_446_ = lean_ctor_get_uint8(v_x_438_, 0);
v_gen_443_ = v_gen_445_;
v_gen_x27_444_ = v_gen_446_;
goto v___jp_442_;
}
case 1:
{
uint8_t v_gen_447_; uint8_t v_gen_448_; 
v_gen_447_ = lean_ctor_get_uint8(v_x_437_, 0);
v_gen_448_ = lean_ctor_get_uint8(v_x_438_, 0);
v_gen_443_ = v_gen_447_;
v_gen_x27_444_ = v_gen_448_;
goto v___jp_442_;
}
case 2:
{
uint8_t v_gen_449_; uint8_t v_gen_450_; 
v_gen_449_ = lean_ctor_get_uint8(v_x_437_, 0);
v_gen_450_ = lean_ctor_get_uint8(v_x_438_, 0);
v_gen_443_ = v_gen_449_;
v_gen_x27_444_ = v_gen_450_;
goto v___jp_442_;
}
case 5:
{
uint8_t v_gen_451_; uint8_t v_gen_452_; 
v_gen_451_ = lean_ctor_get_uint8(v_x_437_, 0);
v_gen_452_ = lean_ctor_get_uint8(v_x_438_, 0);
v_gen_443_ = v_gen_451_;
v_gen_x27_444_ = v_gen_452_;
goto v___jp_442_;
}
case 8:
{
uint8_t v_gen_453_; uint8_t v_gen_454_; 
v_gen_453_ = lean_ctor_get_uint8(v_x_437_, 0);
v_gen_454_ = lean_ctor_get_uint8(v_x_438_, 0);
v_gen_443_ = v_gen_453_;
v_gen_x27_444_ = v_gen_454_;
goto v___jp_442_;
}
default: 
{
return v_decide_441_;
}
}
}
v___jp_442_:
{
if (v_gen_x27_444_ == 0)
{
if (v_gen_443_ == 0)
{
return v_decide_441_;
}
else
{
return v_gen_x27_444_;
}
}
else
{
return v_gen_443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq___boxed(lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
uint8_t v_res_457_; lean_object* v_r_458_; 
v_res_457_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_x_455_, v_x_456_);
lean_dec(v_x_456_);
lean_dec(v_x_455_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(2u);
v___x_483_ = lean_nat_to_int(v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_to_int(v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr(lean_object* v_x_510_, lean_object* v_prec_511_){
_start:
{
lean_object* v___y_513_; lean_object* v___y_520_; lean_object* v___y_527_; lean_object* v___y_534_; lean_object* v___y_541_; 
switch(lean_obj_tag(v_x_510_))
{
case 0:
{
uint8_t v_gen_547_; lean_object* v___y_549_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_gen_547_ = lean_ctor_get_uint8(v_x_510_, 0);
v___x_557_ = lean_unsigned_to_nat(1024u);
v___x_558_ = lean_nat_dec_le(v___x_557_, v_prec_511_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
v___x_559_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_549_ = v___x_559_;
goto v___jp_548_;
}
else
{
lean_object* v___x_560_; 
v___x_560_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_549_ = v___x_560_;
goto v___jp_548_;
}
v___jp_548_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_550_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__12));
v___x_551_ = l_Bool_repr___redArg(v_gen_547_);
v___x_552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
lean_inc(v___y_549_);
v___x_553_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_553_, 0, v___y_549_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = 0;
v___x_555_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*1, v___x_554_);
v___x_556_ = l_Repr_addAppParen(v___x_555_, v_prec_511_);
return v___x_556_;
}
}
case 1:
{
uint8_t v_gen_561_; lean_object* v___y_563_; lean_object* v___x_571_; uint8_t v___x_572_; 
v_gen_561_ = lean_ctor_get_uint8(v_x_510_, 0);
v___x_571_ = lean_unsigned_to_nat(1024u);
v___x_572_ = lean_nat_dec_le(v___x_571_, v_prec_511_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
v___x_573_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_563_ = v___x_573_;
goto v___jp_562_;
}
else
{
lean_object* v___x_574_; 
v___x_574_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_563_ = v___x_574_;
goto v___jp_562_;
}
v___jp_562_:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_564_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__17));
v___x_565_ = l_Bool_repr___redArg(v_gen_561_);
v___x_566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
lean_inc(v___y_563_);
v___x_567_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_567_, 0, v___y_563_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = 0;
v___x_569_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_569_, 0, v___x_567_);
lean_ctor_set_uint8(v___x_569_, sizeof(void*)*1, v___x_568_);
v___x_570_ = l_Repr_addAppParen(v___x_569_, v_prec_511_);
return v___x_570_;
}
}
case 2:
{
uint8_t v_gen_575_; lean_object* v___y_577_; lean_object* v___x_585_; uint8_t v___x_586_; 
v_gen_575_ = lean_ctor_get_uint8(v_x_510_, 0);
v___x_585_ = lean_unsigned_to_nat(1024u);
v___x_586_ = lean_nat_dec_le(v___x_585_, v_prec_511_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
v___x_587_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_577_ = v___x_587_;
goto v___jp_576_;
}
else
{
lean_object* v___x_588_; 
v___x_588_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_577_ = v___x_588_;
goto v___jp_576_;
}
v___jp_576_:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_578_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__20));
v___x_579_ = l_Bool_repr___redArg(v_gen_575_);
v___x_580_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_578_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
lean_inc(v___y_577_);
v___x_581_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_581_, 0, v___y_577_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = 0;
v___x_583_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*1, v___x_582_);
v___x_584_ = l_Repr_addAppParen(v___x_583_, v_prec_511_);
return v___x_584_;
}
}
case 3:
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = lean_unsigned_to_nat(1024u);
v___x_590_ = lean_nat_dec_le(v___x_589_, v_prec_511_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
v___x_591_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_527_ = v___x_591_;
goto v___jp_526_;
}
else
{
lean_object* v___x_592_; 
v___x_592_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_527_ = v___x_592_;
goto v___jp_526_;
}
}
case 4:
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = lean_unsigned_to_nat(1024u);
v___x_594_ = lean_nat_dec_le(v___x_593_, v_prec_511_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; 
v___x_595_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_534_ = v___x_595_;
goto v___jp_533_;
}
else
{
lean_object* v___x_596_; 
v___x_596_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_534_ = v___x_596_;
goto v___jp_533_;
}
}
case 5:
{
uint8_t v_gen_597_; lean_object* v___y_599_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_gen_597_ = lean_ctor_get_uint8(v_x_510_, 0);
v___x_607_ = lean_unsigned_to_nat(1024u);
v___x_608_ = lean_nat_dec_le(v___x_607_, v_prec_511_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; 
v___x_609_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_599_ = v___x_609_;
goto v___jp_598_;
}
else
{
lean_object* v___x_610_; 
v___x_610_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_599_ = v___x_610_;
goto v___jp_598_;
}
v___jp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_600_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__23));
v___x_601_ = l_Bool_repr___redArg(v_gen_597_);
v___x_602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
lean_inc(v___y_599_);
v___x_603_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_603_, 0, v___y_599_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = 0;
v___x_605_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*1, v___x_604_);
v___x_606_ = l_Repr_addAppParen(v___x_605_, v_prec_511_);
return v___x_606_;
}
}
case 6:
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(1024u);
v___x_612_ = lean_nat_dec_le(v___x_611_, v_prec_511_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
v___x_613_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_520_ = v___x_613_;
goto v___jp_519_;
}
else
{
lean_object* v___x_614_; 
v___x_614_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_520_ = v___x_614_;
goto v___jp_519_;
}
}
case 7:
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = lean_unsigned_to_nat(1024u);
v___x_616_ = lean_nat_dec_le(v___x_615_, v_prec_511_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
v___x_617_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_513_ = v___x_617_;
goto v___jp_512_;
}
else
{
lean_object* v___x_618_; 
v___x_618_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_513_ = v___x_618_;
goto v___jp_512_;
}
}
case 8:
{
uint8_t v_gen_619_; lean_object* v___y_621_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_gen_619_ = lean_ctor_get_uint8(v_x_510_, 0);
v___x_629_ = lean_unsigned_to_nat(1024u);
v___x_630_ = lean_nat_dec_le(v___x_629_, v_prec_511_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; 
v___x_631_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_621_ = v___x_631_;
goto v___jp_620_;
}
else
{
lean_object* v___x_632_; 
v___x_632_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_621_ = v___x_632_;
goto v___jp_620_;
}
v___jp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_622_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__26));
v___x_623_ = l_Bool_repr___redArg(v_gen_619_);
v___x_624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
lean_inc(v___y_621_);
v___x_625_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_625_, 0, v___y_621_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = 0;
v___x_627_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set_uint8(v___x_627_, sizeof(void*)*1, v___x_626_);
v___x_628_ = l_Repr_addAppParen(v___x_627_, v_prec_511_);
return v___x_628_;
}
}
default: 
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = lean_unsigned_to_nat(1024u);
v___x_634_ = lean_nat_dec_le(v___x_633_, v_prec_511_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
v___x_635_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_541_ = v___x_635_;
goto v___jp_540_;
}
else
{
lean_object* v___x_636_; 
v___x_636_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_541_ = v___x_636_;
goto v___jp_540_;
}
}
}
v___jp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_514_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__1));
lean_inc(v___y_513_);
v___x_515_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_515_, 0, v___y_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = 0;
v___x_517_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set_uint8(v___x_517_, sizeof(void*)*1, v___x_516_);
v___x_518_ = l_Repr_addAppParen(v___x_517_, v_prec_511_);
return v___x_518_;
}
v___jp_519_:
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_521_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__3));
lean_inc(v___y_520_);
v___x_522_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_522_, 0, v___y_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = 0;
v___x_524_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*1, v___x_523_);
v___x_525_ = l_Repr_addAppParen(v___x_524_, v_prec_511_);
return v___x_525_;
}
v___jp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_528_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__5));
lean_inc(v___y_527_);
v___x_529_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_529_, 0, v___y_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = 0;
v___x_531_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*1, v___x_530_);
v___x_532_ = l_Repr_addAppParen(v___x_531_, v_prec_511_);
return v___x_532_;
}
v___jp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_535_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__7));
lean_inc(v___y_534_);
v___x_536_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_536_, 0, v___y_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = 0;
v___x_538_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*1, v___x_537_);
v___x_539_ = l_Repr_addAppParen(v___x_538_, v_prec_511_);
return v___x_539_;
}
v___jp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_542_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__9));
lean_inc(v___y_541_);
v___x_543_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_543_, 0, v___y_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = 0;
v___x_545_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_545_, 0, v___x_543_);
lean_ctor_set_uint8(v___x_545_, sizeof(void*)*1, v___x_544_);
v___x_546_ = l_Repr_addAppParen(v___x_545_, v_prec_511_);
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___boxed(lean_object* v_x_637_, lean_object* v_prec_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr(v_x_637_, v_prec_638_);
lean_dec(v_prec_638_);
lean_dec(v_x_637_);
return v_res_639_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0(void){
_start:
{
uint64_t v___x_642_; uint64_t v___x_643_; uint64_t v___x_644_; 
v___x_642_ = 13ULL;
v___x_643_ = 0ULL;
v___x_644_ = lean_uint64_mix_hash(v___x_643_, v___x_642_);
return v___x_644_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1(void){
_start:
{
uint64_t v___x_645_; uint64_t v___x_646_; uint64_t v___x_647_; 
v___x_645_ = 11ULL;
v___x_646_ = 0ULL;
v___x_647_ = lean_uint64_mix_hash(v___x_646_, v___x_645_);
return v___x_647_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2(void){
_start:
{
uint64_t v___x_648_; uint64_t v___x_649_; uint64_t v___x_650_; 
v___x_648_ = 13ULL;
v___x_649_ = 1ULL;
v___x_650_ = lean_uint64_mix_hash(v___x_649_, v___x_648_);
return v___x_650_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3(void){
_start:
{
uint64_t v___x_651_; uint64_t v___x_652_; uint64_t v___x_653_; 
v___x_651_ = 11ULL;
v___x_652_ = 1ULL;
v___x_653_ = lean_uint64_mix_hash(v___x_652_, v___x_651_);
return v___x_653_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4(void){
_start:
{
uint64_t v___x_654_; uint64_t v___x_655_; uint64_t v___x_656_; 
v___x_654_ = 13ULL;
v___x_655_ = 2ULL;
v___x_656_ = lean_uint64_mix_hash(v___x_655_, v___x_654_);
return v___x_656_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5(void){
_start:
{
uint64_t v___x_657_; uint64_t v___x_658_; uint64_t v___x_659_; 
v___x_657_ = 11ULL;
v___x_658_ = 2ULL;
v___x_659_ = lean_uint64_mix_hash(v___x_658_, v___x_657_);
return v___x_659_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6(void){
_start:
{
uint64_t v___x_660_; uint64_t v___x_661_; uint64_t v___x_662_; 
v___x_660_ = 13ULL;
v___x_661_ = 5ULL;
v___x_662_ = lean_uint64_mix_hash(v___x_661_, v___x_660_);
return v___x_662_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7(void){
_start:
{
uint64_t v___x_663_; uint64_t v___x_664_; uint64_t v___x_665_; 
v___x_663_ = 11ULL;
v___x_664_ = 5ULL;
v___x_665_ = lean_uint64_mix_hash(v___x_664_, v___x_663_);
return v___x_665_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8(void){
_start:
{
uint64_t v___x_666_; uint64_t v___x_667_; uint64_t v___x_668_; 
v___x_666_ = 13ULL;
v___x_667_ = 8ULL;
v___x_668_ = lean_uint64_mix_hash(v___x_667_, v___x_666_);
return v___x_668_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9(void){
_start:
{
uint64_t v___x_669_; uint64_t v___x_670_; uint64_t v___x_671_; 
v___x_669_ = 11ULL;
v___x_670_ = 8ULL;
v___x_671_ = lean_uint64_mix_hash(v___x_670_, v___x_669_);
return v___x_671_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(lean_object* v_x_672_){
_start:
{
switch(lean_obj_tag(v_x_672_))
{
case 0:
{
uint8_t v_gen_673_; 
v_gen_673_ = lean_ctor_get_uint8(v_x_672_, 0);
if (v_gen_673_ == 0)
{
uint64_t v___x_674_; 
v___x_674_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__0);
return v___x_674_;
}
else
{
uint64_t v___x_675_; 
v___x_675_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__1);
return v___x_675_;
}
}
case 1:
{
uint8_t v_gen_676_; 
v_gen_676_ = lean_ctor_get_uint8(v_x_672_, 0);
if (v_gen_676_ == 0)
{
uint64_t v___x_677_; 
v___x_677_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__2);
return v___x_677_;
}
else
{
uint64_t v___x_678_; 
v___x_678_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__3);
return v___x_678_;
}
}
case 2:
{
uint8_t v_gen_679_; 
v_gen_679_ = lean_ctor_get_uint8(v_x_672_, 0);
if (v_gen_679_ == 0)
{
uint64_t v___x_680_; 
v___x_680_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__4);
return v___x_680_;
}
else
{
uint64_t v___x_681_; 
v___x_681_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__5);
return v___x_681_;
}
}
case 3:
{
uint64_t v___x_682_; 
v___x_682_ = 3ULL;
return v___x_682_;
}
case 4:
{
uint64_t v___x_683_; 
v___x_683_ = 4ULL;
return v___x_683_;
}
case 5:
{
uint8_t v_gen_684_; 
v_gen_684_ = lean_ctor_get_uint8(v_x_672_, 0);
if (v_gen_684_ == 0)
{
uint64_t v___x_685_; 
v___x_685_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__6);
return v___x_685_;
}
else
{
uint64_t v___x_686_; 
v___x_686_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__7);
return v___x_686_;
}
}
case 6:
{
uint64_t v___x_687_; 
v___x_687_ = 6ULL;
return v___x_687_;
}
case 7:
{
uint64_t v___x_688_; 
v___x_688_ = 7ULL;
return v___x_688_;
}
case 8:
{
uint8_t v_gen_689_; 
v_gen_689_ = lean_ctor_get_uint8(v_x_672_, 0);
if (v_gen_689_ == 0)
{
uint64_t v___x_690_; 
v___x_690_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__8);
return v___x_690_;
}
else
{
uint64_t v___x_691_; 
v___x_691_ = lean_uint64_once(&l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9, &l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9_once, _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___closed__9);
return v___x_691_;
}
}
default: 
{
uint64_t v___x_692_; 
v___x_692_ = 9ULL;
return v___x_692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___boxed(lean_object* v_x_693_){
_start:
{
uint64_t v_res_694_; lean_object* v_r_695_; 
v_res_694_ = l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(v_x_693_);
lean_dec(v_x_693_);
v_r_695_ = lean_box_uint64(v_res_694_);
return v_r_695_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = lean_box(0);
v___x_704_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__2));
v___x_705_ = l_Lean_Expr_const___override(v___x_704_, v___x_703_);
return v___x_705_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_706_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_709_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___x_707_);
lean_ctor_set(v___x_709_, 2, v___x_706_);
return v___x_709_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default(void){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4);
return v___x_710_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS(void){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default;
return v___x_711_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(lean_object* v_xs_712_, lean_object* v_ys_713_, lean_object* v_x_714_){
_start:
{
lean_object* v_zero_715_; uint8_t v_isZero_716_; 
v_zero_715_ = lean_unsigned_to_nat(0u);
v_isZero_716_ = lean_nat_dec_eq(v_x_714_, v_zero_715_);
if (v_isZero_716_ == 1)
{
lean_dec(v_x_714_);
return v_isZero_716_;
}
else
{
lean_object* v_one_717_; lean_object* v_n_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v_one_717_ = lean_unsigned_to_nat(1u);
v_n_718_ = lean_nat_sub(v_x_714_, v_one_717_);
lean_dec(v_x_714_);
v___x_719_ = lean_array_fget_borrowed(v_xs_712_, v_n_718_);
v___x_720_ = lean_array_fget_borrowed(v_ys_713_, v_n_718_);
v___x_721_ = lean_name_eq(v___x_719_, v___x_720_);
if (v___x_721_ == 0)
{
lean_dec(v_n_718_);
return v___x_721_;
}
else
{
v_x_714_ = v_n_718_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg___boxed(lean_object* v_xs_723_, lean_object* v_ys_724_, lean_object* v_x_725_){
_start:
{
uint8_t v_res_726_; lean_object* v_r_727_; 
v_res_726_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_xs_723_, v_ys_724_, v_x_725_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_xs_723_);
v_r_727_ = lean_box(v_res_726_);
return v_r_727_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqCnstrRHS_beq(lean_object* v_x_728_, lean_object* v_x_729_){
_start:
{
lean_object* v_levelNames_730_; lean_object* v_numMVars_731_; lean_object* v_expr_732_; lean_object* v_levelNames_733_; lean_object* v_numMVars_734_; lean_object* v_expr_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v_levelNames_730_ = lean_ctor_get(v_x_728_, 0);
v_numMVars_731_ = lean_ctor_get(v_x_728_, 1);
v_expr_732_ = lean_ctor_get(v_x_728_, 2);
v_levelNames_733_ = lean_ctor_get(v_x_729_, 0);
v_numMVars_734_ = lean_ctor_get(v_x_729_, 1);
v_expr_735_ = lean_ctor_get(v_x_729_, 2);
v___x_736_ = lean_array_get_size(v_levelNames_730_);
v___x_737_ = lean_array_get_size(v_levelNames_733_);
v___x_738_ = lean_nat_dec_eq(v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
return v___x_738_;
}
else
{
uint8_t v___x_739_; 
v___x_739_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_levelNames_730_, v_levelNames_733_, v___x_736_);
if (v___x_739_ == 0)
{
return v___x_739_;
}
else
{
uint8_t v___x_740_; 
v___x_740_ = lean_nat_dec_eq(v_numMVars_731_, v_numMVars_734_);
if (v___x_740_ == 0)
{
return v___x_740_;
}
else
{
uint8_t v___x_741_; 
v___x_741_ = lean_expr_eqv(v_expr_732_, v_expr_735_);
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqCnstrRHS_beq___boxed(lean_object* v_x_742_, lean_object* v_x_743_){
_start:
{
uint8_t v_res_744_; lean_object* v_r_745_; 
v_res_744_ = l_Lean_Meta_Grind_instBEqCnstrRHS_beq(v_x_742_, v_x_743_);
lean_dec_ref(v_x_743_);
lean_dec_ref(v_x_742_);
v_r_745_ = lean_box(v_res_744_);
return v_r_745_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(lean_object* v_xs_746_, lean_object* v_ys_747_, lean_object* v_hsz_748_, lean_object* v_x_749_, lean_object* v_x_750_){
_start:
{
uint8_t v___x_751_; 
v___x_751_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_xs_746_, v_ys_747_, v_x_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___boxed(lean_object* v_xs_752_, lean_object* v_ys_753_, lean_object* v_hsz_754_, lean_object* v_x_755_, lean_object* v_x_756_){
_start:
{
uint8_t v_res_757_; lean_object* v_r_758_; 
v_res_757_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(v_xs_752_, v_ys_753_, v_hsz_754_, v_x_755_, v_x_756_);
lean_dec_ref(v_ys_753_);
lean_dec_ref(v_xs_752_);
v_r_758_ = lean_box(v_res_757_);
return v_r_758_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__1(lean_object* v_a_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = lean_nat_to_int(v_a_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
if (lean_obj_tag(v_x_765_) == 0)
{
lean_dec(v_x_763_);
return v_x_764_;
}
else
{
lean_object* v_head_766_; lean_object* v_tail_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_778_; 
v_head_766_ = lean_ctor_get(v_x_765_, 0);
v_tail_767_ = lean_ctor_get(v_x_765_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_x_765_);
if (v_isSharedCheck_778_ == 0)
{
v___x_769_ = v_x_765_;
v_isShared_770_ = v_isSharedCheck_778_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_tail_767_);
lean_inc(v_head_766_);
lean_dec(v_x_765_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_778_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
lean_inc(v_x_763_);
if (v_isShared_770_ == 0)
{
lean_ctor_set_tag(v___x_769_, 5);
lean_ctor_set(v___x_769_, 1, v_x_763_);
lean_ctor_set(v___x_769_, 0, v_x_764_);
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_x_764_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_x_763_);
v___x_772_ = v_reuseFailAlloc_777_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = l_Lean_Name_reprPrec(v_head_766_, v___x_773_);
v___x_775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_772_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v_x_764_ = v___x_775_;
v_x_765_ = v_tail_767_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2(lean_object* v_x_779_, lean_object* v_x_780_, lean_object* v_x_781_){
_start:
{
if (lean_obj_tag(v_x_781_) == 0)
{
lean_dec(v_x_779_);
return v_x_780_;
}
else
{
lean_object* v_head_782_; lean_object* v_tail_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_794_; 
v_head_782_ = lean_ctor_get(v_x_781_, 0);
v_tail_783_ = lean_ctor_get(v_x_781_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v_x_781_);
if (v_isSharedCheck_794_ == 0)
{
v___x_785_ = v_x_781_;
v_isShared_786_ = v_isSharedCheck_794_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_tail_783_);
lean_inc(v_head_782_);
lean_dec(v_x_781_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_794_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
lean_inc(v_x_779_);
if (v_isShared_786_ == 0)
{
lean_ctor_set_tag(v___x_785_, 5);
lean_ctor_set(v___x_785_, 1, v_x_779_);
lean_ctor_set(v___x_785_, 0, v_x_780_);
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_x_780_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_x_779_);
v___x_788_ = v_reuseFailAlloc_793_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_789_ = lean_unsigned_to_nat(0u);
v___x_790_ = l_Lean_Name_reprPrec(v_head_782_, v___x_789_);
v___x_791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_788_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2_spec__3(v_x_779_, v___x_791_, v_tail_783_);
return v___x_792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(lean_object* v___y_795_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = l_Lean_Name_reprPrec(v___y_795_, v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0(lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
if (lean_obj_tag(v_x_798_) == 0)
{
lean_object* v___x_800_; 
lean_dec(v_x_799_);
v___x_800_ = lean_box(0);
return v___x_800_;
}
else
{
lean_object* v_tail_801_; 
v_tail_801_ = lean_ctor_get(v_x_798_, 1);
if (lean_obj_tag(v_tail_801_) == 0)
{
lean_object* v_head_802_; lean_object* v___x_803_; 
lean_dec(v_x_799_);
v_head_802_ = lean_ctor_get(v_x_798_, 0);
lean_inc(v_head_802_);
lean_dec_ref_known(v_x_798_, 2);
v___x_803_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(v_head_802_);
return v___x_803_;
}
else
{
lean_object* v_head_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_inc(v_tail_801_);
v_head_804_ = lean_ctor_get(v_x_798_, 0);
lean_inc(v_head_804_);
lean_dec_ref_known(v_x_798_, 2);
v___x_805_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(v_head_804_);
v___x_806_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2(v_x_799_, v___x_805_, v_tail_801_);
return v___x_806_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0));
v___x_816_ = lean_string_length(v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5);
v___x_818_ = lean_nat_to_int(v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0(lean_object* v_xs_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_827_ = lean_array_get_size(v_xs_826_);
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = lean_nat_dec_eq(v___x_827_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_830_ = lean_array_to_list(v_xs_826_);
v___x_831_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__3));
v___x_832_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0(v___x_830_, v___x_831_);
v___x_833_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6);
v___x_834_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__7));
v___x_835_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___x_832_);
v___x_836_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__8));
v___x_837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_833_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = l_Std_Format_fill(v___x_838_);
return v___x_839_;
}
else
{
lean_object* v___x_840_; 
lean_dec_ref(v_xs_826_);
v___x_840_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__10));
return v___x_840_;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_unsigned_to_nat(14u);
v___x_855_ = lean_nat_to_int(v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_unsigned_to_nat(12u);
v___x_860_ = lean_nat_to_int(v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_unsigned_to_nat(8u);
v___x_865_ = lean_nat_to_int(v___x_864_);
return v___x_865_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0));
v___x_868_ = lean_string_length(v___x_867_);
return v___x_868_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15);
v___x_870_ = lean_nat_to_int(v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(lean_object* v_x_875_){
_start:
{
lean_object* v_levelNames_876_; lean_object* v_numMVars_877_; lean_object* v_expr_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v_levelNames_876_ = lean_ctor_get(v_x_875_, 0);
lean_inc_ref(v_levelNames_876_);
v_numMVars_877_ = lean_ctor_get(v_x_875_, 1);
lean_inc(v_numMVars_877_);
v_expr_878_ = lean_ctor_get(v_x_875_, 2);
lean_inc_ref(v_expr_878_);
lean_dec_ref(v_x_875_);
v___x_879_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5));
v___x_880_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__6));
v___x_881_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7);
v___x_882_ = l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0(v_levelNames_876_);
v___x_883_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = 0;
v___x_885_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set_uint8(v___x_885_, sizeof(void*)*1, v___x_884_);
v___x_886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_880_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2));
v___x_888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = lean_box(1);
v___x_890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__9));
v___x_892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v___x_879_);
v___x_894_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10);
v___x_895_ = l_Nat_reprFast(v_numMVars_877_);
v___x_896_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
v___x_897_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_894_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set_uint8(v___x_898_, sizeof(void*)*1, v___x_884_);
v___x_899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_893_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v___x_887_);
v___x_901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___x_889_);
v___x_902_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__12));
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_879_);
v___x_905_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = l_Lean_instReprExpr_repr(v_expr_878_, v___x_906_);
v___x_908_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_905_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set_uint8(v___x_909_, sizeof(void*)*1, v___x_884_);
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_904_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16);
v___x_912_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__17));
v___x_913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set(v___x_913_, 1, v___x_910_);
v___x_914_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__18));
v___x_915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_911_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set_uint8(v___x_917_, sizeof(void*)*1, v___x_884_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr(lean_object* v_x_918_, lean_object* v_prec_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_x_918_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___boxed(lean_object* v_x_921_, lean_object* v_prec_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr(v_x_921_, v_prec_922_);
lean_dec(v_prec_922_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(lean_object* v_x_926_){
_start:
{
switch(lean_obj_tag(v_x_926_))
{
case 0:
{
lean_object* v___x_927_; 
v___x_927_ = lean_unsigned_to_nat(0u);
return v___x_927_;
}
case 1:
{
lean_object* v___x_928_; 
v___x_928_ = lean_unsigned_to_nat(1u);
return v___x_928_;
}
case 2:
{
lean_object* v___x_929_; 
v___x_929_ = lean_unsigned_to_nat(2u);
return v___x_929_;
}
case 3:
{
lean_object* v___x_930_; 
v___x_930_ = lean_unsigned_to_nat(3u);
return v___x_930_;
}
case 4:
{
lean_object* v___x_931_; 
v___x_931_ = lean_unsigned_to_nat(4u);
return v___x_931_;
}
case 5:
{
lean_object* v___x_932_; 
v___x_932_ = lean_unsigned_to_nat(5u);
return v___x_932_;
}
case 6:
{
lean_object* v___x_933_; 
v___x_933_ = lean_unsigned_to_nat(6u);
return v___x_933_;
}
case 7:
{
lean_object* v___x_934_; 
v___x_934_ = lean_unsigned_to_nat(7u);
return v___x_934_;
}
case 8:
{
lean_object* v___x_935_; 
v___x_935_ = lean_unsigned_to_nat(8u);
return v___x_935_;
}
case 9:
{
lean_object* v___x_936_; 
v___x_936_ = lean_unsigned_to_nat(9u);
return v___x_936_;
}
default: 
{
lean_object* v___x_937_; 
v___x_937_ = lean_unsigned_to_nat(10u);
return v___x_937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx___boxed(lean_object* v_x_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_938_);
lean_dec_ref(v_x_938_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(lean_object* v_t_940_, lean_object* v_k_941_){
_start:
{
switch(lean_obj_tag(v_t_940_))
{
case 0:
{
lean_object* v_lhs_942_; lean_object* v_rhs_943_; lean_object* v___x_944_; 
v_lhs_942_ = lean_ctor_get(v_t_940_, 0);
lean_inc(v_lhs_942_);
v_rhs_943_ = lean_ctor_get(v_t_940_, 1);
lean_inc_ref(v_rhs_943_);
lean_dec_ref_known(v_t_940_, 2);
v___x_944_ = lean_apply_2(v_k_941_, v_lhs_942_, v_rhs_943_);
return v___x_944_;
}
case 1:
{
lean_object* v_lhs_945_; lean_object* v_rhs_946_; lean_object* v___x_947_; 
v_lhs_945_ = lean_ctor_get(v_t_940_, 0);
lean_inc(v_lhs_945_);
v_rhs_946_ = lean_ctor_get(v_t_940_, 1);
lean_inc_ref(v_rhs_946_);
lean_dec_ref_known(v_t_940_, 2);
v___x_947_ = lean_apply_2(v_k_941_, v_lhs_945_, v_rhs_946_);
return v___x_947_;
}
case 2:
{
lean_object* v_lhs_948_; lean_object* v_n_949_; lean_object* v___x_950_; 
v_lhs_948_ = lean_ctor_get(v_t_940_, 0);
lean_inc(v_lhs_948_);
v_n_949_ = lean_ctor_get(v_t_940_, 1);
lean_inc(v_n_949_);
lean_dec_ref_known(v_t_940_, 2);
v___x_950_ = lean_apply_2(v_k_941_, v_lhs_948_, v_n_949_);
return v___x_950_;
}
case 3:
{
lean_object* v_lhs_951_; lean_object* v_n_952_; lean_object* v___x_953_; 
v_lhs_951_ = lean_ctor_get(v_t_940_, 0);
lean_inc(v_lhs_951_);
v_n_952_ = lean_ctor_get(v_t_940_, 1);
lean_inc(v_n_952_);
lean_dec_ref_known(v_t_940_, 2);
v___x_953_ = lean_apply_2(v_k_941_, v_lhs_951_, v_n_952_);
return v___x_953_;
}
case 6:
{
lean_object* v_bvarIdx_954_; uint8_t v_strict_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_bvarIdx_954_ = lean_ctor_get(v_t_940_, 0);
lean_inc(v_bvarIdx_954_);
v_strict_955_ = lean_ctor_get_uint8(v_t_940_, sizeof(void*)*1);
lean_dec_ref_known(v_t_940_, 1);
v___x_956_ = lean_box(v_strict_955_);
v___x_957_ = lean_apply_2(v_k_941_, v_bvarIdx_954_, v___x_956_);
return v___x_957_;
}
case 8:
{
lean_object* v_e_958_; lean_object* v___x_959_; 
v_e_958_ = lean_ctor_get(v_t_940_, 0);
lean_inc_ref(v_e_958_);
lean_dec_ref_known(v_t_940_, 1);
v___x_959_ = lean_apply_1(v_k_941_, v_e_958_);
return v___x_959_;
}
case 9:
{
lean_object* v_e_960_; lean_object* v___x_961_; 
v_e_960_ = lean_ctor_get(v_t_940_, 0);
lean_inc_ref(v_e_960_);
lean_dec_ref_known(v_t_940_, 1);
v___x_961_ = lean_apply_1(v_k_941_, v_e_960_);
return v___x_961_;
}
case 10:
{
lean_object* v_bvarIdx_962_; uint8_t v_strict_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_bvarIdx_962_ = lean_ctor_get(v_t_940_, 0);
lean_inc(v_bvarIdx_962_);
v_strict_963_ = lean_ctor_get_uint8(v_t_940_, sizeof(void*)*1);
lean_dec_ref_known(v_t_940_, 1);
v___x_964_ = lean_box(v_strict_963_);
v___x_965_ = lean_apply_2(v_k_941_, v_bvarIdx_962_, v___x_964_);
return v___x_965_;
}
default: 
{
lean_object* v_n_966_; lean_object* v___x_967_; 
v_n_966_ = lean_ctor_get(v_t_940_, 0);
lean_inc(v_n_966_);
lean_dec_ref(v_t_940_);
v___x_967_ = lean_apply_1(v_k_941_, v_n_966_);
return v___x_967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim(lean_object* v_motive_968_, lean_object* v_ctorIdx_969_, lean_object* v_t_970_, lean_object* v_h_971_, lean_object* v_k_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_970_, v_k_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___boxed(lean_object* v_motive_974_, lean_object* v_ctorIdx_975_, lean_object* v_t_976_, lean_object* v_h_977_, lean_object* v_k_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim(v_motive_974_, v_ctorIdx_975_, v_t_976_, v_h_977_, v_k_978_);
lean_dec(v_ctorIdx_975_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim___redArg(lean_object* v_t_980_, lean_object* v_notDefEq_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_980_, v_notDefEq_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim(lean_object* v_motive_983_, lean_object* v_t_984_, lean_object* v_h_985_, lean_object* v_notDefEq_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_984_, v_notDefEq_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim___redArg(lean_object* v_t_988_, lean_object* v_defEq_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_988_, v_defEq_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim(lean_object* v_motive_991_, lean_object* v_t_992_, lean_object* v_h_993_, lean_object* v_defEq_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_992_, v_defEq_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim___redArg(lean_object* v_t_996_, lean_object* v_sizeLt_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_996_, v_sizeLt_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim(lean_object* v_motive_999_, lean_object* v_t_1000_, lean_object* v_h_1001_, lean_object* v_sizeLt_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1000_, v_sizeLt_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim___redArg(lean_object* v_t_1004_, lean_object* v_depthLt_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1004_, v_depthLt_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim(lean_object* v_motive_1007_, lean_object* v_t_1008_, lean_object* v_h_1009_, lean_object* v_depthLt_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1008_, v_depthLt_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim___redArg(lean_object* v_t_1012_, lean_object* v_genLt_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1012_, v_genLt_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim(lean_object* v_motive_1015_, lean_object* v_t_1016_, lean_object* v_h_1017_, lean_object* v_genLt_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1016_, v_genLt_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim___redArg(lean_object* v_t_1020_, lean_object* v_isGround_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1020_, v_isGround_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim(lean_object* v_motive_1023_, lean_object* v_t_1024_, lean_object* v_h_1025_, lean_object* v_isGround_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1024_, v_isGround_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim___redArg(lean_object* v_t_1028_, lean_object* v_isValue_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1028_, v_isValue_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim(lean_object* v_motive_1031_, lean_object* v_t_1032_, lean_object* v_h_1033_, lean_object* v_isValue_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1032_, v_isValue_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim___redArg(lean_object* v_t_1036_, lean_object* v_maxInsts_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1036_, v_maxInsts_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim(lean_object* v_motive_1039_, lean_object* v_t_1040_, lean_object* v_h_1041_, lean_object* v_maxInsts_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1040_, v_maxInsts_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim___redArg(lean_object* v_t_1044_, lean_object* v_guard_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1044_, v_guard_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim(lean_object* v_motive_1047_, lean_object* v_t_1048_, lean_object* v_h_1049_, lean_object* v_guard_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1048_, v_guard_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim___redArg(lean_object* v_t_1052_, lean_object* v_check_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1052_, v_check_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim(lean_object* v_motive_1055_, lean_object* v_t_1056_, lean_object* v_h_1057_, lean_object* v_check_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1056_, v_check_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim___redArg(lean_object* v_t_1060_, lean_object* v_notValue_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1060_, v_notValue_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim(lean_object* v_motive_1063_, lean_object* v_t_1064_, lean_object* v_h_1065_, lean_object* v_notValue_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1064_, v_notValue_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default;
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___x_1068_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default(void){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0, &l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0);
return v___x_1071_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint(void){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default;
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr(lean_object* v_x_1139_, lean_object* v_prec_1140_){
_start:
{
switch(lean_obj_tag(v_x_1139_))
{
case 0:
{
lean_object* v_lhs_1141_; lean_object* v_rhs_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1166_; 
v_lhs_1141_ = lean_ctor_get(v_x_1139_, 0);
v_rhs_1142_ = lean_ctor_get(v_x_1139_, 1);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1144_ = v_x_1139_;
v_isShared_1145_ = v_isSharedCheck_1166_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_rhs_1142_);
lean_inc(v_lhs_1141_);
lean_dec(v_x_1139_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1166_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___y_1147_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = lean_unsigned_to_nat(1024u);
v___x_1163_ = lean_nat_dec_le(v___x_1162_, v_prec_1140_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1147_ = v___x_1164_;
goto v___jp_1146_;
}
else
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1147_ = v___x_1165_;
goto v___jp_1146_;
}
v___jp_1146_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1148_ = lean_box(1);
v___x_1149_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__2));
v___x_1150_ = l_Nat_reprFast(v_lhs_1141_);
v___x_1151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set_tag(v___x_1144_, 5);
lean_ctor_set(v___x_1144_, 1, v___x_1151_);
lean_ctor_set(v___x_1144_, 0, v___x_1149_);
v___x_1153_ = v___x_1144_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v___x_1148_);
v___x_1155_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_rhs_1142_);
v___x_1156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
lean_inc(v___y_1147_);
v___x_1157_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___y_1147_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = 0;
v___x_1159_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set_uint8(v___x_1159_, sizeof(void*)*1, v___x_1158_);
v___x_1160_ = l_Repr_addAppParen(v___x_1159_, v_prec_1140_);
return v___x_1160_;
}
}
}
}
case 1:
{
lean_object* v_lhs_1167_; lean_object* v_rhs_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1192_; 
v_lhs_1167_ = lean_ctor_get(v_x_1139_, 0);
v_rhs_1168_ = lean_ctor_get(v_x_1139_, 1);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1170_ = v_x_1139_;
v_isShared_1171_ = v_isSharedCheck_1192_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_rhs_1168_);
lean_inc(v_lhs_1167_);
lean_dec(v_x_1139_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1192_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___y_1173_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = lean_unsigned_to_nat(1024u);
v___x_1189_ = lean_nat_dec_le(v___x_1188_, v_prec_1140_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1173_ = v___x_1190_;
goto v___jp_1172_;
}
else
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1173_ = v___x_1191_;
goto v___jp_1172_;
}
v___jp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1174_ = lean_box(1);
v___x_1175_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__5));
v___x_1176_ = l_Nat_reprFast(v_lhs_1167_);
v___x_1177_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set_tag(v___x_1170_, 5);
lean_ctor_set(v___x_1170_, 1, v___x_1177_);
lean_ctor_set(v___x_1170_, 0, v___x_1175_);
v___x_1179_ = v___x_1170_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
lean_ctor_set(v___x_1180_, 1, v___x_1174_);
v___x_1181_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_rhs_1168_);
v___x_1182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
lean_inc(v___y_1173_);
v___x_1183_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___y_1173_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = 0;
v___x_1185_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set_uint8(v___x_1185_, sizeof(void*)*1, v___x_1184_);
v___x_1186_ = l_Repr_addAppParen(v___x_1185_, v_prec_1140_);
return v___x_1186_;
}
}
}
}
case 2:
{
lean_object* v_lhs_1193_; lean_object* v_n_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1219_; 
v_lhs_1193_ = lean_ctor_get(v_x_1139_, 0);
v_n_1194_ = lean_ctor_get(v_x_1139_, 1);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1196_ = v_x_1139_;
v_isShared_1197_ = v_isSharedCheck_1219_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_n_1194_);
lean_inc(v_lhs_1193_);
lean_dec(v_x_1139_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1219_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___y_1199_; lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = lean_unsigned_to_nat(1024u);
v___x_1216_ = lean_nat_dec_le(v___x_1215_, v_prec_1140_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1199_ = v___x_1217_;
goto v___jp_1198_;
}
else
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1199_ = v___x_1218_;
goto v___jp_1198_;
}
v___jp_1198_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1200_ = lean_box(1);
v___x_1201_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__8));
v___x_1202_ = l_Nat_reprFast(v_lhs_1193_);
v___x_1203_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set_tag(v___x_1196_, 5);
lean_ctor_set(v___x_1196_, 1, v___x_1203_);
lean_ctor_set(v___x_1196_, 0, v___x_1201_);
v___x_1205_ = v___x_1196_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v___x_1200_);
v___x_1207_ = l_Nat_reprFast(v_n_1194_);
v___x_1208_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1206_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
lean_inc(v___y_1199_);
v___x_1210_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___y_1199_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
v___x_1211_ = 0;
v___x_1212_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set_uint8(v___x_1212_, sizeof(void*)*1, v___x_1211_);
v___x_1213_ = l_Repr_addAppParen(v___x_1212_, v_prec_1140_);
return v___x_1213_;
}
}
}
}
case 3:
{
lean_object* v_lhs_1220_; lean_object* v_n_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1246_; 
v_lhs_1220_ = lean_ctor_get(v_x_1139_, 0);
v_n_1221_ = lean_ctor_get(v_x_1139_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1223_ = v_x_1139_;
v_isShared_1224_ = v_isSharedCheck_1246_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_n_1221_);
lean_inc(v_lhs_1220_);
lean_dec(v_x_1139_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1246_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___y_1226_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1242_ = lean_unsigned_to_nat(1024u);
v___x_1243_ = lean_nat_dec_le(v___x_1242_, v_prec_1140_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1226_ = v___x_1244_;
goto v___jp_1225_;
}
else
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1226_ = v___x_1245_;
goto v___jp_1225_;
}
v___jp_1225_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1227_ = lean_box(1);
v___x_1228_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__11));
v___x_1229_ = l_Nat_reprFast(v_lhs_1220_);
v___x_1230_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set_tag(v___x_1223_, 5);
lean_ctor_set(v___x_1223_, 1, v___x_1230_);
lean_ctor_set(v___x_1223_, 0, v___x_1228_);
v___x_1232_ = v___x_1223_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
lean_ctor_set(v___x_1233_, 1, v___x_1227_);
v___x_1234_ = l_Nat_reprFast(v_n_1221_);
v___x_1235_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
v___x_1236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1233_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
lean_inc(v___y_1226_);
v___x_1237_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___y_1226_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = 0;
v___x_1239_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set_uint8(v___x_1239_, sizeof(void*)*1, v___x_1238_);
v___x_1240_ = l_Repr_addAppParen(v___x_1239_, v_prec_1140_);
return v___x_1240_;
}
}
}
}
case 4:
{
lean_object* v_n_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1267_; 
v_n_1247_ = lean_ctor_get(v_x_1139_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1249_ = v_x_1139_;
v_isShared_1250_ = v_isSharedCheck_1267_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_n_1247_);
lean_dec(v_x_1139_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1267_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___y_1252_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = lean_unsigned_to_nat(1024u);
v___x_1264_ = lean_nat_dec_le(v___x_1263_, v_prec_1140_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; 
v___x_1265_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1252_ = v___x_1265_;
goto v___jp_1251_;
}
else
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1252_ = v___x_1266_;
goto v___jp_1251_;
}
v___jp_1251_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1253_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__14));
v___x_1254_ = l_Nat_reprFast(v_n_1247_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set_tag(v___x_1249_, 3);
lean_ctor_set(v___x_1249_, 0, v___x_1254_);
v___x_1256_ = v___x_1249_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1253_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
lean_inc(v___y_1252_);
v___x_1258_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___y_1252_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = 0;
v___x_1260_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set_uint8(v___x_1260_, sizeof(void*)*1, v___x_1259_);
v___x_1261_ = l_Repr_addAppParen(v___x_1260_, v_prec_1140_);
return v___x_1261_;
}
}
}
}
case 5:
{
lean_object* v_bvarIdx_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1288_; 
v_bvarIdx_1268_ = lean_ctor_get(v_x_1139_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1270_ = v_x_1139_;
v_isShared_1271_ = v_isSharedCheck_1288_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_bvarIdx_1268_);
lean_dec(v_x_1139_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1288_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___y_1273_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = lean_unsigned_to_nat(1024u);
v___x_1285_ = lean_nat_dec_le(v___x_1284_, v_prec_1140_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1273_ = v___x_1286_;
goto v___jp_1272_;
}
else
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1273_ = v___x_1287_;
goto v___jp_1272_;
}
v___jp_1272_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1274_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__17));
v___x_1275_ = l_Nat_reprFast(v_bvarIdx_1268_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set_tag(v___x_1270_, 3);
lean_ctor_set(v___x_1270_, 0, v___x_1275_);
v___x_1277_ = v___x_1270_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1274_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
lean_inc(v___y_1273_);
v___x_1279_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___y_1273_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = 0;
v___x_1281_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*1, v___x_1280_);
v___x_1282_ = l_Repr_addAppParen(v___x_1281_, v_prec_1140_);
return v___x_1282_;
}
}
}
}
case 6:
{
lean_object* v_bvarIdx_1289_; uint8_t v_strict_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1314_; 
v_bvarIdx_1289_ = lean_ctor_get(v_x_1139_, 0);
v_strict_1290_ = lean_ctor_get_uint8(v_x_1139_, sizeof(void*)*1);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1292_ = v_x_1139_;
v_isShared_1293_ = v_isSharedCheck_1314_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_bvarIdx_1289_);
lean_dec(v_x_1139_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1314_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___y_1295_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = lean_unsigned_to_nat(1024u);
v___x_1311_ = lean_nat_dec_le(v___x_1310_, v_prec_1140_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1295_ = v___x_1312_;
goto v___jp_1294_;
}
else
{
lean_object* v___x_1313_; 
v___x_1313_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1295_ = v___x_1313_;
goto v___jp_1294_;
}
v___jp_1294_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; lean_object* v___x_1307_; 
v___x_1296_ = lean_box(1);
v___x_1297_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__20));
v___x_1298_ = l_Nat_reprFast(v_bvarIdx_1289_);
v___x_1299_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
v___x_1300_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1297_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v___x_1296_);
v___x_1302_ = l_Bool_repr___redArg(v_strict_1290_);
v___x_1303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1301_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
lean_inc(v___y_1295_);
v___x_1304_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___y_1295_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = 0;
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___x_1304_);
v___x_1307_ = v___x_1292_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1304_);
v___x_1307_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1308_; 
lean_ctor_set_uint8(v___x_1307_, sizeof(void*)*1, v___x_1305_);
v___x_1308_ = l_Repr_addAppParen(v___x_1307_, v_prec_1140_);
return v___x_1308_;
}
}
}
}
case 7:
{
lean_object* v_n_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1335_; 
v_n_1315_ = lean_ctor_get(v_x_1139_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1317_ = v_x_1139_;
v_isShared_1318_ = v_isSharedCheck_1335_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_n_1315_);
lean_dec(v_x_1139_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1335_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___y_1320_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1331_ = lean_unsigned_to_nat(1024u);
v___x_1332_ = lean_nat_dec_le(v___x_1331_, v_prec_1140_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1320_ = v___x_1333_;
goto v___jp_1319_;
}
else
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1320_ = v___x_1334_;
goto v___jp_1319_;
}
v___jp_1319_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1321_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__23));
v___x_1322_ = l_Nat_reprFast(v_n_1315_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set_tag(v___x_1317_, 3);
lean_ctor_set(v___x_1317_, 0, v___x_1322_);
v___x_1324_ = v___x_1317_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1321_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
lean_inc(v___y_1320_);
v___x_1326_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___y_1320_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
v___x_1327_ = 0;
v___x_1328_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
lean_ctor_set_uint8(v___x_1328_, sizeof(void*)*1, v___x_1327_);
v___x_1329_ = l_Repr_addAppParen(v___x_1328_, v_prec_1140_);
return v___x_1329_;
}
}
}
}
case 8:
{
lean_object* v_e_1336_; lean_object* v___y_1338_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_e_1336_ = lean_ctor_get(v_x_1139_, 0);
lean_inc_ref(v_e_1336_);
lean_dec_ref_known(v_x_1139_, 1);
v___x_1347_ = lean_unsigned_to_nat(1024u);
v___x_1348_ = lean_nat_dec_le(v___x_1347_, v_prec_1140_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1338_ = v___x_1349_;
goto v___jp_1337_;
}
else
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1338_ = v___x_1350_;
goto v___jp_1337_;
}
v___jp_1337_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1339_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__26));
v___x_1340_ = lean_unsigned_to_nat(1024u);
v___x_1341_ = l_Lean_instReprExpr_repr(v_e_1336_, v___x_1340_);
v___x_1342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1339_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
lean_inc(v___y_1338_);
v___x_1343_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___y_1338_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
v___x_1344_ = 0;
v___x_1345_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1345_, 0, v___x_1343_);
lean_ctor_set_uint8(v___x_1345_, sizeof(void*)*1, v___x_1344_);
v___x_1346_ = l_Repr_addAppParen(v___x_1345_, v_prec_1140_);
return v___x_1346_;
}
}
case 9:
{
lean_object* v_e_1351_; lean_object* v___y_1353_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v_e_1351_ = lean_ctor_get(v_x_1139_, 0);
lean_inc_ref(v_e_1351_);
lean_dec_ref_known(v_x_1139_, 1);
v___x_1362_ = lean_unsigned_to_nat(1024u);
v___x_1363_ = lean_nat_dec_le(v___x_1362_, v_prec_1140_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1353_ = v___x_1364_;
goto v___jp_1352_;
}
else
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1353_ = v___x_1365_;
goto v___jp_1352_;
}
v___jp_1352_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1354_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__29));
v___x_1355_ = lean_unsigned_to_nat(1024u);
v___x_1356_ = l_Lean_instReprExpr_repr(v_e_1351_, v___x_1355_);
v___x_1357_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1354_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
lean_inc(v___y_1353_);
v___x_1358_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___y_1353_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = 0;
v___x_1360_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*1, v___x_1359_);
v___x_1361_ = l_Repr_addAppParen(v___x_1360_, v_prec_1140_);
return v___x_1361_;
}
}
default: 
{
lean_object* v_bvarIdx_1366_; uint8_t v_strict_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1391_; 
v_bvarIdx_1366_ = lean_ctor_get(v_x_1139_, 0);
v_strict_1367_ = lean_ctor_get_uint8(v_x_1139_, sizeof(void*)*1);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1369_ = v_x_1139_;
v_isShared_1370_ = v_isSharedCheck_1391_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_bvarIdx_1366_);
lean_dec(v_x_1139_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1391_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___y_1372_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1387_ = lean_unsigned_to_nat(1024u);
v___x_1388_ = lean_nat_dec_le(v___x_1387_, v_prec_1140_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1372_ = v___x_1389_;
goto v___jp_1371_;
}
else
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1372_ = v___x_1390_;
goto v___jp_1371_;
}
v___jp_1371_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; lean_object* v___x_1384_; 
v___x_1373_ = lean_box(1);
v___x_1374_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__32));
v___x_1375_ = l_Nat_reprFast(v_bvarIdx_1366_);
v___x_1376_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
v___x_1377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1374_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
lean_ctor_set(v___x_1378_, 1, v___x_1373_);
v___x_1379_ = l_Bool_repr___redArg(v_strict_1367_);
v___x_1380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1378_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
lean_inc(v___y_1372_);
v___x_1381_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___y_1372_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = 0;
if (v_isShared_1370_ == 0)
{
lean_ctor_set_tag(v___x_1369_, 6);
lean_ctor_set(v___x_1369_, 0, v___x_1381_);
v___x_1384_ = v___x_1369_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1381_);
v___x_1384_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; 
lean_ctor_set_uint8(v___x_1384_, sizeof(void*)*1, v___x_1382_);
v___x_1385_ = l_Repr_addAppParen(v___x_1384_, v_prec_1140_);
return v___x_1385_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___boxed(lean_object* v_x_1392_, lean_object* v_prec_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr(v_x_1392_, v_prec_1393_);
lean_dec(v_prec_1393_);
return v_res_1394_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(lean_object* v_x_1397_, lean_object* v_x_1398_){
_start:
{
lean_object* v_lhs_1400_; lean_object* v_rhs_1401_; lean_object* v_lhs_x27_1402_; lean_object* v_rhs_x27_1403_; lean_object* v_lhs_1407_; lean_object* v_n_1408_; lean_object* v_lhs_x27_1409_; lean_object* v_n_x27_1410_; lean_object* v_bvarIdx_1414_; uint8_t v_strict_1415_; lean_object* v_bvarIdx_x27_1416_; uint8_t v_strict_x27_1417_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v_decide_1421_; 
v___x_1419_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_1397_);
v___x_1420_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_1398_);
v_decide_1421_ = lean_nat_dec_eq(v___x_1419_, v___x_1420_);
lean_dec(v___x_1420_);
lean_dec(v___x_1419_);
if (v_decide_1421_ == 0)
{
return v_decide_1421_;
}
else
{
switch(lean_obj_tag(v_x_1397_))
{
case 0:
{
lean_object* v_lhs_1422_; lean_object* v_rhs_1423_; lean_object* v_lhs_1424_; lean_object* v_rhs_1425_; 
v_lhs_1422_ = lean_ctor_get(v_x_1397_, 0);
v_rhs_1423_ = lean_ctor_get(v_x_1397_, 1);
v_lhs_1424_ = lean_ctor_get(v_x_1398_, 0);
v_rhs_1425_ = lean_ctor_get(v_x_1398_, 1);
v_lhs_1400_ = v_lhs_1422_;
v_rhs_1401_ = v_rhs_1423_;
v_lhs_x27_1402_ = v_lhs_1424_;
v_rhs_x27_1403_ = v_rhs_1425_;
goto v___jp_1399_;
}
case 1:
{
lean_object* v_lhs_1426_; lean_object* v_rhs_1427_; lean_object* v_lhs_1428_; lean_object* v_rhs_1429_; 
v_lhs_1426_ = lean_ctor_get(v_x_1397_, 0);
v_rhs_1427_ = lean_ctor_get(v_x_1397_, 1);
v_lhs_1428_ = lean_ctor_get(v_x_1398_, 0);
v_rhs_1429_ = lean_ctor_get(v_x_1398_, 1);
v_lhs_1400_ = v_lhs_1426_;
v_rhs_1401_ = v_rhs_1427_;
v_lhs_x27_1402_ = v_lhs_1428_;
v_rhs_x27_1403_ = v_rhs_1429_;
goto v___jp_1399_;
}
case 2:
{
lean_object* v_lhs_1430_; lean_object* v_n_1431_; lean_object* v_lhs_1432_; lean_object* v_n_1433_; 
v_lhs_1430_ = lean_ctor_get(v_x_1397_, 0);
v_n_1431_ = lean_ctor_get(v_x_1397_, 1);
v_lhs_1432_ = lean_ctor_get(v_x_1398_, 0);
v_n_1433_ = lean_ctor_get(v_x_1398_, 1);
v_lhs_1407_ = v_lhs_1430_;
v_n_1408_ = v_n_1431_;
v_lhs_x27_1409_ = v_lhs_1432_;
v_n_x27_1410_ = v_n_1433_;
goto v___jp_1406_;
}
case 3:
{
lean_object* v_lhs_1434_; lean_object* v_n_1435_; lean_object* v_lhs_1436_; lean_object* v_n_1437_; 
v_lhs_1434_ = lean_ctor_get(v_x_1397_, 0);
v_n_1435_ = lean_ctor_get(v_x_1397_, 1);
v_lhs_1436_ = lean_ctor_get(v_x_1398_, 0);
v_n_1437_ = lean_ctor_get(v_x_1398_, 1);
v_lhs_1407_ = v_lhs_1434_;
v_n_1408_ = v_n_1435_;
v_lhs_x27_1409_ = v_lhs_1436_;
v_n_x27_1410_ = v_n_1437_;
goto v___jp_1406_;
}
case 6:
{
lean_object* v_bvarIdx_1438_; uint8_t v_strict_1439_; lean_object* v_bvarIdx_1440_; uint8_t v_strict_1441_; 
v_bvarIdx_1438_ = lean_ctor_get(v_x_1397_, 0);
v_strict_1439_ = lean_ctor_get_uint8(v_x_1397_, sizeof(void*)*1);
v_bvarIdx_1440_ = lean_ctor_get(v_x_1398_, 0);
v_strict_1441_ = lean_ctor_get_uint8(v_x_1398_, sizeof(void*)*1);
v_bvarIdx_1414_ = v_bvarIdx_1438_;
v_strict_1415_ = v_strict_1439_;
v_bvarIdx_x27_1416_ = v_bvarIdx_1440_;
v_strict_x27_1417_ = v_strict_1441_;
goto v___jp_1413_;
}
case 8:
{
lean_object* v_e_1442_; lean_object* v_e_1443_; uint8_t v___x_1444_; 
v_e_1442_ = lean_ctor_get(v_x_1397_, 0);
v_e_1443_ = lean_ctor_get(v_x_1398_, 0);
v___x_1444_ = lean_expr_eqv(v_e_1442_, v_e_1443_);
return v___x_1444_;
}
case 9:
{
lean_object* v_e_1445_; lean_object* v_e_1446_; uint8_t v___x_1447_; 
v_e_1445_ = lean_ctor_get(v_x_1397_, 0);
v_e_1446_ = lean_ctor_get(v_x_1398_, 0);
v___x_1447_ = lean_expr_eqv(v_e_1445_, v_e_1446_);
return v___x_1447_;
}
case 10:
{
lean_object* v_bvarIdx_1448_; uint8_t v_strict_1449_; lean_object* v_bvarIdx_1450_; uint8_t v_strict_1451_; 
v_bvarIdx_1448_ = lean_ctor_get(v_x_1397_, 0);
v_strict_1449_ = lean_ctor_get_uint8(v_x_1397_, sizeof(void*)*1);
v_bvarIdx_1450_ = lean_ctor_get(v_x_1398_, 0);
v_strict_1451_ = lean_ctor_get_uint8(v_x_1398_, sizeof(void*)*1);
v_bvarIdx_1414_ = v_bvarIdx_1448_;
v_strict_1415_ = v_strict_1449_;
v_bvarIdx_x27_1416_ = v_bvarIdx_1450_;
v_strict_x27_1417_ = v_strict_1451_;
goto v___jp_1413_;
}
default: 
{
lean_object* v_n_1452_; lean_object* v_n_1453_; uint8_t v___x_1454_; 
v_n_1452_ = lean_ctor_get(v_x_1397_, 0);
v_n_1453_ = lean_ctor_get(v_x_1398_, 0);
v___x_1454_ = lean_nat_dec_eq(v_n_1452_, v_n_1453_);
return v___x_1454_;
}
}
}
v___jp_1399_:
{
uint8_t v___x_1404_; 
v___x_1404_ = lean_nat_dec_eq(v_lhs_1400_, v_lhs_x27_1402_);
if (v___x_1404_ == 0)
{
return v___x_1404_;
}
else
{
uint8_t v___x_1405_; 
v___x_1405_ = l_Lean_Meta_Grind_instBEqCnstrRHS_beq(v_rhs_1401_, v_rhs_x27_1403_);
return v___x_1405_;
}
}
v___jp_1406_:
{
uint8_t v___x_1411_; 
v___x_1411_ = lean_nat_dec_eq(v_lhs_1407_, v_lhs_x27_1409_);
if (v___x_1411_ == 0)
{
return v___x_1411_;
}
else
{
uint8_t v___x_1412_; 
v___x_1412_ = lean_nat_dec_eq(v_n_1408_, v_n_x27_1410_);
return v___x_1412_;
}
}
v___jp_1413_:
{
uint8_t v___x_1418_; 
v___x_1418_ = lean_nat_dec_eq(v_bvarIdx_1414_, v_bvarIdx_x27_1416_);
if (v___x_1418_ == 0)
{
return v___x_1418_;
}
else
{
if (v_strict_x27_1417_ == 0)
{
if (v_strict_1415_ == 0)
{
return v___x_1418_;
}
else
{
return v_strict_x27_1417_;
}
}
else
{
return v_strict_1415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq___boxed(lean_object* v_x_1455_, lean_object* v_x_1456_){
_start:
{
uint8_t v_res_1457_; lean_object* v_r_1458_; 
v_res_1457_ = l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(v_x_1455_, v_x_1456_);
lean_dec_ref(v_x_1456_);
lean_dec_ref(v_x_1455_);
v_r_1458_ = lean_box(v_res_1457_);
return v_r_1458_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0(void){
_start:
{
uint8_t v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1461_ = 0;
v___x_1462_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default));
v___x_1463_ = l_Lean_Meta_Grind_instInhabitedOrigin_default;
v___x_1464_ = lean_box(0);
v___x_1465_ = lean_unsigned_to_nat(0u);
v___x_1466_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_1467_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_1468_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
lean_ctor_set(v___x_1468_, 1, v___x_1466_);
lean_ctor_set(v___x_1468_, 2, v___x_1465_);
lean_ctor_set(v___x_1468_, 3, v___x_1464_);
lean_ctor_set(v___x_1468_, 4, v___x_1464_);
lean_ctor_set(v___x_1468_, 5, v___x_1463_);
lean_ctor_set(v___x_1468_, 6, v___x_1462_);
lean_ctor_set(v___x_1468_, 7, v___x_1464_);
lean_ctor_set_uint8(v___x_1468_, sizeof(void*)*8, v___x_1461_);
return v___x_1468_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default(void){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0, &l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0);
return v___x_1469_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem(void){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default;
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0(lean_object* v_thm_1471_){
_start:
{
lean_object* v_symbols_1472_; 
v_symbols_1472_ = lean_ctor_get(v_thm_1471_, 4);
lean_inc(v_symbols_1472_);
return v_symbols_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0___boxed(lean_object* v_thm_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0(v_thm_1473_);
lean_dec_ref(v_thm_1473_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__1(lean_object* v_thm_1475_, lean_object* v_symbols_1476_){
_start:
{
lean_object* v_levelParams_1477_; lean_object* v_proof_1478_; lean_object* v_numParams_1479_; lean_object* v_patterns_1480_; lean_object* v_origin_1481_; lean_object* v_kind_1482_; uint8_t v_minIndexable_1483_; lean_object* v_cnstrs_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
v_levelParams_1477_ = lean_ctor_get(v_thm_1475_, 0);
v_proof_1478_ = lean_ctor_get(v_thm_1475_, 1);
v_numParams_1479_ = lean_ctor_get(v_thm_1475_, 2);
v_patterns_1480_ = lean_ctor_get(v_thm_1475_, 3);
v_origin_1481_ = lean_ctor_get(v_thm_1475_, 5);
v_kind_1482_ = lean_ctor_get(v_thm_1475_, 6);
v_minIndexable_1483_ = lean_ctor_get_uint8(v_thm_1475_, sizeof(void*)*8);
v_cnstrs_1484_ = lean_ctor_get(v_thm_1475_, 7);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_thm_1475_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; 
v_unused_1492_ = lean_ctor_get(v_thm_1475_, 4);
lean_dec(v_unused_1492_);
v___x_1486_ = v_thm_1475_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_cnstrs_1484_);
lean_inc(v_kind_1482_);
lean_inc(v_origin_1481_);
lean_inc(v_patterns_1480_);
lean_inc(v_numParams_1479_);
lean_inc(v_proof_1478_);
lean_inc(v_levelParams_1477_);
lean_dec(v_thm_1475_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v_symbols_1476_);
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_levelParams_1477_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_proof_1478_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_numParams_1479_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_patterns_1480_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_symbols_1476_);
lean_ctor_set(v_reuseFailAlloc_1490_, 5, v_origin_1481_);
lean_ctor_set(v_reuseFailAlloc_1490_, 6, v_kind_1482_);
lean_ctor_set(v_reuseFailAlloc_1490_, 7, v_cnstrs_1484_);
lean_ctor_set_uint8(v_reuseFailAlloc_1490_, sizeof(void*)*8, v_minIndexable_1483_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2(lean_object* v_thm_1493_){
_start:
{
lean_object* v_origin_1494_; 
v_origin_1494_ = lean_ctor_get(v_thm_1493_, 5);
lean_inc_ref(v_origin_1494_);
return v_origin_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2___boxed(lean_object* v_thm_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2(v_thm_1495_);
lean_dec_ref(v_thm_1495_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3(lean_object* v_thm_1497_){
_start:
{
lean_object* v_proof_1498_; 
v_proof_1498_ = lean_ctor_get(v_thm_1497_, 1);
lean_inc_ref(v_proof_1498_);
return v_proof_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3___boxed(lean_object* v_thm_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3(v_thm_1499_);
lean_dec_ref(v_thm_1499_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4(lean_object* v_thm_1501_){
_start:
{
lean_object* v_levelParams_1502_; 
v_levelParams_1502_ = lean_ctor_get(v_thm_1501_, 0);
lean_inc_ref(v_levelParams_1502_);
return v_levelParams_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4___boxed(lean_object* v_thm_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4(v_thm_1503_);
lean_dec_ref(v_thm_1503_);
return v_res_1504_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1517_ = l_Lean_Meta_Grind_instInhabitedOrigin_default;
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_1520_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_1521_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
lean_ctor_set(v___x_1521_, 1, v___x_1519_);
lean_ctor_set(v___x_1521_, 2, v___x_1518_);
lean_ctor_set(v___x_1521_, 3, v___x_1517_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default(void){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0, &l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0);
return v___x_1522_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem(void){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default;
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0(lean_object* v_thm_1524_){
_start:
{
lean_object* v_symbols_1525_; 
v_symbols_1525_ = lean_ctor_get(v_thm_1524_, 2);
lean_inc(v_symbols_1525_);
return v_symbols_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0___boxed(lean_object* v_thm_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0(v_thm_1526_);
lean_dec_ref(v_thm_1526_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__1(lean_object* v_thm_1528_, lean_object* v_symbols_1529_){
_start:
{
lean_object* v_levelParams_1530_; lean_object* v_proof_1531_; lean_object* v_origin_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
v_levelParams_1530_ = lean_ctor_get(v_thm_1528_, 0);
v_proof_1531_ = lean_ctor_get(v_thm_1528_, 1);
v_origin_1532_ = lean_ctor_get(v_thm_1528_, 3);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_thm_1528_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; 
v_unused_1540_ = lean_ctor_get(v_thm_1528_, 2);
lean_dec(v_unused_1540_);
v___x_1534_ = v_thm_1528_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_origin_1532_);
lean_inc(v_proof_1531_);
lean_inc(v_levelParams_1530_);
lean_dec(v_thm_1528_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 2, v_symbols_1529_);
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_levelParams_1530_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_proof_1531_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_symbols_1529_);
lean_ctor_set(v_reuseFailAlloc_1538_, 3, v_origin_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2(lean_object* v_thm_1541_){
_start:
{
lean_object* v_origin_1542_; 
v_origin_1542_ = lean_ctor_get(v_thm_1541_, 3);
lean_inc_ref(v_origin_1542_);
return v_origin_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2___boxed(lean_object* v_thm_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2(v_thm_1543_);
lean_dec_ref(v_thm_1543_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3(lean_object* v_thm_1545_){
_start:
{
lean_object* v_proof_1546_; 
v_proof_1546_ = lean_ctor_get(v_thm_1545_, 1);
lean_inc_ref(v_proof_1546_);
return v_proof_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3___boxed(lean_object* v_thm_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3(v_thm_1547_);
lean_dec_ref(v_thm_1547_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4(lean_object* v_thm_1549_){
_start:
{
lean_object* v_levelParams_1550_; 
v_levelParams_1550_ = lean_ctor_get(v_thm_1549_, 0);
lean_inc_ref(v_levelParams_1550_);
return v_levelParams_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4___boxed(lean_object* v_thm_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4(v_thm_1551_);
lean_dec_ref(v_thm_1551_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorIdx(lean_object* v_x_1565_){
_start:
{
switch(lean_obj_tag(v_x_1565_))
{
case 0:
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_unsigned_to_nat(0u);
return v___x_1566_;
}
case 1:
{
lean_object* v___x_1567_; 
v___x_1567_ = lean_unsigned_to_nat(1u);
return v___x_1567_;
}
case 2:
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_unsigned_to_nat(2u);
return v___x_1568_;
}
case 3:
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_unsigned_to_nat(3u);
return v___x_1569_;
}
default: 
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_unsigned_to_nat(4u);
return v___x_1570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorIdx___boxed(lean_object* v_x_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Meta_Grind_Entry_ctorIdx(v_x_1571_);
lean_dec_ref(v_x_1571_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim___redArg(lean_object* v_t_1573_, lean_object* v_k_1574_){
_start:
{
switch(lean_obj_tag(v_t_1573_))
{
case 2:
{
lean_object* v_declName_1575_; uint8_t v_eager_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v_declName_1575_ = lean_ctor_get(v_t_1573_, 0);
lean_inc(v_declName_1575_);
v_eager_1576_ = lean_ctor_get_uint8(v_t_1573_, sizeof(void*)*1);
lean_dec_ref_known(v_t_1573_, 1);
v___x_1577_ = lean_box(v_eager_1576_);
v___x_1578_ = lean_apply_2(v_k_1574_, v_declName_1575_, v___x_1577_);
return v___x_1578_;
}
case 3:
{
lean_object* v_thm_1579_; lean_object* v___x_1580_; 
v_thm_1579_ = lean_ctor_get(v_t_1573_, 0);
lean_inc_ref(v_thm_1579_);
lean_dec_ref_known(v_t_1573_, 1);
v___x_1580_ = lean_apply_1(v_k_1574_, v_thm_1579_);
return v___x_1580_;
}
case 4:
{
lean_object* v_thm_1581_; lean_object* v___x_1582_; 
v_thm_1581_ = lean_ctor_get(v_t_1573_, 0);
lean_inc_ref(v_thm_1581_);
lean_dec_ref_known(v_t_1573_, 1);
v___x_1582_ = lean_apply_1(v_k_1574_, v_thm_1581_);
return v___x_1582_;
}
default: 
{
lean_object* v_declName_1583_; lean_object* v___x_1584_; 
v_declName_1583_ = lean_ctor_get(v_t_1573_, 0);
lean_inc(v_declName_1583_);
lean_dec_ref(v_t_1573_);
v___x_1584_ = lean_apply_1(v_k_1574_, v_declName_1583_);
return v___x_1584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim(lean_object* v_motive_1585_, lean_object* v_ctorIdx_1586_, lean_object* v_t_1587_, lean_object* v_h_1588_, lean_object* v_k_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1587_, v_k_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim___boxed(lean_object* v_motive_1591_, lean_object* v_ctorIdx_1592_, lean_object* v_t_1593_, lean_object* v_h_1594_, lean_object* v_k_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_Meta_Grind_Entry_ctorElim(v_motive_1591_, v_ctorIdx_1592_, v_t_1593_, v_h_1594_, v_k_1595_);
lean_dec(v_ctorIdx_1592_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ext_elim___redArg(lean_object* v_t_1597_, lean_object* v_ext_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1597_, v_ext_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ext_elim(lean_object* v_motive_1600_, lean_object* v_t_1601_, lean_object* v_h_1602_, lean_object* v_ext_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1601_, v_ext_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_funCC_elim___redArg(lean_object* v_t_1605_, lean_object* v_funCC_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1605_, v_funCC_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_funCC_elim(lean_object* v_motive_1608_, lean_object* v_t_1609_, lean_object* v_h_1610_, lean_object* v_funCC_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1609_, v_funCC_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_cases_elim___redArg(lean_object* v_t_1613_, lean_object* v_cases_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1613_, v_cases_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_cases_elim(lean_object* v_motive_1616_, lean_object* v_t_1617_, lean_object* v_h_1618_, lean_object* v_cases_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1617_, v_cases_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ematch_elim___redArg(lean_object* v_t_1621_, lean_object* v_ematch_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1621_, v_ematch_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ematch_elim(lean_object* v_motive_1624_, lean_object* v_t_1625_, lean_object* v_h_1626_, lean_object* v_ematch_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1625_, v_ematch_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_inj_elim___redArg(lean_object* v_t_1629_, lean_object* v_inj_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1629_, v_inj_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_inj_elim(lean_object* v_motive_1632_, lean_object* v_t_1633_, lean_object* v_h_1634_, lean_object* v_inj_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1633_, v_inj_1635_);
return v___x_1636_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0, &l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0);
v___x_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg(){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___closed__0);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___boxed(lean_object* v___dummy_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg();
return v_res_1646_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg();
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0(lean_object* v_00_u03b2_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
return v___x_1650_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1651_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0);
v___x_1652_ = l_Lean_NameSet_empty;
v___x_1653_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0);
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
v___x_1656_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1695_, size_t v_x_1696_, size_t v_x_1697_, lean_object* v_x_1698_, lean_object* v_x_1699_){
_start:
{
if (lean_obj_tag(v_x_1695_) == 0)
{
lean_object* v_es_1700_; size_t v___x_1701_; size_t v___x_1702_; lean_object* v_j_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v_es_1700_ = lean_ctor_get(v_x_1695_, 0);
v___x_1701_ = ((size_t)31ULL);
v___x_1702_ = lean_usize_land(v_x_1696_, v___x_1701_);
v_j_1703_ = lean_usize_to_nat(v___x_1702_);
v___x_1704_ = lean_array_get_size(v_es_1700_);
v___x_1705_ = lean_nat_dec_lt(v_j_1703_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_dec(v_j_1703_);
lean_dec(v_x_1699_);
lean_dec_ref(v_x_1698_);
return v_x_1695_;
}
else
{
lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1746_; 
lean_inc_ref(v_es_1700_);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_x_1695_);
if (v_isSharedCheck_1746_ == 0)
{
lean_object* v_unused_1747_; 
v_unused_1747_ = lean_ctor_get(v_x_1695_, 0);
lean_dec(v_unused_1747_);
v___x_1707_ = v_x_1695_;
v_isShared_1708_ = v_isSharedCheck_1746_;
goto v_resetjp_1706_;
}
else
{
lean_dec(v_x_1695_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1746_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_v_1709_; lean_object* v___x_1710_; lean_object* v_xs_x27_1711_; lean_object* v___y_1713_; 
v_v_1709_ = lean_array_fget(v_es_1700_, v_j_1703_);
v___x_1710_ = lean_box(0);
v_xs_x27_1711_ = lean_array_fset(v_es_1700_, v_j_1703_, v___x_1710_);
switch(lean_obj_tag(v_v_1709_))
{
case 0:
{
lean_object* v_key_1718_; lean_object* v_val_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1731_; 
v_key_1718_ = lean_ctor_get(v_v_1709_, 0);
v_val_1719_ = lean_ctor_get(v_v_1709_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_v_1709_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1721_ = v_v_1709_;
v_isShared_1722_ = v_isSharedCheck_1731_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_val_1719_);
lean_inc(v_key_1718_);
lean_dec(v_v_1709_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1731_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v___x_1723_ = l_Lean_Meta_Grind_Origin_key(v_x_1698_);
v___x_1724_ = l_Lean_Meta_Grind_Origin_key(v_key_1718_);
v___x_1725_ = lean_name_eq(v___x_1723_, v___x_1724_);
lean_dec(v___x_1724_);
lean_dec(v___x_1723_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_del_object(v___x_1721_);
v___x_1726_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1718_, v_val_1719_, v_x_1698_, v_x_1699_);
v___x_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
v___y_1713_ = v___x_1727_;
goto v___jp_1712_;
}
else
{
lean_object* v___x_1729_; 
lean_dec(v_val_1719_);
lean_dec(v_key_1718_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 1, v_x_1699_);
lean_ctor_set(v___x_1721_, 0, v_x_1698_);
v___x_1729_ = v___x_1721_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_x_1698_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_x_1699_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
v___y_1713_ = v___x_1729_;
goto v___jp_1712_;
}
}
}
}
case 1:
{
lean_object* v_node_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1744_; 
v_node_1732_ = lean_ctor_get(v_v_1709_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_v_1709_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1734_ = v_v_1709_;
v_isShared_1735_ = v_isSharedCheck_1744_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_node_1732_);
lean_dec(v_v_1709_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1744_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
size_t v___x_1736_; size_t v___x_1737_; size_t v___x_1738_; size_t v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1736_ = ((size_t)5ULL);
v___x_1737_ = lean_usize_shift_right(v_x_1696_, v___x_1736_);
v___x_1738_ = ((size_t)1ULL);
v___x_1739_ = lean_usize_add(v_x_1697_, v___x_1738_);
v___x_1740_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_node_1732_, v___x_1737_, v___x_1739_, v_x_1698_, v_x_1699_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1740_);
v___x_1742_ = v___x_1734_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
v___y_1713_ = v___x_1742_;
goto v___jp_1712_;
}
}
}
default: 
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v_x_1698_);
lean_ctor_set(v___x_1745_, 1, v_x_1699_);
v___y_1713_ = v___x_1745_;
goto v___jp_1712_;
}
}
v___jp_1712_:
{
lean_object* v___x_1714_; lean_object* v___x_1716_; 
v___x_1714_ = lean_array_fset(v_xs_x27_1711_, v_j_1703_, v___y_1713_);
lean_dec(v_j_1703_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1714_);
v___x_1716_ = v___x_1707_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
else
{
lean_object* v_ks_1748_; lean_object* v_vs_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1767_; 
v_ks_1748_ = lean_ctor_get(v_x_1695_, 0);
v_vs_1749_ = lean_ctor_get(v_x_1695_, 1);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_x_1695_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1751_ = v_x_1695_;
v_isShared_1752_ = v_isSharedCheck_1767_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_vs_1749_);
lean_inc(v_ks_1748_);
lean_dec(v_x_1695_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1767_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_ks_1748_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_vs_1749_);
v___x_1754_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v_newNode_1755_; size_t v___x_1756_; uint8_t v___x_1757_; 
v_newNode_1755_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(v___x_1754_, v_x_1698_, v_x_1699_);
v___x_1756_ = ((size_t)7ULL);
v___x_1757_ = lean_usize_dec_le(v___x_1756_, v_x_1697_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1758_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1755_);
v___x_1759_ = lean_unsigned_to_nat(4u);
v___x_1760_ = lean_nat_dec_lt(v___x_1758_, v___x_1759_);
lean_dec(v___x_1758_);
if (v___x_1760_ == 0)
{
lean_object* v_ks_1761_; lean_object* v_vs_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v_ks_1761_ = lean_ctor_get(v_newNode_1755_, 0);
lean_inc_ref(v_ks_1761_);
v_vs_1762_ = lean_ctor_get(v_newNode_1755_, 1);
lean_inc_ref(v_vs_1762_);
lean_dec_ref(v_newNode_1755_);
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0);
v___x_1765_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_x_1697_, v_ks_1761_, v_vs_1762_, v___x_1763_, v___x_1764_);
lean_dec_ref(v_vs_1762_);
lean_dec_ref(v_ks_1761_);
return v___x_1765_;
}
else
{
return v_newNode_1755_;
}
}
else
{
return v_newNode_1755_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(size_t v_depth_1768_, lean_object* v_keys_1769_, lean_object* v_vals_1770_, lean_object* v_i_1771_, lean_object* v_entries_1772_){
_start:
{
lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = lean_array_get_size(v_keys_1769_);
v___x_1774_ = lean_nat_dec_lt(v_i_1771_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_dec(v_i_1771_);
return v_entries_1772_;
}
else
{
lean_object* v_k_1775_; lean_object* v_v_1776_; uint64_t v___y_1778_; lean_object* v___x_1789_; 
v_k_1775_ = lean_array_fget_borrowed(v_keys_1769_, v_i_1771_);
v_v_1776_ = lean_array_fget_borrowed(v_vals_1770_, v_i_1771_);
v___x_1789_ = l_Lean_Meta_Grind_Origin_key(v_k_1775_);
if (lean_obj_tag(v___x_1789_) == 0)
{
uint64_t v___x_1790_; 
v___x_1790_ = 1723ULL;
v___y_1778_ = v___x_1790_;
goto v___jp_1777_;
}
else
{
uint64_t v_hash_1791_; 
v_hash_1791_ = lean_ctor_get_uint64(v___x_1789_, sizeof(void*)*2);
lean_dec(v___x_1789_);
v___y_1778_ = v_hash_1791_;
goto v___jp_1777_;
}
v___jp_1777_:
{
size_t v_h_1779_; size_t v___x_1780_; lean_object* v___x_1781_; size_t v___x_1782_; size_t v___x_1783_; size_t v___x_1784_; size_t v_h_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_h_1779_ = lean_uint64_to_usize(v___y_1778_);
v___x_1780_ = ((size_t)5ULL);
v___x_1781_ = lean_unsigned_to_nat(1u);
v___x_1782_ = ((size_t)1ULL);
v___x_1783_ = lean_usize_sub(v_depth_1768_, v___x_1782_);
v___x_1784_ = lean_usize_mul(v___x_1780_, v___x_1783_);
v_h_1785_ = lean_usize_shift_right(v_h_1779_, v___x_1784_);
v___x_1786_ = lean_nat_add(v_i_1771_, v___x_1781_);
lean_dec(v_i_1771_);
lean_inc(v_v_1776_);
lean_inc(v_k_1775_);
v___x_1787_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_entries_1772_, v_h_1785_, v_depth_1768_, v_k_1775_, v_v_1776_);
v_i_1771_ = v___x_1786_;
v_entries_1772_ = v___x_1787_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_depth_1792_, lean_object* v_keys_1793_, lean_object* v_vals_1794_, lean_object* v_i_1795_, lean_object* v_entries_1796_){
_start:
{
size_t v_depth_boxed_1797_; lean_object* v_res_1798_; 
v_depth_boxed_1797_ = lean_unbox_usize(v_depth_1792_);
lean_dec(v_depth_1792_);
v_res_1798_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_depth_boxed_1797_, v_keys_1793_, v_vals_1794_, v_i_1795_, v_entries_1796_);
lean_dec_ref(v_vals_1794_);
lean_dec_ref(v_keys_1793_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_x_1799_, lean_object* v_x_1800_, lean_object* v_x_1801_, lean_object* v_x_1802_, lean_object* v_x_1803_){
_start:
{
size_t v_x_1258__boxed_1804_; size_t v_x_1259__boxed_1805_; lean_object* v_res_1806_; 
v_x_1258__boxed_1804_ = lean_unbox_usize(v_x_1800_);
lean_dec(v_x_1800_);
v_x_1259__boxed_1805_ = lean_unbox_usize(v_x_1801_);
lean_dec(v_x_1801_);
v_res_1806_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_1799_, v_x_1258__boxed_1804_, v_x_1259__boxed_1805_, v_x_1802_, v_x_1803_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(lean_object* v_x_1807_, lean_object* v_x_1808_, lean_object* v_x_1809_){
_start:
{
uint64_t v___y_1811_; lean_object* v___x_1815_; 
v___x_1815_ = l_Lean_Meta_Grind_Origin_key(v_x_1808_);
if (lean_obj_tag(v___x_1815_) == 0)
{
uint64_t v___x_1816_; 
v___x_1816_ = 1723ULL;
v___y_1811_ = v___x_1816_;
goto v___jp_1810_;
}
else
{
uint64_t v_hash_1817_; 
v_hash_1817_ = lean_ctor_get_uint64(v___x_1815_, sizeof(void*)*2);
lean_dec(v___x_1815_);
v___y_1811_ = v_hash_1817_;
goto v___jp_1810_;
}
v___jp_1810_:
{
size_t v___x_1812_; size_t v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = lean_uint64_to_usize(v___y_1811_);
v___x_1813_ = ((size_t)1ULL);
v___x_1814_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_1807_, v___x_1812_, v___x_1813_, v_x_1808_, v_x_1809_);
return v___x_1814_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(lean_object* v_keys_1818_, lean_object* v_vals_1819_, lean_object* v_i_1820_, lean_object* v_k_1821_){
_start:
{
lean_object* v___x_1822_; uint8_t v___x_1823_; 
v___x_1822_ = lean_array_get_size(v_keys_1818_);
v___x_1823_ = lean_nat_dec_lt(v_i_1820_, v___x_1822_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
lean_dec(v_i_1820_);
v___x_1824_ = lean_box(0);
return v___x_1824_;
}
else
{
lean_object* v_k_x27_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v_k_x27_1825_ = lean_array_fget_borrowed(v_keys_1818_, v_i_1820_);
v___x_1826_ = l_Lean_Meta_Grind_Origin_key(v_k_1821_);
v___x_1827_ = l_Lean_Meta_Grind_Origin_key(v_k_x27_1825_);
v___x_1828_ = lean_name_eq(v___x_1826_, v___x_1827_);
lean_dec(v___x_1827_);
lean_dec(v___x_1826_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = lean_unsigned_to_nat(1u);
v___x_1830_ = lean_nat_add(v_i_1820_, v___x_1829_);
lean_dec(v_i_1820_);
v_i_1820_ = v___x_1830_;
goto _start;
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = lean_array_fget_borrowed(v_vals_1819_, v_i_1820_);
lean_dec(v_i_1820_);
lean_inc(v___x_1832_);
v___x_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
return v___x_1833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg___boxed(lean_object* v_keys_1834_, lean_object* v_vals_1835_, lean_object* v_i_1836_, lean_object* v_k_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_keys_1834_, v_vals_1835_, v_i_1836_, v_k_1837_);
lean_dec_ref(v_k_1837_);
lean_dec_ref(v_vals_1835_);
lean_dec_ref(v_keys_1834_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(lean_object* v_x_1839_, size_t v_x_1840_, lean_object* v_x_1841_){
_start:
{
if (lean_obj_tag(v_x_1839_) == 0)
{
lean_object* v_es_1842_; lean_object* v___x_1843_; size_t v___x_1844_; size_t v___x_1845_; lean_object* v_j_1846_; lean_object* v___x_1847_; 
v_es_1842_ = lean_ctor_get(v_x_1839_, 0);
v___x_1843_ = lean_box(2);
v___x_1844_ = ((size_t)31ULL);
v___x_1845_ = lean_usize_land(v_x_1840_, v___x_1844_);
v_j_1846_ = lean_usize_to_nat(v___x_1845_);
v___x_1847_ = lean_array_get_borrowed(v___x_1843_, v_es_1842_, v_j_1846_);
lean_dec(v_j_1846_);
switch(lean_obj_tag(v___x_1847_))
{
case 0:
{
lean_object* v_key_1848_; lean_object* v_val_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; 
v_key_1848_ = lean_ctor_get(v___x_1847_, 0);
v_val_1849_ = lean_ctor_get(v___x_1847_, 1);
v___x_1850_ = l_Lean_Meta_Grind_Origin_key(v_x_1841_);
v___x_1851_ = l_Lean_Meta_Grind_Origin_key(v_key_1848_);
v___x_1852_ = lean_name_eq(v___x_1850_, v___x_1851_);
lean_dec(v___x_1851_);
lean_dec(v___x_1850_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_box(0);
return v___x_1853_;
}
else
{
lean_object* v___x_1854_; 
lean_inc(v_val_1849_);
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v_val_1849_);
return v___x_1854_;
}
}
case 1:
{
lean_object* v_node_1855_; size_t v___x_1856_; size_t v___x_1857_; 
v_node_1855_ = lean_ctor_get(v___x_1847_, 0);
v___x_1856_ = ((size_t)5ULL);
v___x_1857_ = lean_usize_shift_right(v_x_1840_, v___x_1856_);
v_x_1839_ = v_node_1855_;
v_x_1840_ = v___x_1857_;
goto _start;
}
default: 
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_box(0);
return v___x_1859_;
}
}
}
else
{
lean_object* v_ks_1860_; lean_object* v_vs_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v_ks_1860_ = lean_ctor_get(v_x_1839_, 0);
v_vs_1861_ = lean_ctor_get(v_x_1839_, 1);
v___x_1862_ = lean_unsigned_to_nat(0u);
v___x_1863_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_ks_1860_, v_vs_1861_, v___x_1862_, v_x_1841_);
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_x_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_){
_start:
{
size_t v_x_1458__boxed_1867_; lean_object* v_res_1868_; 
v_x_1458__boxed_1867_ = lean_unbox_usize(v_x_1865_);
lean_dec(v_x_1865_);
v_res_1868_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_1864_, v_x_1458__boxed_1867_, v_x_1866_);
lean_dec_ref(v_x_1866_);
lean_dec_ref(v_x_1864_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(lean_object* v_x_1869_, lean_object* v_x_1870_){
_start:
{
uint64_t v___y_1872_; lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_Meta_Grind_Origin_key(v_x_1870_);
if (lean_obj_tag(v___x_1875_) == 0)
{
uint64_t v___x_1876_; 
v___x_1876_ = 1723ULL;
v___y_1872_ = v___x_1876_;
goto v___jp_1871_;
}
else
{
uint64_t v_hash_1877_; 
v_hash_1877_ = lean_ctor_get_uint64(v___x_1875_, sizeof(void*)*2);
lean_dec(v___x_1875_);
v___y_1872_ = v_hash_1877_;
goto v___jp_1871_;
}
v___jp_1871_:
{
size_t v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = lean_uint64_to_usize(v___y_1872_);
v___x_1874_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_1869_, v___x_1873_, v_x_1870_);
return v___x_1874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg___boxed(lean_object* v_x_1878_, lean_object* v_x_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_x_1878_, v_x_1879_);
lean_dec_ref(v_x_1879_);
lean_dec_ref(v_x_1878_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(lean_object* v_keys_1881_, lean_object* v_vals_1882_, lean_object* v_i_1883_, lean_object* v_k_1884_){
_start:
{
lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1885_ = lean_array_get_size(v_keys_1881_);
v___x_1886_ = lean_nat_dec_lt(v_i_1883_, v___x_1885_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; 
lean_dec(v_i_1883_);
v___x_1887_ = lean_box(0);
return v___x_1887_;
}
else
{
lean_object* v_k_x27_1888_; uint8_t v___x_1889_; 
v_k_x27_1888_ = lean_array_fget_borrowed(v_keys_1881_, v_i_1883_);
v___x_1889_ = lean_name_eq(v_k_1884_, v_k_x27_1888_);
if (v___x_1889_ == 0)
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_unsigned_to_nat(1u);
v___x_1891_ = lean_nat_add(v_i_1883_, v___x_1890_);
lean_dec(v_i_1883_);
v_i_1883_ = v___x_1891_;
goto _start;
}
else
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_array_fget_borrowed(v_vals_1882_, v_i_1883_);
lean_dec(v_i_1883_);
lean_inc(v___x_1893_);
v___x_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg___boxed(lean_object* v_keys_1895_, lean_object* v_vals_1896_, lean_object* v_i_1897_, lean_object* v_k_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_keys_1895_, v_vals_1896_, v_i_1897_, v_k_1898_);
lean_dec(v_k_1898_);
lean_dec_ref(v_vals_1896_);
lean_dec_ref(v_keys_1895_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(lean_object* v_x_1900_, size_t v_x_1901_, lean_object* v_x_1902_){
_start:
{
if (lean_obj_tag(v_x_1900_) == 0)
{
lean_object* v_es_1903_; lean_object* v___x_1904_; size_t v___x_1905_; size_t v___x_1906_; lean_object* v_j_1907_; lean_object* v___x_1908_; 
v_es_1903_ = lean_ctor_get(v_x_1900_, 0);
v___x_1904_ = lean_box(2);
v___x_1905_ = ((size_t)31ULL);
v___x_1906_ = lean_usize_land(v_x_1901_, v___x_1905_);
v_j_1907_ = lean_usize_to_nat(v___x_1906_);
v___x_1908_ = lean_array_get_borrowed(v___x_1904_, v_es_1903_, v_j_1907_);
lean_dec(v_j_1907_);
switch(lean_obj_tag(v___x_1908_))
{
case 0:
{
lean_object* v_key_1909_; lean_object* v_val_1910_; uint8_t v___x_1911_; 
v_key_1909_ = lean_ctor_get(v___x_1908_, 0);
v_val_1910_ = lean_ctor_get(v___x_1908_, 1);
v___x_1911_ = lean_name_eq(v_x_1902_, v_key_1909_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_box(0);
return v___x_1912_;
}
else
{
lean_object* v___x_1913_; 
lean_inc(v_val_1910_);
v___x_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_val_1910_);
return v___x_1913_;
}
}
case 1:
{
lean_object* v_node_1914_; size_t v___x_1915_; size_t v___x_1916_; 
v_node_1914_ = lean_ctor_get(v___x_1908_, 0);
v___x_1915_ = ((size_t)5ULL);
v___x_1916_ = lean_usize_shift_right(v_x_1901_, v___x_1915_);
v_x_1900_ = v_node_1914_;
v_x_1901_ = v___x_1916_;
goto _start;
}
default: 
{
lean_object* v___x_1918_; 
v___x_1918_ = lean_box(0);
return v___x_1918_;
}
}
}
else
{
lean_object* v_ks_1919_; lean_object* v_vs_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_ks_1919_ = lean_ctor_get(v_x_1900_, 0);
v_vs_1920_ = lean_ctor_get(v_x_1900_, 1);
v___x_1921_ = lean_unsigned_to_nat(0u);
v___x_1922_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_ks_1919_, v_vs_1920_, v___x_1921_, v_x_1902_);
return v___x_1922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg___boxed(lean_object* v_x_1923_, lean_object* v_x_1924_, lean_object* v_x_1925_){
_start:
{
size_t v_x_1545__boxed_1926_; lean_object* v_res_1927_; 
v_x_1545__boxed_1926_ = lean_unbox_usize(v_x_1924_);
lean_dec(v_x_1924_);
v_res_1927_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_1923_, v_x_1545__boxed_1926_, v_x_1925_);
lean_dec(v_x_1925_);
lean_dec_ref(v_x_1923_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(lean_object* v_x_1928_, lean_object* v_x_1929_){
_start:
{
uint64_t v___y_1931_; 
if (lean_obj_tag(v_x_1929_) == 0)
{
uint64_t v___x_1934_; 
v___x_1934_ = 1723ULL;
v___y_1931_ = v___x_1934_;
goto v___jp_1930_;
}
else
{
uint64_t v_hash_1935_; 
v_hash_1935_ = lean_ctor_get_uint64(v_x_1929_, sizeof(void*)*2);
v___y_1931_ = v_hash_1935_;
goto v___jp_1930_;
}
v___jp_1930_:
{
size_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = lean_uint64_to_usize(v___y_1931_);
v___x_1933_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_1928_, v___x_1932_, v_x_1929_);
return v___x_1933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg___boxed(lean_object* v_x_1936_, lean_object* v_x_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_x_1936_, v_x_1937_);
lean_dec(v_x_1937_);
lean_dec_ref(v_x_1936_);
return v_res_1938_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg();
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0(lean_object* v_msg_1947_){
_start:
{
lean_object* v___f_1948_; lean_object* v___f_1949_; lean_object* v___f_1950_; lean_object* v___f_1951_; lean_object* v___f_1952_; lean_object* v___f_1953_; lean_object* v___f_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___f_1948_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0));
v___f_1949_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1));
v___f_1950_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2));
v___f_1951_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3));
v___f_1952_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4));
v___f_1953_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5));
v___f_1954_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6));
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___f_1948_);
lean_ctor_set(v___x_1955_, 1, v___f_1949_);
v___x_1956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
lean_ctor_set(v___x_1956_, 1, v___f_1950_);
lean_ctor_set(v___x_1956_, 2, v___f_1951_);
lean_ctor_set(v___x_1956_, 3, v___f_1952_);
lean_ctor_set(v___x_1956_, 4, v___f_1953_);
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
lean_ctor_set(v___x_1957_, 1, v___f_1954_);
v___x_1958_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7, &l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once, _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7);
v___x_1959_ = l_instInhabitedOfMonad___redArg(v___x_1957_, v___x_1958_);
v___x_1960_ = lean_panic_fn_borrowed(v___x_1959_, v_msg_1947_);
lean_dec(v___x_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(lean_object* v_xs_1961_, lean_object* v_v_1962_, lean_object* v_i_1963_){
_start:
{
lean_object* v___x_1964_; uint8_t v___x_1965_; 
v___x_1964_ = lean_array_get_size(v_xs_1961_);
v___x_1965_ = lean_nat_dec_lt(v_i_1963_, v___x_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
lean_dec(v_i_1963_);
v___x_1966_ = lean_box(0);
return v___x_1966_;
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
v___x_1967_ = lean_array_fget_borrowed(v_xs_1961_, v_i_1963_);
v___x_1968_ = l_Lean_Meta_Grind_Origin_key(v___x_1967_);
v___x_1969_ = l_Lean_Meta_Grind_Origin_key(v_v_1962_);
v___x_1970_ = lean_name_eq(v___x_1968_, v___x_1969_);
lean_dec(v___x_1969_);
lean_dec(v___x_1968_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = lean_unsigned_to_nat(1u);
v___x_1972_ = lean_nat_add(v_i_1963_, v___x_1971_);
lean_dec(v_i_1963_);
v_i_1963_ = v___x_1972_;
goto _start;
}
else
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1974_, 0, v_i_1963_);
return v___x_1974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13___boxed(lean_object* v_xs_1975_, lean_object* v_v_1976_, lean_object* v_i_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(v_xs_1975_, v_v_1976_, v_i_1977_);
lean_dec_ref(v_v_1976_);
lean_dec_ref(v_xs_1975_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(lean_object* v_xs_1979_, lean_object* v_v_1980_){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = lean_unsigned_to_nat(0u);
v___x_1982_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(v_xs_1979_, v_v_1980_, v___x_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9___boxed(lean_object* v_xs_1983_, lean_object* v_v_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(v_xs_1983_, v_v_1984_);
lean_dec_ref(v_v_1984_);
lean_dec_ref(v_xs_1983_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(lean_object* v_x_1986_, size_t v_x_1987_, lean_object* v_x_1988_){
_start:
{
if (lean_obj_tag(v_x_1986_) == 0)
{
lean_object* v_es_1989_; lean_object* v___x_1990_; size_t v___x_1991_; size_t v___x_1992_; lean_object* v_j_1993_; lean_object* v_entry_1994_; 
v_es_1989_ = lean_ctor_get(v_x_1986_, 0);
v___x_1990_ = lean_box(2);
v___x_1991_ = ((size_t)31ULL);
v___x_1992_ = lean_usize_land(v_x_1987_, v___x_1991_);
v_j_1993_ = lean_usize_to_nat(v___x_1992_);
v_entry_1994_ = lean_array_get(v___x_1990_, v_es_1989_, v_j_1993_);
switch(lean_obj_tag(v_entry_1994_))
{
case 0:
{
lean_object* v_key_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v_key_1995_ = lean_ctor_get(v_entry_1994_, 0);
lean_inc(v_key_1995_);
lean_dec_ref_known(v_entry_1994_, 2);
v___x_1996_ = l_Lean_Meta_Grind_Origin_key(v_x_1988_);
v___x_1997_ = l_Lean_Meta_Grind_Origin_key(v_key_1995_);
lean_dec(v_key_1995_);
v___x_1998_ = lean_name_eq(v___x_1996_, v___x_1997_);
lean_dec(v___x_1997_);
lean_dec(v___x_1996_);
if (v___x_1998_ == 0)
{
lean_dec(v_j_1993_);
return v_x_1986_;
}
else
{
lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2006_; 
lean_inc_ref(v_es_1989_);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_x_1986_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; 
v_unused_2007_ = lean_ctor_get(v_x_1986_, 0);
lean_dec(v_unused_2007_);
v___x_2000_ = v_x_1986_;
v_isShared_2001_ = v_isSharedCheck_2006_;
goto v_resetjp_1999_;
}
else
{
lean_dec(v_x_1986_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2006_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2004_; 
v___x_2002_ = lean_array_set(v_es_1989_, v_j_1993_, v___x_1990_);
lean_dec(v_j_1993_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2002_);
v___x_2004_ = v___x_2000_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
case 1:
{
lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2042_; 
lean_inc_ref(v_es_1989_);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_x_1986_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; 
v_unused_2043_ = lean_ctor_get(v_x_1986_, 0);
lean_dec(v_unused_2043_);
v___x_2009_ = v_x_1986_;
v_isShared_2010_ = v_isSharedCheck_2042_;
goto v_resetjp_2008_;
}
else
{
lean_dec(v_x_1986_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2042_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_node_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2041_; 
v_node_2011_ = lean_ctor_get(v_entry_1994_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_entry_1994_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2013_ = v_entry_1994_;
v_isShared_2014_ = v_isSharedCheck_2041_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_node_2011_);
lean_dec(v_entry_1994_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2041_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
size_t v___x_2015_; lean_object* v_entries_2016_; size_t v___x_2017_; lean_object* v_newNode_2018_; lean_object* v___x_2019_; 
v___x_2015_ = ((size_t)5ULL);
v_entries_2016_ = lean_array_set(v_es_1989_, v_j_1993_, v___x_1990_);
v___x_2017_ = lean_usize_shift_right(v_x_1987_, v___x_2015_);
v_newNode_2018_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_node_2011_, v___x_2017_, v_x_1988_);
lean_inc_ref(v_newNode_2018_);
v___x_2019_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2018_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v___x_2021_; 
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v_newNode_2018_);
v___x_2021_ = v___x_2013_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_newNode_2018_);
v___x_2021_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2022_ = lean_array_set(v_entries_2016_, v_j_1993_, v___x_2021_);
lean_dec(v_j_1993_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2022_);
v___x_2024_ = v___x_2009_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
else
{
lean_object* v_val_2027_; lean_object* v_fst_2028_; lean_object* v_snd_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2040_; 
lean_dec_ref(v_newNode_2018_);
lean_del_object(v___x_2013_);
v_val_2027_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_val_2027_);
lean_dec_ref_known(v___x_2019_, 1);
v_fst_2028_ = lean_ctor_get(v_val_2027_, 0);
v_snd_2029_ = lean_ctor_get(v_val_2027_, 1);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_val_2027_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2031_ = v_val_2027_;
v_isShared_2032_ = v_isSharedCheck_2040_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_snd_2029_);
lean_inc(v_fst_2028_);
lean_dec(v_val_2027_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2040_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_fst_2028_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_snd_2029_);
v___x_2034_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2035_ = lean_array_set(v_entries_2016_, v_j_1993_, v___x_2034_);
lean_dec(v_j_1993_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2035_);
v___x_2037_ = v___x_2009_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_1993_);
return v_x_1986_;
}
}
}
else
{
lean_object* v_ks_2044_; lean_object* v_vs_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2059_; 
v_ks_2044_ = lean_ctor_get(v_x_1986_, 0);
v_vs_2045_ = lean_ctor_get(v_x_1986_, 1);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_x_1986_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2047_ = v_x_1986_;
v_isShared_2048_ = v_isSharedCheck_2059_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_vs_2045_);
lean_inc(v_ks_2044_);
lean_dec(v_x_1986_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2059_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(v_ks_2044_, v_x_1988_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v___x_2051_; 
if (v_isShared_2048_ == 0)
{
v___x_2051_ = v___x_2047_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_ks_2044_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_vs_2045_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
else
{
lean_object* v_val_2053_; lean_object* v_keys_x27_2054_; lean_object* v_vals_x27_2055_; lean_object* v___x_2057_; 
v_val_2053_ = lean_ctor_get(v___x_2049_, 0);
lean_inc_n(v_val_2053_, 2);
lean_dec_ref_known(v___x_2049_, 1);
v_keys_x27_2054_ = l_Array_eraseIdx___redArg(v_ks_2044_, v_val_2053_);
v_vals_x27_2055_ = l_Array_eraseIdx___redArg(v_vs_2045_, v_val_2053_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 1, v_vals_x27_2055_);
lean_ctor_set(v___x_2047_, 0, v_keys_x27_2054_);
v___x_2057_ = v___x_2047_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_keys_x27_2054_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v_vals_x27_2055_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2060_, lean_object* v_x_2061_, lean_object* v_x_2062_){
_start:
{
size_t v_x_1684__boxed_2063_; lean_object* v_res_2064_; 
v_x_1684__boxed_2063_ = lean_unbox_usize(v_x_2061_);
lean_dec(v_x_2061_);
v_res_2064_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2060_, v_x_1684__boxed_2063_, v_x_2062_);
lean_dec_ref(v_x_2062_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(lean_object* v_x_2065_, lean_object* v_x_2066_){
_start:
{
uint64_t v___y_2068_; lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_Meta_Grind_Origin_key(v_x_2066_);
if (lean_obj_tag(v___x_2071_) == 0)
{
uint64_t v___x_2072_; 
v___x_2072_ = 1723ULL;
v___y_2068_ = v___x_2072_;
goto v___jp_2067_;
}
else
{
uint64_t v_hash_2073_; 
v_hash_2073_ = lean_ctor_get_uint64(v___x_2071_, sizeof(void*)*2);
lean_dec(v___x_2071_);
v___y_2068_ = v_hash_2073_;
goto v___jp_2067_;
}
v___jp_2067_:
{
size_t v_h_2069_; lean_object* v___x_2070_; 
v_h_2069_ = lean_uint64_to_usize(v___y_2068_);
v___x_2070_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2065_, v_h_2069_, v_x_2066_);
return v___x_2070_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg___boxed(lean_object* v_x_2074_, lean_object* v_x_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_x_2074_, v_x_2075_);
lean_dec_ref(v_x_2075_);
return v_res_2076_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2080_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2));
v___x_2081_ = lean_unsigned_to_nat(6u);
v___x_2082_ = lean_unsigned_to_nat(82u);
v___x_2083_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__1));
v___x_2084_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__0));
v___x_2085_ = l_mkPanicMessageWithDecl(v___x_2084_, v___x_2083_, v___x_2082_, v___x_2081_, v___x_2080_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0(lean_object* v_s_2086_, lean_object* v_thm_2087_){
_start:
{
lean_object* v_symbols_2091_; 
v_symbols_2091_ = lean_ctor_get(v_thm_2087_, 4);
lean_inc(v_symbols_2091_);
if (lean_obj_tag(v_symbols_2091_) == 1)
{
lean_object* v_head_2092_; 
v_head_2092_ = lean_ctor_get(v_symbols_2091_, 0);
lean_inc(v_head_2092_);
if (lean_obj_tag(v_head_2092_) == 2)
{
lean_object* v_levelParams_2093_; lean_object* v_proof_2094_; lean_object* v_numParams_2095_; lean_object* v_patterns_2096_; lean_object* v_origin_2097_; lean_object* v_kind_2098_; uint8_t v_minIndexable_2099_; lean_object* v_cnstrs_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2151_; 
v_levelParams_2093_ = lean_ctor_get(v_thm_2087_, 0);
v_proof_2094_ = lean_ctor_get(v_thm_2087_, 1);
v_numParams_2095_ = lean_ctor_get(v_thm_2087_, 2);
v_patterns_2096_ = lean_ctor_get(v_thm_2087_, 3);
v_origin_2097_ = lean_ctor_get(v_thm_2087_, 5);
v_kind_2098_ = lean_ctor_get(v_thm_2087_, 6);
v_minIndexable_2099_ = lean_ctor_get_uint8(v_thm_2087_, sizeof(void*)*8);
v_cnstrs_2100_ = lean_ctor_get(v_thm_2087_, 7);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_thm_2087_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; 
v_unused_2152_ = lean_ctor_get(v_thm_2087_, 4);
lean_dec(v_unused_2152_);
v___x_2102_ = v_thm_2087_;
v_isShared_2103_ = v_isSharedCheck_2151_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_cnstrs_2100_);
lean_inc(v_kind_2098_);
lean_inc(v_origin_2097_);
lean_inc(v_patterns_2096_);
lean_inc(v_numParams_2095_);
lean_inc(v_proof_2094_);
lean_inc(v_levelParams_2093_);
lean_dec(v_thm_2087_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2151_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v_tail_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2149_; 
v_tail_2104_ = lean_ctor_get(v_symbols_2091_, 1);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_symbols_2091_);
if (v_isSharedCheck_2149_ == 0)
{
lean_object* v_unused_2150_; 
v_unused_2150_ = lean_ctor_get(v_symbols_2091_, 0);
lean_dec(v_unused_2150_);
v___x_2106_ = v_symbols_2091_;
v_isShared_2107_ = v_isSharedCheck_2149_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_tail_2104_);
lean_dec(v_symbols_2091_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2149_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v_constName_2108_; lean_object* v_smap_2109_; lean_object* v_origins_2110_; lean_object* v_erased_2111_; lean_object* v_omap_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2148_; 
v_constName_2108_ = lean_ctor_get(v_head_2092_, 0);
lean_inc(v_constName_2108_);
lean_dec_ref_known(v_head_2092_, 1);
v_smap_2109_ = lean_ctor_get(v_s_2086_, 0);
v_origins_2110_ = lean_ctor_get(v_s_2086_, 1);
v_erased_2111_ = lean_ctor_get(v_s_2086_, 2);
v_omap_2112_ = lean_ctor_get(v_s_2086_, 3);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_s_2086_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2114_ = v_s_2086_;
v_isShared_2115_ = v_isSharedCheck_2148_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_omap_2112_);
lean_inc(v_erased_2111_);
lean_inc(v_origins_2110_);
lean_inc(v_smap_2109_);
lean_dec(v_s_2086_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2148_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v_thm_2117_; 
lean_inc_ref(v_origin_2097_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 4, v_tail_2104_);
v_thm_2117_ = v___x_2102_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_levelParams_2093_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_proof_2094_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v_numParams_2095_);
lean_ctor_set(v_reuseFailAlloc_2147_, 3, v_patterns_2096_);
lean_ctor_set(v_reuseFailAlloc_2147_, 4, v_tail_2104_);
lean_ctor_set(v_reuseFailAlloc_2147_, 5, v_origin_2097_);
lean_ctor_set(v_reuseFailAlloc_2147_, 6, v_kind_2098_);
lean_ctor_set(v_reuseFailAlloc_2147_, 7, v_cnstrs_2100_);
lean_ctor_set_uint8(v_reuseFailAlloc_2147_, sizeof(void*)*8, v_minIndexable_2099_);
v_thm_2117_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2118_; lean_object* v_origins_2119_; lean_object* v_erased_2120_; lean_object* v___y_2122_; lean_object* v___x_2140_; 
v___x_2118_ = lean_box(0);
lean_inc_ref(v_origin_2097_);
v_origins_2119_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_origins_2110_, v_origin_2097_, v___x_2118_);
v_erased_2120_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_erased_2111_, v_origin_2097_);
v___x_2140_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_smap_2109_, v_constName_2108_);
if (lean_obj_tag(v___x_2140_) == 1)
{
lean_object* v_val_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v_val_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_val_2141_);
lean_dec_ref_known(v___x_2140_, 1);
lean_inc_ref(v_thm_2117_);
v___x_2142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2142_, 0, v_thm_2117_);
lean_ctor_set(v___x_2142_, 1, v_val_2141_);
v___x_2143_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2109_, v_constName_2108_, v___x_2142_);
v___y_2122_ = v___x_2143_;
goto v___jp_2121_;
}
else
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_dec(v___x_2140_);
v___x_2144_ = lean_box(0);
lean_inc_ref(v_thm_2117_);
v___x_2145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2145_, 0, v_thm_2117_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2109_, v_constName_2108_, v___x_2145_);
v___y_2122_ = v___x_2146_;
goto v___jp_2121_;
}
v___jp_2121_:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_omap_2112_, v_origin_2097_);
if (lean_obj_tag(v___x_2123_) == 1)
{
lean_object* v_val_2124_; lean_object* v___x_2126_; 
v_val_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_val_2124_);
lean_dec_ref_known(v___x_2123_, 1);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 1, v_val_2124_);
lean_ctor_set(v___x_2106_, 0, v_thm_2117_);
v___x_2126_ = v___x_2106_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_thm_2117_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_val_2124_);
v___x_2126_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2112_, v_origin_2097_, v___x_2126_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 3, v___x_2127_);
lean_ctor_set(v___x_2114_, 2, v_erased_2120_);
lean_ctor_set(v___x_2114_, 1, v_origins_2119_);
lean_ctor_set(v___x_2114_, 0, v___y_2122_);
v___x_2129_ = v___x_2114_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___y_2122_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_origins_2119_);
lean_ctor_set(v_reuseFailAlloc_2130_, 2, v_erased_2120_);
lean_ctor_set(v_reuseFailAlloc_2130_, 3, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
lean_dec(v___x_2123_);
v___x_2132_ = lean_box(0);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 1, v___x_2132_);
lean_ctor_set(v___x_2106_, 0, v_thm_2117_);
v___x_2134_ = v___x_2106_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_thm_2117_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
v___x_2135_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2112_, v_origin_2097_, v___x_2134_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 3, v___x_2135_);
lean_ctor_set(v___x_2114_, 2, v_erased_2120_);
lean_ctor_set(v___x_2114_, 1, v_origins_2119_);
lean_ctor_set(v___x_2114_, 0, v___y_2122_);
v___x_2137_ = v___x_2114_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___y_2122_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_origins_2119_);
lean_ctor_set(v_reuseFailAlloc_2138_, 2, v_erased_2120_);
lean_ctor_set(v_reuseFailAlloc_2138_, 3, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
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
lean_dec_ref_known(v_symbols_2091_, 2);
lean_dec(v_head_2092_);
lean_dec_ref(v_thm_2087_);
lean_dec_ref(v_s_2086_);
goto v___jp_2088_;
}
}
else
{
lean_dec(v_symbols_2091_);
lean_dec_ref(v_thm_2087_);
lean_dec_ref(v_s_2086_);
goto v___jp_2088_;
}
v___jp_2088_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3, &l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3);
v___x_2090_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0(v___x_2089_);
return v___x_2090_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1_spec__6(lean_object* v_msg_2153_){
_start:
{
lean_object* v___f_2154_; lean_object* v___f_2155_; lean_object* v___f_2156_; lean_object* v___f_2157_; lean_object* v___f_2158_; lean_object* v___f_2159_; lean_object* v___f_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___f_2154_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0));
v___f_2155_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1));
v___f_2156_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2));
v___f_2157_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3));
v___f_2158_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4));
v___f_2159_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5));
v___f_2160_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6));
v___x_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___f_2154_);
lean_ctor_set(v___x_2161_, 1, v___f_2155_);
v___x_2162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
lean_ctor_set(v___x_2162_, 1, v___f_2156_);
lean_ctor_set(v___x_2162_, 2, v___f_2157_);
lean_ctor_set(v___x_2162_, 3, v___f_2158_);
lean_ctor_set(v___x_2162_, 4, v___f_2159_);
v___x_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
lean_ctor_set(v___x_2163_, 1, v___f_2160_);
v___x_2164_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7, &l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once, _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7);
v___x_2165_ = l_instInhabitedOfMonad___redArg(v___x_2163_, v___x_2164_);
v___x_2166_ = lean_panic_fn_borrowed(v___x_2165_, v_msg_2153_);
lean_dec(v___x_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1(lean_object* v_s_2167_, lean_object* v_thm_2168_){
_start:
{
lean_object* v_symbols_2172_; 
v_symbols_2172_ = lean_ctor_get(v_thm_2168_, 2);
lean_inc(v_symbols_2172_);
if (lean_obj_tag(v_symbols_2172_) == 1)
{
lean_object* v_head_2173_; 
v_head_2173_ = lean_ctor_get(v_symbols_2172_, 0);
lean_inc(v_head_2173_);
if (lean_obj_tag(v_head_2173_) == 2)
{
lean_object* v_levelParams_2174_; lean_object* v_proof_2175_; lean_object* v_origin_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2227_; 
v_levelParams_2174_ = lean_ctor_get(v_thm_2168_, 0);
v_proof_2175_ = lean_ctor_get(v_thm_2168_, 1);
v_origin_2176_ = lean_ctor_get(v_thm_2168_, 3);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_thm_2168_);
if (v_isSharedCheck_2227_ == 0)
{
lean_object* v_unused_2228_; 
v_unused_2228_ = lean_ctor_get(v_thm_2168_, 2);
lean_dec(v_unused_2228_);
v___x_2178_ = v_thm_2168_;
v_isShared_2179_ = v_isSharedCheck_2227_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_origin_2176_);
lean_inc(v_proof_2175_);
lean_inc(v_levelParams_2174_);
lean_dec(v_thm_2168_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2227_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v_tail_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2225_; 
v_tail_2180_ = lean_ctor_get(v_symbols_2172_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_symbols_2172_);
if (v_isSharedCheck_2225_ == 0)
{
lean_object* v_unused_2226_; 
v_unused_2226_ = lean_ctor_get(v_symbols_2172_, 0);
lean_dec(v_unused_2226_);
v___x_2182_ = v_symbols_2172_;
v_isShared_2183_ = v_isSharedCheck_2225_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_tail_2180_);
lean_dec(v_symbols_2172_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2225_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v_constName_2184_; lean_object* v_smap_2185_; lean_object* v_origins_2186_; lean_object* v_erased_2187_; lean_object* v_omap_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2224_; 
v_constName_2184_ = lean_ctor_get(v_head_2173_, 0);
lean_inc(v_constName_2184_);
lean_dec_ref_known(v_head_2173_, 1);
v_smap_2185_ = lean_ctor_get(v_s_2167_, 0);
v_origins_2186_ = lean_ctor_get(v_s_2167_, 1);
v_erased_2187_ = lean_ctor_get(v_s_2167_, 2);
v_omap_2188_ = lean_ctor_get(v_s_2167_, 3);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_s_2167_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2190_ = v_s_2167_;
v_isShared_2191_ = v_isSharedCheck_2224_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_omap_2188_);
lean_inc(v_erased_2187_);
lean_inc(v_origins_2186_);
lean_inc(v_smap_2185_);
lean_dec(v_s_2167_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2224_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v_thm_2193_; 
lean_inc_ref(v_origin_2176_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 2, v_tail_2180_);
v_thm_2193_ = v___x_2178_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_levelParams_2174_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_proof_2175_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_tail_2180_);
lean_ctor_set(v_reuseFailAlloc_2223_, 3, v_origin_2176_);
v_thm_2193_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
lean_object* v___x_2194_; lean_object* v_origins_2195_; lean_object* v_erased_2196_; lean_object* v___y_2198_; lean_object* v___x_2216_; 
v___x_2194_ = lean_box(0);
lean_inc_ref(v_origin_2176_);
v_origins_2195_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_origins_2186_, v_origin_2176_, v___x_2194_);
v_erased_2196_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_erased_2187_, v_origin_2176_);
v___x_2216_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_smap_2185_, v_constName_2184_);
if (lean_obj_tag(v___x_2216_) == 1)
{
lean_object* v_val_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v_val_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_val_2217_);
lean_dec_ref_known(v___x_2216_, 1);
lean_inc_ref(v_thm_2193_);
v___x_2218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2218_, 0, v_thm_2193_);
lean_ctor_set(v___x_2218_, 1, v_val_2217_);
v___x_2219_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2185_, v_constName_2184_, v___x_2218_);
v___y_2198_ = v___x_2219_;
goto v___jp_2197_;
}
else
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_dec(v___x_2216_);
v___x_2220_ = lean_box(0);
lean_inc_ref(v_thm_2193_);
v___x_2221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2221_, 0, v_thm_2193_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2185_, v_constName_2184_, v___x_2221_);
v___y_2198_ = v___x_2222_;
goto v___jp_2197_;
}
v___jp_2197_:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_omap_2188_, v_origin_2176_);
if (lean_obj_tag(v___x_2199_) == 1)
{
lean_object* v_val_2200_; lean_object* v___x_2202_; 
v_val_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_val_2200_);
lean_dec_ref_known(v___x_2199_, 1);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 1, v_val_2200_);
lean_ctor_set(v___x_2182_, 0, v_thm_2193_);
v___x_2202_ = v___x_2182_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_thm_2193_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_val_2200_);
v___x_2202_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2203_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2188_, v_origin_2176_, v___x_2202_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 3, v___x_2203_);
lean_ctor_set(v___x_2190_, 2, v_erased_2196_);
lean_ctor_set(v___x_2190_, 1, v_origins_2195_);
lean_ctor_set(v___x_2190_, 0, v___y_2198_);
v___x_2205_ = v___x_2190_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___y_2198_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_origins_2195_);
lean_ctor_set(v_reuseFailAlloc_2206_, 2, v_erased_2196_);
lean_ctor_set(v_reuseFailAlloc_2206_, 3, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
lean_dec(v___x_2199_);
v___x_2208_ = lean_box(0);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 1, v___x_2208_);
lean_ctor_set(v___x_2182_, 0, v_thm_2193_);
v___x_2210_ = v___x_2182_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_thm_2193_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2188_, v_origin_2176_, v___x_2210_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 3, v___x_2211_);
lean_ctor_set(v___x_2190_, 2, v_erased_2196_);
lean_ctor_set(v___x_2190_, 1, v_origins_2195_);
lean_ctor_set(v___x_2190_, 0, v___y_2198_);
v___x_2213_ = v___x_2190_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___y_2198_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_origins_2195_);
lean_ctor_set(v_reuseFailAlloc_2214_, 2, v_erased_2196_);
lean_ctor_set(v_reuseFailAlloc_2214_, 3, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
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
lean_dec(v_head_2173_);
lean_dec_ref_known(v_symbols_2172_, 2);
lean_dec_ref(v_thm_2168_);
lean_dec_ref(v_s_2167_);
goto v___jp_2169_;
}
}
else
{
lean_dec(v_symbols_2172_);
lean_dec_ref(v_thm_2168_);
lean_dec_ref(v_s_2167_);
goto v___jp_2169_;
}
v___jp_2169_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3, &l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3);
v___x_2171_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1_spec__6(v___x_2170_);
return v___x_2171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionState_addEntry(lean_object* v_s_2229_, lean_object* v_e_2230_){
_start:
{
switch(lean_obj_tag(v_e_2230_))
{
case 0:
{
lean_object* v_declName_2231_; lean_object* v_casesTypes_2232_; lean_object* v_extThms_2233_; lean_object* v_funCC_2234_; lean_object* v_ematch_2235_; lean_object* v_inj_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2245_; 
v_declName_2231_ = lean_ctor_get(v_e_2230_, 0);
lean_inc(v_declName_2231_);
lean_dec_ref_known(v_e_2230_, 1);
v_casesTypes_2232_ = lean_ctor_get(v_s_2229_, 0);
v_extThms_2233_ = lean_ctor_get(v_s_2229_, 1);
v_funCC_2234_ = lean_ctor_get(v_s_2229_, 2);
v_ematch_2235_ = lean_ctor_get(v_s_2229_, 3);
v_inj_2236_ = lean_ctor_get(v_s_2229_, 4);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_s_2229_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2238_ = v_s_2229_;
v_isShared_2239_ = v_isSharedCheck_2245_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_inj_2236_);
lean_inc(v_ematch_2235_);
lean_inc(v_funCC_2234_);
lean_inc(v_extThms_2233_);
lean_inc(v_casesTypes_2232_);
lean_dec(v_s_2229_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2245_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2243_; 
v___x_2240_ = lean_box(0);
v___x_2241_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_extThms_2233_, v_declName_2231_, v___x_2240_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 1, v___x_2241_);
v___x_2243_ = v___x_2238_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_casesTypes_2232_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v___x_2241_);
lean_ctor_set(v_reuseFailAlloc_2244_, 2, v_funCC_2234_);
lean_ctor_set(v_reuseFailAlloc_2244_, 3, v_ematch_2235_);
lean_ctor_set(v_reuseFailAlloc_2244_, 4, v_inj_2236_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
case 1:
{
lean_object* v_declName_2246_; lean_object* v_casesTypes_2247_; lean_object* v_extThms_2248_; lean_object* v_funCC_2249_; lean_object* v_ematch_2250_; lean_object* v_inj_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2259_; 
v_declName_2246_ = lean_ctor_get(v_e_2230_, 0);
lean_inc(v_declName_2246_);
lean_dec_ref_known(v_e_2230_, 1);
v_casesTypes_2247_ = lean_ctor_get(v_s_2229_, 0);
v_extThms_2248_ = lean_ctor_get(v_s_2229_, 1);
v_funCC_2249_ = lean_ctor_get(v_s_2229_, 2);
v_ematch_2250_ = lean_ctor_get(v_s_2229_, 3);
v_inj_2251_ = lean_ctor_get(v_s_2229_, 4);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_s_2229_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2253_ = v_s_2229_;
v_isShared_2254_ = v_isSharedCheck_2259_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_inj_2251_);
lean_inc(v_ematch_2250_);
lean_inc(v_funCC_2249_);
lean_inc(v_extThms_2248_);
lean_inc(v_casesTypes_2247_);
lean_dec(v_s_2229_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2259_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; lean_object* v___x_2257_; 
v___x_2255_ = l_Lean_NameSet_insert(v_funCC_2249_, v_declName_2246_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 2, v___x_2255_);
v___x_2257_ = v___x_2253_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_casesTypes_2247_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_extThms_2248_);
lean_ctor_set(v_reuseFailAlloc_2258_, 2, v___x_2255_);
lean_ctor_set(v_reuseFailAlloc_2258_, 3, v_ematch_2250_);
lean_ctor_set(v_reuseFailAlloc_2258_, 4, v_inj_2251_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
case 2:
{
lean_object* v_declName_2260_; uint8_t v_eager_2261_; lean_object* v_casesTypes_2262_; lean_object* v_extThms_2263_; lean_object* v_funCC_2264_; lean_object* v_ematch_2265_; lean_object* v_inj_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2275_; 
v_declName_2260_ = lean_ctor_get(v_e_2230_, 0);
lean_inc(v_declName_2260_);
v_eager_2261_ = lean_ctor_get_uint8(v_e_2230_, sizeof(void*)*1);
lean_dec_ref_known(v_e_2230_, 1);
v_casesTypes_2262_ = lean_ctor_get(v_s_2229_, 0);
v_extThms_2263_ = lean_ctor_get(v_s_2229_, 1);
v_funCC_2264_ = lean_ctor_get(v_s_2229_, 2);
v_ematch_2265_ = lean_ctor_get(v_s_2229_, 3);
v_inj_2266_ = lean_ctor_get(v_s_2229_, 4);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_s_2229_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2268_ = v_s_2229_;
v_isShared_2269_ = v_isSharedCheck_2275_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_inj_2266_);
lean_inc(v_ematch_2265_);
lean_inc(v_funCC_2264_);
lean_inc(v_extThms_2263_);
lean_inc(v_casesTypes_2262_);
lean_dec(v_s_2229_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2275_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2273_; 
v___x_2270_ = lean_box(v_eager_2261_);
v___x_2271_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_casesTypes_2262_, v_declName_2260_, v___x_2270_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 0, v___x_2271_);
v___x_2273_ = v___x_2268_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_extThms_2263_);
lean_ctor_set(v_reuseFailAlloc_2274_, 2, v_funCC_2264_);
lean_ctor_set(v_reuseFailAlloc_2274_, 3, v_ematch_2265_);
lean_ctor_set(v_reuseFailAlloc_2274_, 4, v_inj_2266_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
case 3:
{
lean_object* v_thm_2276_; lean_object* v_casesTypes_2277_; lean_object* v_extThms_2278_; lean_object* v_funCC_2279_; lean_object* v_ematch_2280_; lean_object* v_inj_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2289_; 
v_thm_2276_ = lean_ctor_get(v_e_2230_, 0);
lean_inc_ref(v_thm_2276_);
lean_dec_ref_known(v_e_2230_, 1);
v_casesTypes_2277_ = lean_ctor_get(v_s_2229_, 0);
v_extThms_2278_ = lean_ctor_get(v_s_2229_, 1);
v_funCC_2279_ = lean_ctor_get(v_s_2229_, 2);
v_ematch_2280_ = lean_ctor_get(v_s_2229_, 3);
v_inj_2281_ = lean_ctor_get(v_s_2229_, 4);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_s_2229_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2283_ = v_s_2229_;
v_isShared_2284_ = v_isSharedCheck_2289_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_inj_2281_);
lean_inc(v_ematch_2280_);
lean_inc(v_funCC_2279_);
lean_inc(v_extThms_2278_);
lean_inc(v_casesTypes_2277_);
lean_dec(v_s_2229_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2289_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2285_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0(v_ematch_2280_, v_thm_2276_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 3, v___x_2285_);
v___x_2287_ = v___x_2283_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_casesTypes_2277_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v_extThms_2278_);
lean_ctor_set(v_reuseFailAlloc_2288_, 2, v_funCC_2279_);
lean_ctor_set(v_reuseFailAlloc_2288_, 3, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2288_, 4, v_inj_2281_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
default: 
{
lean_object* v_thm_2290_; lean_object* v_casesTypes_2291_; lean_object* v_extThms_2292_; lean_object* v_funCC_2293_; lean_object* v_ematch_2294_; lean_object* v_inj_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2303_; 
v_thm_2290_ = lean_ctor_get(v_e_2230_, 0);
lean_inc_ref(v_thm_2290_);
lean_dec_ref_known(v_e_2230_, 1);
v_casesTypes_2291_ = lean_ctor_get(v_s_2229_, 0);
v_extThms_2292_ = lean_ctor_get(v_s_2229_, 1);
v_funCC_2293_ = lean_ctor_get(v_s_2229_, 2);
v_ematch_2294_ = lean_ctor_get(v_s_2229_, 3);
v_inj_2295_ = lean_ctor_get(v_s_2229_, 4);
v_isSharedCheck_2303_ = !lean_is_exclusive(v_s_2229_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2297_ = v_s_2229_;
v_isShared_2298_ = v_isSharedCheck_2303_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_inj_2295_);
lean_inc(v_ematch_2294_);
lean_inc(v_funCC_2293_);
lean_inc(v_extThms_2292_);
lean_inc(v_casesTypes_2291_);
lean_dec(v_s_2229_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2303_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v___x_2301_; 
v___x_2299_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1(v_inj_2295_, v_thm_2290_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 4, v___x_2299_);
v___x_2301_ = v___x_2297_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_casesTypes_2291_);
lean_ctor_set(v_reuseFailAlloc_2302_, 1, v_extThms_2292_);
lean_ctor_set(v_reuseFailAlloc_2302_, 2, v_funCC_2293_);
lean_ctor_set(v_reuseFailAlloc_2302_, 3, v_ematch_2294_);
lean_ctor_set(v_reuseFailAlloc_2302_, 4, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1(lean_object* v_00_u03b2_2304_, lean_object* v_x_2305_, lean_object* v_x_2306_, lean_object* v_x_2307_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_x_2305_, v_x_2306_, v_x_2307_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2(lean_object* v_00_u03b2_2309_, lean_object* v_x_2310_, lean_object* v_x_2311_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_x_2310_, v_x_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2313_, lean_object* v_x_2314_, lean_object* v_x_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2(v_00_u03b2_2313_, v_x_2314_, v_x_2315_);
lean_dec_ref(v_x_2315_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3(lean_object* v_00_u03b2_2317_, lean_object* v_x_2318_, lean_object* v_x_2319_){
_start:
{
lean_object* v___x_2320_; 
v___x_2320_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_x_2318_, v_x_2319_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2321_, lean_object* v_x_2322_, lean_object* v_x_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3(v_00_u03b2_2321_, v_x_2322_, v_x_2323_);
lean_dec_ref(v_x_2323_);
lean_dec_ref(v_x_2322_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4(lean_object* v_00_u03b2_2325_, lean_object* v_x_2326_, lean_object* v_x_2327_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_x_2326_, v_x_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___boxed(lean_object* v_00_u03b2_2329_, lean_object* v_x_2330_, lean_object* v_x_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4(v_00_u03b2_2329_, v_x_2330_, v_x_2331_);
lean_dec(v_x_2331_);
lean_dec_ref(v_x_2330_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2333_, lean_object* v_x_2334_, size_t v_x_2335_, size_t v_x_2336_, lean_object* v_x_2337_, lean_object* v_x_2338_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_2334_, v_x_2335_, v_x_2336_, v_x_2337_, v_x_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_, lean_object* v_x_2343_, lean_object* v_x_2344_, lean_object* v_x_2345_){
_start:
{
size_t v_x_2255__boxed_2346_; size_t v_x_2256__boxed_2347_; lean_object* v_res_2348_; 
v_x_2255__boxed_2346_ = lean_unbox_usize(v_x_2342_);
lean_dec(v_x_2342_);
v_x_2256__boxed_2347_ = lean_unbox_usize(v_x_2343_);
lean_dec(v_x_2343_);
v_res_2348_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(v_00_u03b2_2340_, v_x_2341_, v_x_2255__boxed_2346_, v_x_2256__boxed_2347_, v_x_2344_, v_x_2345_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2349_, lean_object* v_x_2350_, size_t v_x_2351_, lean_object* v_x_2352_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2350_, v_x_2351_, v_x_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2354_, lean_object* v_x_2355_, lean_object* v_x_2356_, lean_object* v_x_2357_){
_start:
{
size_t v_x_2272__boxed_2358_; lean_object* v_res_2359_; 
v_x_2272__boxed_2358_ = lean_unbox_usize(v_x_2356_);
lean_dec(v_x_2356_);
v_res_2359_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(v_00_u03b2_2354_, v_x_2355_, v_x_2272__boxed_2358_, v_x_2357_);
lean_dec_ref(v_x_2357_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(lean_object* v_00_u03b2_2360_, lean_object* v_x_2361_, size_t v_x_2362_, lean_object* v_x_2363_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_2361_, v_x_2362_, v_x_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2365_, lean_object* v_x_2366_, lean_object* v_x_2367_, lean_object* v_x_2368_){
_start:
{
size_t v_x_2283__boxed_2369_; lean_object* v_res_2370_; 
v_x_2283__boxed_2369_ = lean_unbox_usize(v_x_2367_);
lean_dec(v_x_2367_);
v_res_2370_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(v_00_u03b2_2365_, v_x_2366_, v_x_2283__boxed_2369_, v_x_2368_);
lean_dec_ref(v_x_2368_);
lean_dec_ref(v_x_2366_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(lean_object* v_00_u03b2_2371_, lean_object* v_x_2372_, size_t v_x_2373_, lean_object* v_x_2374_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_2372_, v_x_2373_, v_x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2376_, lean_object* v_x_2377_, lean_object* v_x_2378_, lean_object* v_x_2379_){
_start:
{
size_t v_x_2294__boxed_2380_; lean_object* v_res_2381_; 
v_x_2294__boxed_2380_ = lean_unbox_usize(v_x_2378_);
lean_dec(v_x_2378_);
v_res_2381_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(v_00_u03b2_2376_, v_x_2377_, v_x_2294__boxed_2380_, v_x_2379_);
lean_dec(v_x_2379_);
lean_dec_ref(v_x_2377_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2382_, lean_object* v_n_2383_, lean_object* v_k_2384_, lean_object* v_v_2385_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(v_n_2383_, v_k_2384_, v_v_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2387_, size_t v_depth_2388_, lean_object* v_keys_2389_, lean_object* v_vals_2390_, lean_object* v_heq_2391_, lean_object* v_i_2392_, lean_object* v_entries_2393_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_depth_2388_, v_keys_2389_, v_vals_2390_, v_i_2392_, v_entries_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2395_, lean_object* v_depth_2396_, lean_object* v_keys_2397_, lean_object* v_vals_2398_, lean_object* v_heq_2399_, lean_object* v_i_2400_, lean_object* v_entries_2401_){
_start:
{
size_t v_depth_boxed_2402_; lean_object* v_res_2403_; 
v_depth_boxed_2402_ = lean_unbox_usize(v_depth_2396_);
lean_dec(v_depth_2396_);
v_res_2403_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(v_00_u03b2_2395_, v_depth_boxed_2402_, v_keys_2397_, v_vals_2398_, v_heq_2399_, v_i_2400_, v_entries_2401_);
lean_dec_ref(v_vals_2398_);
lean_dec_ref(v_keys_2397_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12(lean_object* v_00_u03b2_2404_, lean_object* v_keys_2405_, lean_object* v_vals_2406_, lean_object* v_heq_2407_, lean_object* v_i_2408_, lean_object* v_k_2409_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_keys_2405_, v_vals_2406_, v_i_2408_, v_k_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___boxed(lean_object* v_00_u03b2_2411_, lean_object* v_keys_2412_, lean_object* v_vals_2413_, lean_object* v_heq_2414_, lean_object* v_i_2415_, lean_object* v_k_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12(v_00_u03b2_2411_, v_keys_2412_, v_vals_2413_, v_heq_2414_, v_i_2415_, v_k_2416_);
lean_dec_ref(v_k_2416_);
lean_dec_ref(v_vals_2413_);
lean_dec_ref(v_keys_2412_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15(lean_object* v_00_u03b2_2418_, lean_object* v_keys_2419_, lean_object* v_vals_2420_, lean_object* v_heq_2421_, lean_object* v_i_2422_, lean_object* v_k_2423_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_keys_2419_, v_vals_2420_, v_i_2422_, v_k_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___boxed(lean_object* v_00_u03b2_2425_, lean_object* v_keys_2426_, lean_object* v_vals_2427_, lean_object* v_heq_2428_, lean_object* v_i_2429_, lean_object* v_k_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15(v_00_u03b2_2425_, v_keys_2426_, v_vals_2427_, v_heq_2428_, v_i_2429_, v_k_2430_);
lean_dec(v_k_2430_);
lean_dec_ref(v_vals_2427_);
lean_dec_ref(v_keys_2426_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_2432_, lean_object* v_x_2433_, lean_object* v_x_2434_, lean_object* v_x_2435_, lean_object* v_x_2436_){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(v_x_2433_, v_x_2434_, v_x_2435_, v_x_2436_);
return v___x_2437_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__10));
v___x_2465_ = l_Lean_mkAtom(v___x_2464_);
return v___x_2465_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2466_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__12, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__12_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__12);
v___x_2467_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2468_ = lean_array_push(v___x_2467_, v___x_2466_);
return v___x_2468_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__17));
v___x_2478_ = l_Lean_mkAtom(v___x_2477_);
return v___x_2478_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__18, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__18_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__18);
v___x_2480_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2481_ = lean_array_push(v___x_2480_, v___x_2479_);
return v___x_2481_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__20(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2482_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__19, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__19_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__19);
v___x_2483_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__16));
v___x_2484_ = lean_box(2);
v___x_2485_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
lean_ctor_set(v___x_2485_, 1, v___x_2483_);
lean_ctor_set(v___x_2485_, 2, v___x_2482_);
return v___x_2485_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__21(void){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2486_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__20, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__20_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__20);
v___x_2487_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__13, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__13_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__13);
v___x_2488_ = lean_array_push(v___x_2487_, v___x_2486_);
return v___x_2488_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__22(void){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2489_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__21, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__21_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__21);
v___x_2490_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__11));
v___x_2491_ = lean_box(2);
v___x_2492_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
lean_ctor_set(v___x_2492_, 1, v___x_2490_);
lean_ctor_set(v___x_2492_, 2, v___x_2489_);
return v___x_2492_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2493_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__22, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__22_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__22);
v___x_2494_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2495_ = lean_array_push(v___x_2494_, v___x_2493_);
return v___x_2495_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2496_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__23, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__23_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__23);
v___x_2497_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__9));
v___x_2498_ = lean_box(2);
v___x_2499_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
lean_ctor_set(v___x_2499_, 1, v___x_2497_);
lean_ctor_set(v___x_2499_, 2, v___x_2496_);
return v___x_2499_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__25(void){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2500_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__24, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__24_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__24);
v___x_2501_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2502_ = lean_array_push(v___x_2501_, v___x_2500_);
return v___x_2502_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__26(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2503_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__25, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__25_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__25);
v___x_2504_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__7));
v___x_2505_ = lean_box(2);
v___x_2506_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
lean_ctor_set(v___x_2506_, 1, v___x_2504_);
lean_ctor_set(v___x_2506_, 2, v___x_2503_);
return v___x_2506_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__27(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__26, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__26_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__26);
v___x_2508_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2509_ = lean_array_push(v___x_2508_, v___x_2507_);
return v___x_2509_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__28(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2510_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__27, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__27_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__27);
v___x_2511_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__4));
v___x_2512_ = lean_box(2);
v___x_2513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
lean_ctor_set(v___x_2513_, 1, v___x_2511_);
lean_ctor_set(v___x_2513_, 2, v___x_2510_);
return v___x_2513_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1(void){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__28, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__28_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__28);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(lean_object* v_msg_2515_){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = lean_box(0);
v___x_2517_ = lean_panic_fn_borrowed(v___x_2516_, v_msg_2515_);
return v___x_2517_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2520_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2));
v___x_2521_ = lean_unsigned_to_nat(17u);
v___x_2522_ = lean_unsigned_to_nat(203u);
v___x_2523_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___lam__0___closed__1));
v___x_2524_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___lam__0___closed__0));
v___x_2525_ = l_mkPanicMessageWithDecl(v___x_2524_, v___x_2523_, v___x_2522_, v___x_2521_, v___x_2520_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__0(lean_object* v_x_2526_, lean_object* v_e_2527_){
_start:
{
lean_object* v___y_2529_; 
switch(lean_obj_tag(v_e_2527_))
{
case 3:
{
lean_object* v_thm_2536_; lean_object* v_origin_2537_; 
v_thm_2536_ = lean_ctor_get(v_e_2527_, 0);
v_origin_2537_ = lean_ctor_get(v_thm_2536_, 5);
if (lean_obj_tag(v_origin_2537_) == 0)
{
lean_object* v_declName_2538_; 
v_declName_2538_ = lean_ctor_get(v_origin_2537_, 0);
lean_inc(v_declName_2538_);
v___y_2529_ = v_declName_2538_;
goto v___jp_2528_;
}
else
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___lam__0___closed__2, &l_Lean_Meta_Grind_mkExtension___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2);
v___x_2540_ = l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(v___x_2539_);
v___y_2529_ = v___x_2540_;
goto v___jp_2528_;
}
}
case 4:
{
lean_object* v_thm_2541_; lean_object* v_origin_2542_; 
v_thm_2541_ = lean_ctor_get(v_e_2527_, 0);
v_origin_2542_ = lean_ctor_get(v_thm_2541_, 3);
if (lean_obj_tag(v_origin_2542_) == 0)
{
lean_object* v_declName_2543_; 
v_declName_2543_ = lean_ctor_get(v_origin_2542_, 0);
lean_inc(v_declName_2543_);
v___y_2529_ = v_declName_2543_;
goto v___jp_2528_;
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___lam__0___closed__2, &l_Lean_Meta_Grind_mkExtension___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2);
v___x_2545_ = l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(v___x_2544_);
v___y_2529_ = v___x_2545_;
goto v___jp_2528_;
}
}
default: 
{
lean_object* v_declName_2546_; 
v_declName_2546_ = lean_ctor_get(v_e_2527_, 0);
lean_inc(v_declName_2546_);
v___y_2529_ = v_declName_2546_;
goto v___jp_2528_;
}
}
v___jp_2528_:
{
uint8_t v___x_2530_; 
v___x_2530_ = l_Lean_isPrivateName(v___y_2529_);
lean_dec(v___y_2529_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2531_, 0, v_e_2527_);
lean_inc_ref_n(v___x_2531_, 2);
v___x_2532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
lean_ctor_set(v___x_2532_, 2, v___x_2531_);
return v___x_2532_;
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = lean_box(0);
v___x_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2534_, 0, v_e_2527_);
v___x_2535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2533_);
lean_ctor_set(v___x_2535_, 1, v___x_2533_);
lean_ctor_set(v___x_2535_, 2, v___x_2534_);
return v___x_2535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__0___boxed(lean_object* v_x_2547_, lean_object* v_e_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_Meta_Grind_mkExtension___lam__0(v_x_2547_, v_e_2548_);
lean_dec_ref(v_x_2547_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__1(lean_object* v___y_2550_){
_start:
{
lean_inc_ref(v___y_2550_);
return v___y_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__1___boxed(lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_Meta_Grind_mkExtension___lam__1(v___y_2551_);
lean_dec_ref(v___y_2551_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension(lean_object* v_name_2556_){
_start:
{
lean_object* v___f_2558_; lean_object* v___f_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___f_2558_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__0));
v___f_2559_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__1));
v___x_2560_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__2));
v___x_2561_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1);
v___x_2562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2562_, 0, v_name_2556_);
lean_ctor_set(v___x_2562_, 1, v___x_2560_);
lean_ctor_set(v___x_2562_, 2, v___x_2561_);
lean_ctor_set(v___x_2562_, 3, v___f_2559_);
lean_ctor_set(v___x_2562_, 4, v___f_2558_);
v___x_2563_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2562_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___boxed(lean_object* v_name_2564_, lean_object* v_a_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_Meta_Grind_mkExtension(v_name_2564_);
return v_res_2566_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0, &l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0);
v___x_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
return v___x_2568_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2569_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0);
v___x_2570_ = lean_unsigned_to_nat(0u);
v___x_2571_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
lean_ctor_set(v___x_2571_, 2, v___x_2570_);
lean_ctor_set(v___x_2571_, 3, v___x_2570_);
lean_ctor_set(v___x_2571_, 4, v___x_2569_);
lean_ctor_set(v___x_2571_, 5, v___x_2569_);
lean_ctor_set(v___x_2571_, 6, v___x_2569_);
lean_ctor_set(v___x_2571_, 7, v___x_2569_);
lean_ctor_set(v___x_2571_, 8, v___x_2569_);
lean_ctor_set(v___x_2571_, 9, v___x_2569_);
lean_ctor_set(v___x_2571_, 10, v___x_2569_);
return v___x_2571_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = lean_unsigned_to_nat(32u);
v___x_2573_ = lean_mk_empty_array_with_capacity(v___x_2572_);
v___x_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
return v___x_2574_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2575_ = ((size_t)5ULL);
v___x_2576_ = lean_unsigned_to_nat(0u);
v___x_2577_ = lean_unsigned_to_nat(32u);
v___x_2578_ = lean_mk_empty_array_with_capacity(v___x_2577_);
v___x_2579_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2);
v___x_2580_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v___x_2578_);
lean_ctor_set(v___x_2580_, 2, v___x_2576_);
lean_ctor_set(v___x_2580_, 3, v___x_2576_);
lean_ctor_set_usize(v___x_2580_, 4, v___x_2575_);
return v___x_2580_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2581_ = lean_box(1);
v___x_2582_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3);
v___x_2583_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0);
v___x_2584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v___x_2582_);
lean_ctor_set(v___x_2584_, 2, v___x_2581_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(lean_object* v_msgData_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v___x_2589_; lean_object* v_toCold_2590_; lean_object* v_env_2591_; lean_object* v_options_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2589_ = lean_st_ref_get(v___y_2587_);
v_toCold_2590_ = lean_ctor_get(v___y_2586_, 0);
v_env_2591_ = lean_ctor_get(v___x_2589_, 0);
lean_inc_ref(v_env_2591_);
lean_dec(v___x_2589_);
v_options_2592_ = lean_ctor_get(v_toCold_2590_, 2);
v___x_2593_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1);
v___x_2594_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4);
lean_inc_ref(v_options_2592_);
v___x_2595_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2595_, 0, v_env_2591_);
lean_ctor_set(v___x_2595_, 1, v___x_2593_);
lean_ctor_set(v___x_2595_, 2, v___x_2594_);
lean_ctor_set(v___x_2595_, 3, v_options_2592_);
v___x_2596_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
lean_ctor_set(v___x_2596_, 1, v_msgData_2585_);
v___x_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___boxed(lean_object* v_msgData_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(v_msgData_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(lean_object* v_msg_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v_ref_2607_; lean_object* v___x_2608_; lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2617_; 
v_ref_2607_ = lean_ctor_get(v___y_2604_, 2);
v___x_2608_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(v_msg_2603_, v___y_2604_, v___y_2605_);
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2617_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2617_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2613_; lean_object* v___x_2615_; 
lean_inc(v_ref_2607_);
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v_ref_2607_);
lean_ctor_set(v___x_2613_, 1, v_a_2609_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set_tag(v___x_2611_, 1);
lean_ctor_set(v___x_2611_, 0, v___x_2613_);
v___x_2615_ = v___x_2611_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2613_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg___boxed(lean_object* v_msg_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v_msg_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
return v_res_2622_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = ((lean_object*)(l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__0));
v___x_2625_ = l_Lean_stringToMessageData(v___x_2624_);
return v___x_2625_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = ((lean_object*)(l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__2));
v___x_2628_ = l_Lean_stringToMessageData(v___x_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object* v_declName_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
lean_object* v___x_2633_; uint8_t v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2633_ = lean_obj_once(&l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1, &l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1);
v___x_2634_ = 0;
v___x_2635_ = l_Lean_MessageData_ofConstName(v_declName_2629_, v___x_2634_);
v___x_2636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2633_);
lean_ctor_set(v___x_2636_, 1, v___x_2635_);
v___x_2637_ = lean_obj_once(&l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3, &l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3_once, _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3);
v___x_2638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2636_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
v___x_2639_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v___x_2638_, v_a_2630_, v_a_2631_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___boxed(lean_object* v_declName_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2640_, v_a_2641_, v_a_2642_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(lean_object* v_00_u03b1_2645_, lean_object* v_declName_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2646_, v_a_2647_, v_a_2648_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___boxed(lean_object* v_00_u03b1_2651_, lean_object* v_declName_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(v_00_u03b1_2651_, v_declName_2652_, v_a_2653_, v_a_2654_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(lean_object* v_00_u03b1_2657_, lean_object* v_msg_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v_msg_2658_, v___y_2659_, v___y_2660_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___boxed(lean_object* v_00_u03b1_2663_, lean_object* v_msg_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(v_00_u03b1_2663_, v_msg_2664_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
return v_res_2668_;
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
