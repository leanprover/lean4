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
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(lean_object* v_x_642_){
_start:
{
switch(lean_obj_tag(v_x_642_))
{
case 0:
{
uint8_t v_gen_643_; 
v_gen_643_ = lean_ctor_get_uint8(v_x_642_, 0);
if (v_gen_643_ == 0)
{
uint64_t v___x_644_; 
v___x_644_ = 2501231519204769793ULL;
return v___x_644_;
}
else
{
uint64_t v___x_645_; 
v___x_645_ = 10067447881416919396ULL;
return v___x_645_;
}
}
case 1:
{
uint8_t v_gen_646_; 
v_gen_646_ = lean_ctor_get_uint8(v_x_642_, 0);
if (v_gen_646_ == 0)
{
uint64_t v___x_647_; 
v___x_647_ = 6634225825881527916ULL;
return v___x_647_;
}
else
{
uint64_t v___x_648_; 
v___x_648_ = 5934453574740161273ULL;
return v___x_648_;
}
}
case 2:
{
uint8_t v_gen_649_; 
v_gen_649_ = lean_ctor_get_uint8(v_x_642_, 0);
if (v_gen_649_ == 0)
{
uint64_t v___x_650_; 
v___x_650_ = 12681986979560805163ULL;
return v___x_650_;
}
else
{
uint64_t v___x_651_; 
v___x_651_ = 1801459268063403150ULL;
return v___x_651_;
}
}
case 3:
{
uint64_t v___x_652_; 
v___x_652_ = 3ULL;
return v___x_652_;
}
case 4:
{
uint64_t v___x_653_; 
v___x_653_ = 4ULL;
return v___x_653_;
}
case 5:
{
uint8_t v_gen_654_; 
v_gen_654_ = lean_ctor_get_uint8(v_x_642_, 0);
if (v_gen_654_ == 0)
{
uint64_t v___x_655_; 
v___x_655_ = 4719458978879008792ULL;
return v___x_655_;
}
else
{
uint64_t v___x_656_; 
v___x_656_ = 4019686727737642149ULL;
return v___x_656_;
}
}
case 6:
{
uint64_t v___x_657_; 
v___x_657_ = 6ULL;
return v___x_657_;
}
case 7:
{
uint64_t v___x_658_; 
v___x_658_ = 7ULL;
return v___x_658_;
}
case 8:
{
uint8_t v_gen_659_; 
v_gen_659_ = lean_ctor_get_uint8(v_x_642_, 0);
if (v_gen_659_ == 0)
{
uint64_t v___x_660_; 
v___x_660_ = 17118441898909283161ULL;
return v___x_660_;
}
else
{
uint64_t v___x_661_; 
v___x_661_ = 13896981575421957644ULL;
return v___x_661_;
}
}
default: 
{
uint64_t v___x_662_; 
v___x_662_ = 9ULL;
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___boxed(lean_object* v_x_663_){
_start:
{
uint64_t v_res_664_; lean_object* v_r_665_; 
v_res_664_ = l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(v_x_663_);
lean_dec(v_x_663_);
v_r_665_ = lean_box_uint64(v_res_664_);
return v_r_665_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = lean_box(0);
v___x_674_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__2));
v___x_675_ = l_Lean_Expr_const___override(v___x_674_, v___x_673_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_676_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_677_ = lean_unsigned_to_nat(0u);
v___x_678_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_679_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___x_677_);
lean_ctor_set(v___x_679_, 2, v___x_676_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default(void){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4);
return v___x_680_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS(void){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default;
return v___x_681_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(lean_object* v_xs_682_, lean_object* v_ys_683_, lean_object* v_x_684_){
_start:
{
lean_object* v_zero_685_; uint8_t v_isZero_686_; 
v_zero_685_ = lean_unsigned_to_nat(0u);
v_isZero_686_ = lean_nat_dec_eq(v_x_684_, v_zero_685_);
if (v_isZero_686_ == 1)
{
lean_dec(v_x_684_);
return v_isZero_686_;
}
else
{
lean_object* v_one_687_; lean_object* v_n_688_; lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v_one_687_ = lean_unsigned_to_nat(1u);
v_n_688_ = lean_nat_sub(v_x_684_, v_one_687_);
lean_dec(v_x_684_);
v___x_689_ = lean_array_fget_borrowed(v_xs_682_, v_n_688_);
v___x_690_ = lean_array_fget_borrowed(v_ys_683_, v_n_688_);
v___x_691_ = lean_name_eq(v___x_689_, v___x_690_);
if (v___x_691_ == 0)
{
lean_dec(v_n_688_);
return v___x_691_;
}
else
{
v_x_684_ = v_n_688_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg___boxed(lean_object* v_xs_693_, lean_object* v_ys_694_, lean_object* v_x_695_){
_start:
{
uint8_t v_res_696_; lean_object* v_r_697_; 
v_res_696_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_xs_693_, v_ys_694_, v_x_695_);
lean_dec_ref(v_ys_694_);
lean_dec_ref(v_xs_693_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqCnstrRHS_beq(lean_object* v_x_698_, lean_object* v_x_699_){
_start:
{
lean_object* v_levelNames_700_; lean_object* v_numMVars_701_; lean_object* v_expr_702_; lean_object* v_levelNames_703_; lean_object* v_numMVars_704_; lean_object* v_expr_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v_levelNames_700_ = lean_ctor_get(v_x_698_, 0);
v_numMVars_701_ = lean_ctor_get(v_x_698_, 1);
v_expr_702_ = lean_ctor_get(v_x_698_, 2);
v_levelNames_703_ = lean_ctor_get(v_x_699_, 0);
v_numMVars_704_ = lean_ctor_get(v_x_699_, 1);
v_expr_705_ = lean_ctor_get(v_x_699_, 2);
v___x_706_ = lean_array_get_size(v_levelNames_700_);
v___x_707_ = lean_array_get_size(v_levelNames_703_);
v___x_708_ = lean_nat_dec_eq(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
return v___x_708_;
}
else
{
uint8_t v___x_709_; 
v___x_709_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_levelNames_700_, v_levelNames_703_, v___x_706_);
if (v___x_709_ == 0)
{
return v___x_709_;
}
else
{
uint8_t v___x_710_; 
v___x_710_ = lean_nat_dec_eq(v_numMVars_701_, v_numMVars_704_);
if (v___x_710_ == 0)
{
return v___x_710_;
}
else
{
uint8_t v___x_711_; 
v___x_711_ = lean_expr_eqv(v_expr_702_, v_expr_705_);
return v___x_711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqCnstrRHS_beq___boxed(lean_object* v_x_712_, lean_object* v_x_713_){
_start:
{
uint8_t v_res_714_; lean_object* v_r_715_; 
v_res_714_ = l_Lean_Meta_Grind_instBEqCnstrRHS_beq(v_x_712_, v_x_713_);
lean_dec_ref(v_x_713_);
lean_dec_ref(v_x_712_);
v_r_715_ = lean_box(v_res_714_);
return v_r_715_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(lean_object* v_xs_716_, lean_object* v_ys_717_, lean_object* v_hsz_718_, lean_object* v_x_719_, lean_object* v_x_720_){
_start:
{
uint8_t v___x_721_; 
v___x_721_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_xs_716_, v_ys_717_, v_x_719_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___boxed(lean_object* v_xs_722_, lean_object* v_ys_723_, lean_object* v_hsz_724_, lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
uint8_t v_res_727_; lean_object* v_r_728_; 
v_res_727_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(v_xs_722_, v_ys_723_, v_hsz_724_, v_x_725_, v_x_726_);
lean_dec_ref(v_ys_723_);
lean_dec_ref(v_xs_722_);
v_r_728_ = lean_box(v_res_727_);
return v_r_728_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__1(lean_object* v_a_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = lean_nat_to_int(v_a_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
if (lean_obj_tag(v_x_735_) == 0)
{
lean_dec(v_x_733_);
return v_x_734_;
}
else
{
lean_object* v_head_736_; lean_object* v_tail_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_748_; 
v_head_736_ = lean_ctor_get(v_x_735_, 0);
v_tail_737_ = lean_ctor_get(v_x_735_, 1);
v_isSharedCheck_748_ = !lean_is_exclusive(v_x_735_);
if (v_isSharedCheck_748_ == 0)
{
v___x_739_ = v_x_735_;
v_isShared_740_ = v_isSharedCheck_748_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_tail_737_);
lean_inc(v_head_736_);
lean_dec(v_x_735_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_748_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
lean_inc(v_x_733_);
if (v_isShared_740_ == 0)
{
lean_ctor_set_tag(v___x_739_, 5);
lean_ctor_set(v___x_739_, 1, v_x_733_);
lean_ctor_set(v___x_739_, 0, v_x_734_);
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_x_734_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_x_733_);
v___x_742_ = v_reuseFailAlloc_747_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = l_Lean_Name_reprPrec(v_head_736_, v___x_743_);
v___x_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_742_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v_x_734_ = v___x_745_;
v_x_735_ = v_tail_737_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2(lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
if (lean_obj_tag(v_x_751_) == 0)
{
lean_dec(v_x_749_);
return v_x_750_;
}
else
{
lean_object* v_head_752_; lean_object* v_tail_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_764_; 
v_head_752_ = lean_ctor_get(v_x_751_, 0);
v_tail_753_ = lean_ctor_get(v_x_751_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_764_ == 0)
{
v___x_755_ = v_x_751_;
v_isShared_756_ = v_isSharedCheck_764_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_tail_753_);
lean_inc(v_head_752_);
lean_dec(v_x_751_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_764_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
lean_inc(v_x_749_);
if (v_isShared_756_ == 0)
{
lean_ctor_set_tag(v___x_755_, 5);
lean_ctor_set(v___x_755_, 1, v_x_749_);
lean_ctor_set(v___x_755_, 0, v_x_750_);
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_x_750_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_x_749_);
v___x_758_ = v_reuseFailAlloc_763_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = l_Lean_Name_reprPrec(v_head_752_, v___x_759_);
v___x_761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_758_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2_spec__3(v_x_749_, v___x_761_, v_tail_753_);
return v___x_762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(lean_object* v___y_765_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = l_Lean_Name_reprPrec(v___y_765_, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0(lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
if (lean_obj_tag(v_x_768_) == 0)
{
lean_object* v___x_770_; 
lean_dec(v_x_769_);
v___x_770_ = lean_box(0);
return v___x_770_;
}
else
{
lean_object* v_tail_771_; 
v_tail_771_ = lean_ctor_get(v_x_768_, 1);
if (lean_obj_tag(v_tail_771_) == 0)
{
lean_object* v_head_772_; lean_object* v___x_773_; 
lean_dec(v_x_769_);
v_head_772_ = lean_ctor_get(v_x_768_, 0);
lean_inc(v_head_772_);
lean_dec_ref_known(v_x_768_, 2);
v___x_773_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(v_head_772_);
return v___x_773_;
}
else
{
lean_object* v_head_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
lean_inc(v_tail_771_);
v_head_774_ = lean_ctor_get(v_x_768_, 0);
lean_inc(v_head_774_);
lean_dec_ref_known(v_x_768_, 2);
v___x_775_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(v_head_774_);
v___x_776_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2(v_x_769_, v___x_775_, v_tail_771_);
return v___x_776_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0));
v___x_786_ = lean_string_length(v___x_785_);
return v___x_786_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5);
v___x_788_ = lean_nat_to_int(v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0(lean_object* v_xs_796_){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_797_ = lean_array_get_size(v_xs_796_);
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_nat_dec_eq(v___x_797_, v___x_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_800_ = lean_array_to_list(v_xs_796_);
v___x_801_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__3));
v___x_802_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0(v___x_800_, v___x_801_);
v___x_803_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6);
v___x_804_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__7));
v___x_805_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v___x_802_);
v___x_806_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__8));
v___x_807_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_805_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_803_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = l_Std_Format_fill(v___x_808_);
return v___x_809_;
}
else
{
lean_object* v___x_810_; 
lean_dec_ref(v_xs_796_);
v___x_810_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__10));
return v___x_810_;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_unsigned_to_nat(14u);
v___x_825_ = lean_nat_to_int(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_unsigned_to_nat(12u);
v___x_830_ = lean_nat_to_int(v___x_829_);
return v___x_830_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_unsigned_to_nat(8u);
v___x_835_ = lean_nat_to_int(v___x_834_);
return v___x_835_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0));
v___x_838_ = lean_string_length(v___x_837_);
return v___x_838_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15);
v___x_840_ = lean_nat_to_int(v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(lean_object* v_x_845_){
_start:
{
lean_object* v_levelNames_846_; lean_object* v_numMVars_847_; lean_object* v_expr_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_levelNames_846_ = lean_ctor_get(v_x_845_, 0);
lean_inc_ref(v_levelNames_846_);
v_numMVars_847_ = lean_ctor_get(v_x_845_, 1);
lean_inc(v_numMVars_847_);
v_expr_848_ = lean_ctor_get(v_x_845_, 2);
lean_inc_ref(v_expr_848_);
lean_dec_ref(v_x_845_);
v___x_849_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5));
v___x_850_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__6));
v___x_851_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7);
v___x_852_ = l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0(v_levelNames_846_);
v___x_853_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = 0;
v___x_855_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*1, v___x_854_);
v___x_856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_850_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2));
v___x_858_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = lean_box(1);
v___x_860_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_858_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__9));
v___x_862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
lean_ctor_set(v___x_863_, 1, v___x_849_);
v___x_864_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10);
v___x_865_ = l_Nat_reprFast(v_numMVars_847_);
v___x_866_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
v___x_867_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_864_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_868_, 0, v___x_867_);
lean_ctor_set_uint8(v___x_868_, sizeof(void*)*1, v___x_854_);
v___x_869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_863_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v___x_857_);
v___x_871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_859_);
v___x_872_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__12));
v___x_873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set(v___x_874_, 1, v___x_849_);
v___x_875_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13);
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = l_Lean_instReprExpr_repr(v_expr_848_, v___x_876_);
v___x_878_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_875_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_ctor_set_uint8(v___x_879_, sizeof(void*)*1, v___x_854_);
v___x_880_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_874_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16);
v___x_882_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__17));
v___x_883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v___x_880_);
v___x_884_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__18));
v___x_885_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_881_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set_uint8(v___x_887_, sizeof(void*)*1, v___x_854_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr(lean_object* v_x_888_, lean_object* v_prec_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_x_888_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___boxed(lean_object* v_x_891_, lean_object* v_prec_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr(v_x_891_, v_prec_892_);
lean_dec(v_prec_892_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(lean_object* v_x_896_){
_start:
{
switch(lean_obj_tag(v_x_896_))
{
case 0:
{
lean_object* v___x_897_; 
v___x_897_ = lean_unsigned_to_nat(0u);
return v___x_897_;
}
case 1:
{
lean_object* v___x_898_; 
v___x_898_ = lean_unsigned_to_nat(1u);
return v___x_898_;
}
case 2:
{
lean_object* v___x_899_; 
v___x_899_ = lean_unsigned_to_nat(2u);
return v___x_899_;
}
case 3:
{
lean_object* v___x_900_; 
v___x_900_ = lean_unsigned_to_nat(3u);
return v___x_900_;
}
case 4:
{
lean_object* v___x_901_; 
v___x_901_ = lean_unsigned_to_nat(4u);
return v___x_901_;
}
case 5:
{
lean_object* v___x_902_; 
v___x_902_ = lean_unsigned_to_nat(5u);
return v___x_902_;
}
case 6:
{
lean_object* v___x_903_; 
v___x_903_ = lean_unsigned_to_nat(6u);
return v___x_903_;
}
case 7:
{
lean_object* v___x_904_; 
v___x_904_ = lean_unsigned_to_nat(7u);
return v___x_904_;
}
case 8:
{
lean_object* v___x_905_; 
v___x_905_ = lean_unsigned_to_nat(8u);
return v___x_905_;
}
case 9:
{
lean_object* v___x_906_; 
v___x_906_ = lean_unsigned_to_nat(9u);
return v___x_906_;
}
default: 
{
lean_object* v___x_907_; 
v___x_907_ = lean_unsigned_to_nat(10u);
return v___x_907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx___boxed(lean_object* v_x_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_908_);
lean_dec_ref(v_x_908_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(lean_object* v_t_910_, lean_object* v_k_911_){
_start:
{
switch(lean_obj_tag(v_t_910_))
{
case 0:
{
lean_object* v_lhs_912_; lean_object* v_rhs_913_; lean_object* v___x_914_; 
v_lhs_912_ = lean_ctor_get(v_t_910_, 0);
lean_inc(v_lhs_912_);
v_rhs_913_ = lean_ctor_get(v_t_910_, 1);
lean_inc_ref(v_rhs_913_);
lean_dec_ref_known(v_t_910_, 2);
v___x_914_ = lean_apply_2(v_k_911_, v_lhs_912_, v_rhs_913_);
return v___x_914_;
}
case 1:
{
lean_object* v_lhs_915_; lean_object* v_rhs_916_; lean_object* v___x_917_; 
v_lhs_915_ = lean_ctor_get(v_t_910_, 0);
lean_inc(v_lhs_915_);
v_rhs_916_ = lean_ctor_get(v_t_910_, 1);
lean_inc_ref(v_rhs_916_);
lean_dec_ref_known(v_t_910_, 2);
v___x_917_ = lean_apply_2(v_k_911_, v_lhs_915_, v_rhs_916_);
return v___x_917_;
}
case 2:
{
lean_object* v_lhs_918_; lean_object* v_n_919_; lean_object* v___x_920_; 
v_lhs_918_ = lean_ctor_get(v_t_910_, 0);
lean_inc(v_lhs_918_);
v_n_919_ = lean_ctor_get(v_t_910_, 1);
lean_inc(v_n_919_);
lean_dec_ref_known(v_t_910_, 2);
v___x_920_ = lean_apply_2(v_k_911_, v_lhs_918_, v_n_919_);
return v___x_920_;
}
case 3:
{
lean_object* v_lhs_921_; lean_object* v_n_922_; lean_object* v___x_923_; 
v_lhs_921_ = lean_ctor_get(v_t_910_, 0);
lean_inc(v_lhs_921_);
v_n_922_ = lean_ctor_get(v_t_910_, 1);
lean_inc(v_n_922_);
lean_dec_ref_known(v_t_910_, 2);
v___x_923_ = lean_apply_2(v_k_911_, v_lhs_921_, v_n_922_);
return v___x_923_;
}
case 6:
{
lean_object* v_bvarIdx_924_; uint8_t v_strict_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_bvarIdx_924_ = lean_ctor_get(v_t_910_, 0);
lean_inc(v_bvarIdx_924_);
v_strict_925_ = lean_ctor_get_uint8(v_t_910_, sizeof(void*)*1);
lean_dec_ref_known(v_t_910_, 1);
v___x_926_ = lean_box(v_strict_925_);
v___x_927_ = lean_apply_2(v_k_911_, v_bvarIdx_924_, v___x_926_);
return v___x_927_;
}
case 8:
{
lean_object* v_e_928_; lean_object* v___x_929_; 
v_e_928_ = lean_ctor_get(v_t_910_, 0);
lean_inc_ref(v_e_928_);
lean_dec_ref_known(v_t_910_, 1);
v___x_929_ = lean_apply_1(v_k_911_, v_e_928_);
return v___x_929_;
}
case 9:
{
lean_object* v_e_930_; lean_object* v___x_931_; 
v_e_930_ = lean_ctor_get(v_t_910_, 0);
lean_inc_ref(v_e_930_);
lean_dec_ref_known(v_t_910_, 1);
v___x_931_ = lean_apply_1(v_k_911_, v_e_930_);
return v___x_931_;
}
case 10:
{
lean_object* v_bvarIdx_932_; uint8_t v_strict_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_bvarIdx_932_ = lean_ctor_get(v_t_910_, 0);
lean_inc(v_bvarIdx_932_);
v_strict_933_ = lean_ctor_get_uint8(v_t_910_, sizeof(void*)*1);
lean_dec_ref_known(v_t_910_, 1);
v___x_934_ = lean_box(v_strict_933_);
v___x_935_ = lean_apply_2(v_k_911_, v_bvarIdx_932_, v___x_934_);
return v___x_935_;
}
default: 
{
lean_object* v_n_936_; lean_object* v___x_937_; 
v_n_936_ = lean_ctor_get(v_t_910_, 0);
lean_inc(v_n_936_);
lean_dec_ref(v_t_910_);
v___x_937_ = lean_apply_1(v_k_911_, v_n_936_);
return v___x_937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim(lean_object* v_motive_938_, lean_object* v_ctorIdx_939_, lean_object* v_t_940_, lean_object* v_h_941_, lean_object* v_k_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_940_, v_k_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___boxed(lean_object* v_motive_944_, lean_object* v_ctorIdx_945_, lean_object* v_t_946_, lean_object* v_h_947_, lean_object* v_k_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim(v_motive_944_, v_ctorIdx_945_, v_t_946_, v_h_947_, v_k_948_);
lean_dec(v_ctorIdx_945_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim___redArg(lean_object* v_t_950_, lean_object* v_notDefEq_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_950_, v_notDefEq_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim(lean_object* v_motive_953_, lean_object* v_t_954_, lean_object* v_h_955_, lean_object* v_notDefEq_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_954_, v_notDefEq_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim___redArg(lean_object* v_t_958_, lean_object* v_defEq_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_958_, v_defEq_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim(lean_object* v_motive_961_, lean_object* v_t_962_, lean_object* v_h_963_, lean_object* v_defEq_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_962_, v_defEq_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim___redArg(lean_object* v_t_966_, lean_object* v_sizeLt_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_966_, v_sizeLt_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim(lean_object* v_motive_969_, lean_object* v_t_970_, lean_object* v_h_971_, lean_object* v_sizeLt_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_970_, v_sizeLt_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim___redArg(lean_object* v_t_974_, lean_object* v_depthLt_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_974_, v_depthLt_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim(lean_object* v_motive_977_, lean_object* v_t_978_, lean_object* v_h_979_, lean_object* v_depthLt_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_978_, v_depthLt_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim___redArg(lean_object* v_t_982_, lean_object* v_genLt_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_982_, v_genLt_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim(lean_object* v_motive_985_, lean_object* v_t_986_, lean_object* v_h_987_, lean_object* v_genLt_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_986_, v_genLt_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim___redArg(lean_object* v_t_990_, lean_object* v_isGround_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_990_, v_isGround_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim(lean_object* v_motive_993_, lean_object* v_t_994_, lean_object* v_h_995_, lean_object* v_isGround_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_994_, v_isGround_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim___redArg(lean_object* v_t_998_, lean_object* v_isValue_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_998_, v_isValue_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim(lean_object* v_motive_1001_, lean_object* v_t_1002_, lean_object* v_h_1003_, lean_object* v_isValue_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1002_, v_isValue_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim___redArg(lean_object* v_t_1006_, lean_object* v_maxInsts_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1006_, v_maxInsts_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim(lean_object* v_motive_1009_, lean_object* v_t_1010_, lean_object* v_h_1011_, lean_object* v_maxInsts_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1010_, v_maxInsts_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim___redArg(lean_object* v_t_1014_, lean_object* v_guard_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1014_, v_guard_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim(lean_object* v_motive_1017_, lean_object* v_t_1018_, lean_object* v_h_1019_, lean_object* v_guard_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1018_, v_guard_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim___redArg(lean_object* v_t_1022_, lean_object* v_check_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1022_, v_check_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim(lean_object* v_motive_1025_, lean_object* v_t_1026_, lean_object* v_h_1027_, lean_object* v_check_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1026_, v_check_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim___redArg(lean_object* v_t_1030_, lean_object* v_notValue_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1030_, v_notValue_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim(lean_object* v_motive_1033_, lean_object* v_t_1034_, lean_object* v_h_1035_, lean_object* v_notValue_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1034_, v_notValue_1036_);
return v___x_1037_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default;
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v___x_1038_);
return v___x_1040_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default(void){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0, &l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0);
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint(void){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default;
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr(lean_object* v_x_1109_, lean_object* v_prec_1110_){
_start:
{
switch(lean_obj_tag(v_x_1109_))
{
case 0:
{
lean_object* v_lhs_1111_; lean_object* v_rhs_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1136_; 
v_lhs_1111_ = lean_ctor_get(v_x_1109_, 0);
v_rhs_1112_ = lean_ctor_get(v_x_1109_, 1);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_x_1109_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1114_ = v_x_1109_;
v_isShared_1115_ = v_isSharedCheck_1136_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_rhs_1112_);
lean_inc(v_lhs_1111_);
lean_dec(v_x_1109_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1136_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___y_1117_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = lean_unsigned_to_nat(1024u);
v___x_1133_ = lean_nat_dec_le(v___x_1132_, v_prec_1110_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1117_ = v___x_1134_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1117_ = v___x_1135_;
goto v___jp_1116_;
}
v___jp_1116_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1118_ = lean_box(1);
v___x_1119_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__2));
v___x_1120_ = l_Nat_reprFast(v_lhs_1111_);
v___x_1121_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set_tag(v___x_1114_, 5);
lean_ctor_set(v___x_1114_, 1, v___x_1121_);
lean_ctor_set(v___x_1114_, 0, v___x_1119_);
v___x_1123_ = v___x_1114_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
lean_ctor_set(v___x_1124_, 1, v___x_1118_);
v___x_1125_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_rhs_1112_);
v___x_1126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
lean_inc(v___y_1117_);
v___x_1127_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___y_1117_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = 0;
v___x_1129_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*1, v___x_1128_);
v___x_1130_ = l_Repr_addAppParen(v___x_1129_, v_prec_1110_);
return v___x_1130_;
}
}
}
}
case 1:
{
lean_object* v_lhs_1137_; lean_object* v_rhs_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1162_; 
v_lhs_1137_ = lean_ctor_get(v_x_1109_, 0);
v_rhs_1138_ = lean_ctor_get(v_x_1109_, 1);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_x_1109_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1140_ = v_x_1109_;
v_isShared_1141_ = v_isSharedCheck_1162_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_rhs_1138_);
lean_inc(v_lhs_1137_);
lean_dec(v_x_1109_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1162_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___y_1143_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = lean_unsigned_to_nat(1024u);
v___x_1159_ = lean_nat_dec_le(v___x_1158_, v_prec_1110_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1143_ = v___x_1160_;
goto v___jp_1142_;
}
else
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1143_ = v___x_1161_;
goto v___jp_1142_;
}
v___jp_1142_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1144_ = lean_box(1);
v___x_1145_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__5));
v___x_1146_ = l_Nat_reprFast(v_lhs_1137_);
v___x_1147_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set_tag(v___x_1140_, 5);
lean_ctor_set(v___x_1140_, 1, v___x_1147_);
lean_ctor_set(v___x_1140_, 0, v___x_1145_);
v___x_1149_ = v___x_1140_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
lean_ctor_set(v___x_1150_, 1, v___x_1144_);
v___x_1151_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_rhs_1138_);
v___x_1152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
lean_inc(v___y_1143_);
v___x_1153_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___y_1143_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = 0;
v___x_1155_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*1, v___x_1154_);
v___x_1156_ = l_Repr_addAppParen(v___x_1155_, v_prec_1110_);
return v___x_1156_;
}
}
}
}
case 2:
{
lean_object* v_lhs_1163_; lean_object* v_n_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1189_; 
v_lhs_1163_ = lean_ctor_get(v_x_1109_, 0);
v_n_1164_ = lean_ctor_get(v_x_1109_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_x_1109_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1166_ = v_x_1109_;
v_isShared_1167_ = v_isSharedCheck_1189_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_n_1164_);
lean_inc(v_lhs_1163_);
lean_dec(v_x_1109_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1189_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___y_1169_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = lean_unsigned_to_nat(1024u);
v___x_1186_ = lean_nat_dec_le(v___x_1185_, v_prec_1110_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1169_ = v___x_1187_;
goto v___jp_1168_;
}
else
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1169_ = v___x_1188_;
goto v___jp_1168_;
}
v___jp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1170_ = lean_box(1);
v___x_1171_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__8));
v___x_1172_ = l_Nat_reprFast(v_lhs_1163_);
v___x_1173_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set_tag(v___x_1166_, 5);
lean_ctor_set(v___x_1166_, 1, v___x_1173_);
lean_ctor_set(v___x_1166_, 0, v___x_1171_);
v___x_1175_ = v___x_1166_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v___x_1170_);
v___x_1177_ = l_Nat_reprFast(v_n_1164_);
v___x_1178_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
v___x_1179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1176_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
lean_inc(v___y_1169_);
v___x_1180_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___y_1169_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = 0;
v___x_1182_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*1, v___x_1181_);
v___x_1183_ = l_Repr_addAppParen(v___x_1182_, v_prec_1110_);
return v___x_1183_;
}
}
}
}
case 3:
{
lean_object* v_lhs_1190_; lean_object* v_n_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1216_; 
v_lhs_1190_ = lean_ctor_get(v_x_1109_, 0);
v_n_1191_ = lean_ctor_get(v_x_1109_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_x_1109_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1193_ = v_x_1109_;
v_isShared_1194_ = v_isSharedCheck_1216_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_n_1191_);
lean_inc(v_lhs_1190_);
lean_dec(v_x_1109_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1216_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___y_1196_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = lean_unsigned_to_nat(1024u);
v___x_1213_ = lean_nat_dec_le(v___x_1212_, v_prec_1110_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1196_ = v___x_1214_;
goto v___jp_1195_;
}
else
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1196_ = v___x_1215_;
goto v___jp_1195_;
}
v___jp_1195_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1197_ = lean_box(1);
v___x_1198_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__11));
v___x_1199_ = l_Nat_reprFast(v_lhs_1190_);
v___x_1200_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set_tag(v___x_1193_, 5);
lean_ctor_set(v___x_1193_, 1, v___x_1200_);
lean_ctor_set(v___x_1193_, 0, v___x_1198_);
v___x_1202_ = v___x_1193_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
lean_ctor_set(v___x_1203_, 1, v___x_1197_);
v___x_1204_ = l_Nat_reprFast(v_n_1191_);
v___x_1205_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1203_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
lean_inc(v___y_1196_);
v___x_1207_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___y_1196_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = 0;
v___x_1209_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set_uint8(v___x_1209_, sizeof(void*)*1, v___x_1208_);
v___x_1210_ = l_Repr_addAppParen(v___x_1209_, v_prec_1110_);
return v___x_1210_;
}
}
}
}
case 4:
{
lean_object* v_n_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1237_; 
v_n_1217_ = lean_ctor_get(v_x_1109_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_x_1109_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1219_ = v_x_1109_;
v_isShared_1220_ = v_isSharedCheck_1237_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_n_1217_);
lean_dec(v_x_1109_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1237_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___y_1222_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_unsigned_to_nat(1024u);
v___x_1234_ = lean_nat_dec_le(v___x_1233_, v_prec_1110_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1222_ = v___x_1235_;
goto v___jp_1221_;
}
else
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1222_ = v___x_1236_;
goto v___jp_1221_;
}
v___jp_1221_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1223_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__14));
v___x_1224_ = l_Nat_reprFast(v_n_1217_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set_tag(v___x_1219_, 3);
lean_ctor_set(v___x_1219_, 0, v___x_1224_);
v___x_1226_ = v___x_1219_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1223_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
lean_inc(v___y_1222_);
v___x_1228_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___y_1222_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = 0;
v___x_1230_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1230_, 0, v___x_1228_);
lean_ctor_set_uint8(v___x_1230_, sizeof(void*)*1, v___x_1229_);
v___x_1231_ = l_Repr_addAppParen(v___x_1230_, v_prec_1110_);
return v___x_1231_;
}
}
}
}
case 5:
{
lean_object* v_bvarIdx_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1258_; 
v_bvarIdx_1238_ = lean_ctor_get(v_x_1109_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_x_1109_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1240_ = v_x_1109_;
v_isShared_1241_ = v_isSharedCheck_1258_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_bvarIdx_1238_);
lean_dec(v_x_1109_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1258_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___y_1243_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = lean_unsigned_to_nat(1024u);
v___x_1255_ = lean_nat_dec_le(v___x_1254_, v_prec_1110_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1243_ = v___x_1256_;
goto v___jp_1242_;
}
else
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1243_ = v___x_1257_;
goto v___jp_1242_;
}
v___jp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1244_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__17));
v___x_1245_ = l_Nat_reprFast(v_bvarIdx_1238_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set_tag(v___x_1240_, 3);
lean_ctor_set(v___x_1240_, 0, v___x_1245_);
v___x_1247_ = v___x_1240_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1244_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
lean_inc(v___y_1243_);
v___x_1249_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___y_1243_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = 0;
v___x_1251_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set_uint8(v___x_1251_, sizeof(void*)*1, v___x_1250_);
v___x_1252_ = l_Repr_addAppParen(v___x_1251_, v_prec_1110_);
return v___x_1252_;
}
}
}
}
case 6:
{
lean_object* v_bvarIdx_1259_; uint8_t v_strict_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1284_; 
v_bvarIdx_1259_ = lean_ctor_get(v_x_1109_, 0);
v_strict_1260_ = lean_ctor_get_uint8(v_x_1109_, sizeof(void*)*1);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_x_1109_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1262_ = v_x_1109_;
v_isShared_1263_ = v_isSharedCheck_1284_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_bvarIdx_1259_);
lean_dec(v_x_1109_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1284_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___y_1265_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = lean_unsigned_to_nat(1024u);
v___x_1281_ = lean_nat_dec_le(v___x_1280_, v_prec_1110_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1265_ = v___x_1282_;
goto v___jp_1264_;
}
else
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1265_ = v___x_1283_;
goto v___jp_1264_;
}
v___jp_1264_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; lean_object* v___x_1277_; 
v___x_1266_ = lean_box(1);
v___x_1267_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__20));
v___x_1268_ = l_Nat_reprFast(v_bvarIdx_1259_);
v___x_1269_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
v___x_1270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1267_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v___x_1266_);
v___x_1272_ = l_Bool_repr___redArg(v_strict_1260_);
v___x_1273_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1271_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
lean_inc(v___y_1265_);
v___x_1274_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___y_1265_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = 0;
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1274_);
v___x_1277_ = v___x_1262_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1274_);
v___x_1277_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1278_; 
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*1, v___x_1275_);
v___x_1278_ = l_Repr_addAppParen(v___x_1277_, v_prec_1110_);
return v___x_1278_;
}
}
}
}
case 7:
{
lean_object* v_n_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1305_; 
v_n_1285_ = lean_ctor_get(v_x_1109_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_x_1109_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1287_ = v_x_1109_;
v_isShared_1288_ = v_isSharedCheck_1305_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_n_1285_);
lean_dec(v_x_1109_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1305_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___y_1290_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = lean_unsigned_to_nat(1024u);
v___x_1302_ = lean_nat_dec_le(v___x_1301_, v_prec_1110_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1290_ = v___x_1303_;
goto v___jp_1289_;
}
else
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1290_ = v___x_1304_;
goto v___jp_1289_;
}
v___jp_1289_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1291_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__23));
v___x_1292_ = l_Nat_reprFast(v_n_1285_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set_tag(v___x_1287_, 3);
lean_ctor_set(v___x_1287_, 0, v___x_1292_);
v___x_1294_ = v___x_1287_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1291_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
lean_inc(v___y_1290_);
v___x_1296_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___y_1290_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = 0;
v___x_1298_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1298_, 0, v___x_1296_);
lean_ctor_set_uint8(v___x_1298_, sizeof(void*)*1, v___x_1297_);
v___x_1299_ = l_Repr_addAppParen(v___x_1298_, v_prec_1110_);
return v___x_1299_;
}
}
}
}
case 8:
{
lean_object* v_e_1306_; lean_object* v___y_1308_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v_e_1306_ = lean_ctor_get(v_x_1109_, 0);
lean_inc_ref(v_e_1306_);
lean_dec_ref_known(v_x_1109_, 1);
v___x_1317_ = lean_unsigned_to_nat(1024u);
v___x_1318_ = lean_nat_dec_le(v___x_1317_, v_prec_1110_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
v___x_1319_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1308_ = v___x_1319_;
goto v___jp_1307_;
}
else
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1308_ = v___x_1320_;
goto v___jp_1307_;
}
v___jp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1309_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__26));
v___x_1310_ = lean_unsigned_to_nat(1024u);
v___x_1311_ = l_Lean_instReprExpr_repr(v_e_1306_, v___x_1310_);
v___x_1312_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1309_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
lean_inc(v___y_1308_);
v___x_1313_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___y_1308_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = 0;
v___x_1315_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*1, v___x_1314_);
v___x_1316_ = l_Repr_addAppParen(v___x_1315_, v_prec_1110_);
return v___x_1316_;
}
}
case 9:
{
lean_object* v_e_1321_; lean_object* v___y_1323_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v_e_1321_ = lean_ctor_get(v_x_1109_, 0);
lean_inc_ref(v_e_1321_);
lean_dec_ref_known(v_x_1109_, 1);
v___x_1332_ = lean_unsigned_to_nat(1024u);
v___x_1333_ = lean_nat_dec_le(v___x_1332_, v_prec_1110_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1323_ = v___x_1334_;
goto v___jp_1322_;
}
else
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1323_ = v___x_1335_;
goto v___jp_1322_;
}
v___jp_1322_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1324_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__29));
v___x_1325_ = lean_unsigned_to_nat(1024u);
v___x_1326_ = l_Lean_instReprExpr_repr(v_e_1321_, v___x_1325_);
v___x_1327_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1324_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
lean_inc(v___y_1323_);
v___x_1328_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___y_1323_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = 0;
v___x_1330_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set_uint8(v___x_1330_, sizeof(void*)*1, v___x_1329_);
v___x_1331_ = l_Repr_addAppParen(v___x_1330_, v_prec_1110_);
return v___x_1331_;
}
}
default: 
{
lean_object* v_bvarIdx_1336_; uint8_t v_strict_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1361_; 
v_bvarIdx_1336_ = lean_ctor_get(v_x_1109_, 0);
v_strict_1337_ = lean_ctor_get_uint8(v_x_1109_, sizeof(void*)*1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_x_1109_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1339_ = v_x_1109_;
v_isShared_1340_ = v_isSharedCheck_1361_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_bvarIdx_1336_);
lean_dec(v_x_1109_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1361_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___y_1342_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v___x_1357_ = lean_unsigned_to_nat(1024u);
v___x_1358_ = lean_nat_dec_le(v___x_1357_, v_prec_1110_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1342_ = v___x_1359_;
goto v___jp_1341_;
}
else
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1342_ = v___x_1360_;
goto v___jp_1341_;
}
v___jp_1341_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; lean_object* v___x_1354_; 
v___x_1343_ = lean_box(1);
v___x_1344_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__32));
v___x_1345_ = l_Nat_reprFast(v_bvarIdx_1336_);
v___x_1346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
v___x_1347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1344_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v___x_1343_);
v___x_1349_ = l_Bool_repr___redArg(v_strict_1337_);
v___x_1350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
lean_inc(v___y_1342_);
v___x_1351_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___y_1342_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = 0;
if (v_isShared_1340_ == 0)
{
lean_ctor_set_tag(v___x_1339_, 6);
lean_ctor_set(v___x_1339_, 0, v___x_1351_);
v___x_1354_ = v___x_1339_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1351_);
v___x_1354_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; 
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*1, v___x_1352_);
v___x_1355_ = l_Repr_addAppParen(v___x_1354_, v_prec_1110_);
return v___x_1355_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___boxed(lean_object* v_x_1362_, lean_object* v_prec_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr(v_x_1362_, v_prec_1363_);
lean_dec(v_prec_1363_);
return v_res_1364_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(lean_object* v_x_1367_, lean_object* v_x_1368_){
_start:
{
lean_object* v_lhs_1370_; lean_object* v_rhs_1371_; lean_object* v_lhs_x27_1372_; lean_object* v_rhs_x27_1373_; lean_object* v_lhs_1377_; lean_object* v_n_1378_; lean_object* v_lhs_x27_1379_; lean_object* v_n_x27_1380_; lean_object* v_bvarIdx_1384_; uint8_t v_strict_1385_; lean_object* v_bvarIdx_x27_1386_; uint8_t v_strict_x27_1387_; lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v_decide_1391_; 
v___x_1389_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_1367_);
v___x_1390_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx(v_x_1368_);
v_decide_1391_ = lean_nat_dec_eq(v___x_1389_, v___x_1390_);
lean_dec(v___x_1390_);
lean_dec(v___x_1389_);
if (v_decide_1391_ == 0)
{
return v_decide_1391_;
}
else
{
switch(lean_obj_tag(v_x_1367_))
{
case 0:
{
lean_object* v_lhs_1392_; lean_object* v_rhs_1393_; lean_object* v_lhs_1394_; lean_object* v_rhs_1395_; 
v_lhs_1392_ = lean_ctor_get(v_x_1367_, 0);
v_rhs_1393_ = lean_ctor_get(v_x_1367_, 1);
v_lhs_1394_ = lean_ctor_get(v_x_1368_, 0);
v_rhs_1395_ = lean_ctor_get(v_x_1368_, 1);
v_lhs_1370_ = v_lhs_1392_;
v_rhs_1371_ = v_rhs_1393_;
v_lhs_x27_1372_ = v_lhs_1394_;
v_rhs_x27_1373_ = v_rhs_1395_;
goto v___jp_1369_;
}
case 1:
{
lean_object* v_lhs_1396_; lean_object* v_rhs_1397_; lean_object* v_lhs_1398_; lean_object* v_rhs_1399_; 
v_lhs_1396_ = lean_ctor_get(v_x_1367_, 0);
v_rhs_1397_ = lean_ctor_get(v_x_1367_, 1);
v_lhs_1398_ = lean_ctor_get(v_x_1368_, 0);
v_rhs_1399_ = lean_ctor_get(v_x_1368_, 1);
v_lhs_1370_ = v_lhs_1396_;
v_rhs_1371_ = v_rhs_1397_;
v_lhs_x27_1372_ = v_lhs_1398_;
v_rhs_x27_1373_ = v_rhs_1399_;
goto v___jp_1369_;
}
case 2:
{
lean_object* v_lhs_1400_; lean_object* v_n_1401_; lean_object* v_lhs_1402_; lean_object* v_n_1403_; 
v_lhs_1400_ = lean_ctor_get(v_x_1367_, 0);
v_n_1401_ = lean_ctor_get(v_x_1367_, 1);
v_lhs_1402_ = lean_ctor_get(v_x_1368_, 0);
v_n_1403_ = lean_ctor_get(v_x_1368_, 1);
v_lhs_1377_ = v_lhs_1400_;
v_n_1378_ = v_n_1401_;
v_lhs_x27_1379_ = v_lhs_1402_;
v_n_x27_1380_ = v_n_1403_;
goto v___jp_1376_;
}
case 3:
{
lean_object* v_lhs_1404_; lean_object* v_n_1405_; lean_object* v_lhs_1406_; lean_object* v_n_1407_; 
v_lhs_1404_ = lean_ctor_get(v_x_1367_, 0);
v_n_1405_ = lean_ctor_get(v_x_1367_, 1);
v_lhs_1406_ = lean_ctor_get(v_x_1368_, 0);
v_n_1407_ = lean_ctor_get(v_x_1368_, 1);
v_lhs_1377_ = v_lhs_1404_;
v_n_1378_ = v_n_1405_;
v_lhs_x27_1379_ = v_lhs_1406_;
v_n_x27_1380_ = v_n_1407_;
goto v___jp_1376_;
}
case 6:
{
lean_object* v_bvarIdx_1408_; uint8_t v_strict_1409_; lean_object* v_bvarIdx_1410_; uint8_t v_strict_1411_; 
v_bvarIdx_1408_ = lean_ctor_get(v_x_1367_, 0);
v_strict_1409_ = lean_ctor_get_uint8(v_x_1367_, sizeof(void*)*1);
v_bvarIdx_1410_ = lean_ctor_get(v_x_1368_, 0);
v_strict_1411_ = lean_ctor_get_uint8(v_x_1368_, sizeof(void*)*1);
v_bvarIdx_1384_ = v_bvarIdx_1408_;
v_strict_1385_ = v_strict_1409_;
v_bvarIdx_x27_1386_ = v_bvarIdx_1410_;
v_strict_x27_1387_ = v_strict_1411_;
goto v___jp_1383_;
}
case 8:
{
lean_object* v_e_1412_; lean_object* v_e_1413_; uint8_t v___x_1414_; 
v_e_1412_ = lean_ctor_get(v_x_1367_, 0);
v_e_1413_ = lean_ctor_get(v_x_1368_, 0);
v___x_1414_ = lean_expr_eqv(v_e_1412_, v_e_1413_);
return v___x_1414_;
}
case 9:
{
lean_object* v_e_1415_; lean_object* v_e_1416_; uint8_t v___x_1417_; 
v_e_1415_ = lean_ctor_get(v_x_1367_, 0);
v_e_1416_ = lean_ctor_get(v_x_1368_, 0);
v___x_1417_ = lean_expr_eqv(v_e_1415_, v_e_1416_);
return v___x_1417_;
}
case 10:
{
lean_object* v_bvarIdx_1418_; uint8_t v_strict_1419_; lean_object* v_bvarIdx_1420_; uint8_t v_strict_1421_; 
v_bvarIdx_1418_ = lean_ctor_get(v_x_1367_, 0);
v_strict_1419_ = lean_ctor_get_uint8(v_x_1367_, sizeof(void*)*1);
v_bvarIdx_1420_ = lean_ctor_get(v_x_1368_, 0);
v_strict_1421_ = lean_ctor_get_uint8(v_x_1368_, sizeof(void*)*1);
v_bvarIdx_1384_ = v_bvarIdx_1418_;
v_strict_1385_ = v_strict_1419_;
v_bvarIdx_x27_1386_ = v_bvarIdx_1420_;
v_strict_x27_1387_ = v_strict_1421_;
goto v___jp_1383_;
}
default: 
{
lean_object* v_n_1422_; lean_object* v_n_1423_; uint8_t v___x_1424_; 
v_n_1422_ = lean_ctor_get(v_x_1367_, 0);
v_n_1423_ = lean_ctor_get(v_x_1368_, 0);
v___x_1424_ = lean_nat_dec_eq(v_n_1422_, v_n_1423_);
return v___x_1424_;
}
}
}
v___jp_1369_:
{
uint8_t v___x_1374_; 
v___x_1374_ = lean_nat_dec_eq(v_lhs_1370_, v_lhs_x27_1372_);
if (v___x_1374_ == 0)
{
return v___x_1374_;
}
else
{
uint8_t v___x_1375_; 
v___x_1375_ = l_Lean_Meta_Grind_instBEqCnstrRHS_beq(v_rhs_1371_, v_rhs_x27_1373_);
return v___x_1375_;
}
}
v___jp_1376_:
{
uint8_t v___x_1381_; 
v___x_1381_ = lean_nat_dec_eq(v_lhs_1377_, v_lhs_x27_1379_);
if (v___x_1381_ == 0)
{
return v___x_1381_;
}
else
{
uint8_t v___x_1382_; 
v___x_1382_ = lean_nat_dec_eq(v_n_1378_, v_n_x27_1380_);
return v___x_1382_;
}
}
v___jp_1383_:
{
uint8_t v___x_1388_; 
v___x_1388_ = lean_nat_dec_eq(v_bvarIdx_1384_, v_bvarIdx_x27_1386_);
if (v___x_1388_ == 0)
{
return v___x_1388_;
}
else
{
if (v_strict_x27_1387_ == 0)
{
if (v_strict_1385_ == 0)
{
return v___x_1388_;
}
else
{
return v_strict_x27_1387_;
}
}
else
{
return v_strict_1385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq___boxed(lean_object* v_x_1425_, lean_object* v_x_1426_){
_start:
{
uint8_t v_res_1427_; lean_object* v_r_1428_; 
v_res_1427_ = l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(v_x_1425_, v_x_1426_);
lean_dec_ref(v_x_1426_);
lean_dec_ref(v_x_1425_);
v_r_1428_ = lean_box(v_res_1427_);
return v_r_1428_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0(void){
_start:
{
uint8_t v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1431_ = 0;
v___x_1432_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default));
v___x_1433_ = l_Lean_Meta_Grind_instInhabitedOrigin_default;
v___x_1434_ = lean_box(0);
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_1437_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_1438_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
lean_ctor_set(v___x_1438_, 1, v___x_1436_);
lean_ctor_set(v___x_1438_, 2, v___x_1435_);
lean_ctor_set(v___x_1438_, 3, v___x_1434_);
lean_ctor_set(v___x_1438_, 4, v___x_1434_);
lean_ctor_set(v___x_1438_, 5, v___x_1433_);
lean_ctor_set(v___x_1438_, 6, v___x_1432_);
lean_ctor_set(v___x_1438_, 7, v___x_1434_);
lean_ctor_set_uint8(v___x_1438_, sizeof(void*)*8, v___x_1431_);
return v___x_1438_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default(void){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0, &l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0);
return v___x_1439_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem(void){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default;
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0(lean_object* v_thm_1441_){
_start:
{
lean_object* v_symbols_1442_; 
v_symbols_1442_ = lean_ctor_get(v_thm_1441_, 4);
lean_inc(v_symbols_1442_);
return v_symbols_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0___boxed(lean_object* v_thm_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0(v_thm_1443_);
lean_dec_ref(v_thm_1443_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__1(lean_object* v_thm_1445_, lean_object* v_symbols_1446_){
_start:
{
lean_object* v_levelParams_1447_; lean_object* v_proof_1448_; lean_object* v_numParams_1449_; lean_object* v_patterns_1450_; lean_object* v_origin_1451_; lean_object* v_kind_1452_; uint8_t v_minIndexable_1453_; lean_object* v_cnstrs_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
v_levelParams_1447_ = lean_ctor_get(v_thm_1445_, 0);
v_proof_1448_ = lean_ctor_get(v_thm_1445_, 1);
v_numParams_1449_ = lean_ctor_get(v_thm_1445_, 2);
v_patterns_1450_ = lean_ctor_get(v_thm_1445_, 3);
v_origin_1451_ = lean_ctor_get(v_thm_1445_, 5);
v_kind_1452_ = lean_ctor_get(v_thm_1445_, 6);
v_minIndexable_1453_ = lean_ctor_get_uint8(v_thm_1445_, sizeof(void*)*8);
v_cnstrs_1454_ = lean_ctor_get(v_thm_1445_, 7);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_thm_1445_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v_thm_1445_, 4);
lean_dec(v_unused_1462_);
v___x_1456_ = v_thm_1445_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_cnstrs_1454_);
lean_inc(v_kind_1452_);
lean_inc(v_origin_1451_);
lean_inc(v_patterns_1450_);
lean_inc(v_numParams_1449_);
lean_inc(v_proof_1448_);
lean_inc(v_levelParams_1447_);
lean_dec(v_thm_1445_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 4, v_symbols_1446_);
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_levelParams_1447_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_proof_1448_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_numParams_1449_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v_patterns_1450_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v_symbols_1446_);
lean_ctor_set(v_reuseFailAlloc_1460_, 5, v_origin_1451_);
lean_ctor_set(v_reuseFailAlloc_1460_, 6, v_kind_1452_);
lean_ctor_set(v_reuseFailAlloc_1460_, 7, v_cnstrs_1454_);
lean_ctor_set_uint8(v_reuseFailAlloc_1460_, sizeof(void*)*8, v_minIndexable_1453_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2(lean_object* v_thm_1463_){
_start:
{
lean_object* v_origin_1464_; 
v_origin_1464_ = lean_ctor_get(v_thm_1463_, 5);
lean_inc_ref(v_origin_1464_);
return v_origin_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2___boxed(lean_object* v_thm_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2(v_thm_1465_);
lean_dec_ref(v_thm_1465_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3(lean_object* v_thm_1467_){
_start:
{
lean_object* v_proof_1468_; 
v_proof_1468_ = lean_ctor_get(v_thm_1467_, 1);
lean_inc_ref(v_proof_1468_);
return v_proof_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3___boxed(lean_object* v_thm_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3(v_thm_1469_);
lean_dec_ref(v_thm_1469_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4(lean_object* v_thm_1471_){
_start:
{
lean_object* v_levelParams_1472_; 
v_levelParams_1472_ = lean_ctor_get(v_thm_1471_, 0);
lean_inc_ref(v_levelParams_1472_);
return v_levelParams_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4___boxed(lean_object* v_thm_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4(v_thm_1473_);
lean_dec_ref(v_thm_1473_);
return v_res_1474_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1487_ = l_Lean_Meta_Grind_instInhabitedOrigin_default;
v___x_1488_ = lean_box(0);
v___x_1489_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_1490_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_1491_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
lean_ctor_set(v___x_1491_, 1, v___x_1489_);
lean_ctor_set(v___x_1491_, 2, v___x_1488_);
lean_ctor_set(v___x_1491_, 3, v___x_1487_);
return v___x_1491_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default(void){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0, &l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem(void){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default;
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0(lean_object* v_thm_1494_){
_start:
{
lean_object* v_symbols_1495_; 
v_symbols_1495_ = lean_ctor_get(v_thm_1494_, 2);
lean_inc(v_symbols_1495_);
return v_symbols_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0___boxed(lean_object* v_thm_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0(v_thm_1496_);
lean_dec_ref(v_thm_1496_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__1(lean_object* v_thm_1498_, lean_object* v_symbols_1499_){
_start:
{
lean_object* v_levelParams_1500_; lean_object* v_proof_1501_; lean_object* v_origin_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
v_levelParams_1500_ = lean_ctor_get(v_thm_1498_, 0);
v_proof_1501_ = lean_ctor_get(v_thm_1498_, 1);
v_origin_1502_ = lean_ctor_get(v_thm_1498_, 3);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_thm_1498_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; 
v_unused_1510_ = lean_ctor_get(v_thm_1498_, 2);
lean_dec(v_unused_1510_);
v___x_1504_ = v_thm_1498_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_origin_1502_);
lean_inc(v_proof_1501_);
lean_inc(v_levelParams_1500_);
lean_dec(v_thm_1498_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 2, v_symbols_1499_);
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_levelParams_1500_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_proof_1501_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_symbols_1499_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_origin_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2(lean_object* v_thm_1511_){
_start:
{
lean_object* v_origin_1512_; 
v_origin_1512_ = lean_ctor_get(v_thm_1511_, 3);
lean_inc_ref(v_origin_1512_);
return v_origin_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2___boxed(lean_object* v_thm_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2(v_thm_1513_);
lean_dec_ref(v_thm_1513_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3(lean_object* v_thm_1515_){
_start:
{
lean_object* v_proof_1516_; 
v_proof_1516_ = lean_ctor_get(v_thm_1515_, 1);
lean_inc_ref(v_proof_1516_);
return v_proof_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3___boxed(lean_object* v_thm_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3(v_thm_1517_);
lean_dec_ref(v_thm_1517_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4(lean_object* v_thm_1519_){
_start:
{
lean_object* v_levelParams_1520_; 
v_levelParams_1520_ = lean_ctor_get(v_thm_1519_, 0);
lean_inc_ref(v_levelParams_1520_);
return v_levelParams_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4___boxed(lean_object* v_thm_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4(v_thm_1521_);
lean_dec_ref(v_thm_1521_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorIdx(lean_object* v_x_1535_){
_start:
{
switch(lean_obj_tag(v_x_1535_))
{
case 0:
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_unsigned_to_nat(0u);
return v___x_1536_;
}
case 1:
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_unsigned_to_nat(1u);
return v___x_1537_;
}
case 2:
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_unsigned_to_nat(2u);
return v___x_1538_;
}
case 3:
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_unsigned_to_nat(3u);
return v___x_1539_;
}
default: 
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_unsigned_to_nat(4u);
return v___x_1540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorIdx___boxed(lean_object* v_x_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_Meta_Grind_Entry_ctorIdx(v_x_1541_);
lean_dec_ref(v_x_1541_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim___redArg(lean_object* v_t_1543_, lean_object* v_k_1544_){
_start:
{
switch(lean_obj_tag(v_t_1543_))
{
case 2:
{
lean_object* v_declName_1545_; uint8_t v_eager_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_declName_1545_ = lean_ctor_get(v_t_1543_, 0);
lean_inc(v_declName_1545_);
v_eager_1546_ = lean_ctor_get_uint8(v_t_1543_, sizeof(void*)*1);
lean_dec_ref_known(v_t_1543_, 1);
v___x_1547_ = lean_box(v_eager_1546_);
v___x_1548_ = lean_apply_2(v_k_1544_, v_declName_1545_, v___x_1547_);
return v___x_1548_;
}
case 3:
{
lean_object* v_thm_1549_; lean_object* v___x_1550_; 
v_thm_1549_ = lean_ctor_get(v_t_1543_, 0);
lean_inc_ref(v_thm_1549_);
lean_dec_ref_known(v_t_1543_, 1);
v___x_1550_ = lean_apply_1(v_k_1544_, v_thm_1549_);
return v___x_1550_;
}
case 4:
{
lean_object* v_thm_1551_; lean_object* v___x_1552_; 
v_thm_1551_ = lean_ctor_get(v_t_1543_, 0);
lean_inc_ref(v_thm_1551_);
lean_dec_ref_known(v_t_1543_, 1);
v___x_1552_ = lean_apply_1(v_k_1544_, v_thm_1551_);
return v___x_1552_;
}
default: 
{
lean_object* v_declName_1553_; lean_object* v___x_1554_; 
v_declName_1553_ = lean_ctor_get(v_t_1543_, 0);
lean_inc(v_declName_1553_);
lean_dec_ref(v_t_1543_);
v___x_1554_ = lean_apply_1(v_k_1544_, v_declName_1553_);
return v___x_1554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim(lean_object* v_motive_1555_, lean_object* v_ctorIdx_1556_, lean_object* v_t_1557_, lean_object* v_h_1558_, lean_object* v_k_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1557_, v_k_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim___boxed(lean_object* v_motive_1561_, lean_object* v_ctorIdx_1562_, lean_object* v_t_1563_, lean_object* v_h_1564_, lean_object* v_k_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_Meta_Grind_Entry_ctorElim(v_motive_1561_, v_ctorIdx_1562_, v_t_1563_, v_h_1564_, v_k_1565_);
lean_dec(v_ctorIdx_1562_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ext_elim___redArg(lean_object* v_t_1567_, lean_object* v_ext_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1567_, v_ext_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ext_elim(lean_object* v_motive_1570_, lean_object* v_t_1571_, lean_object* v_h_1572_, lean_object* v_ext_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1571_, v_ext_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_funCC_elim___redArg(lean_object* v_t_1575_, lean_object* v_funCC_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1575_, v_funCC_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_funCC_elim(lean_object* v_motive_1578_, lean_object* v_t_1579_, lean_object* v_h_1580_, lean_object* v_funCC_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1579_, v_funCC_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_cases_elim___redArg(lean_object* v_t_1583_, lean_object* v_cases_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1583_, v_cases_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_cases_elim(lean_object* v_motive_1586_, lean_object* v_t_1587_, lean_object* v_h_1588_, lean_object* v_cases_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1587_, v_cases_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ematch_elim___redArg(lean_object* v_t_1591_, lean_object* v_ematch_1592_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1591_, v_ematch_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ematch_elim(lean_object* v_motive_1594_, lean_object* v_t_1595_, lean_object* v_h_1596_, lean_object* v_ematch_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1595_, v_ematch_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_inj_elim___redArg(lean_object* v_t_1599_, lean_object* v_inj_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1599_, v_inj_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_inj_elim(lean_object* v_motive_1602_, lean_object* v_t_1603_, lean_object* v_h_1604_, lean_object* v_inj_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1603_, v_inj_1605_);
return v___x_1606_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0, &l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0);
v___x_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg(){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___closed__0);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___boxed(lean_object* v___dummy_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg();
return v_res_1616_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg();
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0(lean_object* v_00_u03b2_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0);
return v___x_1619_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1(void){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1621_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0);
v___x_1622_ = l_Lean_NameSet_empty;
v___x_1623_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0);
v___x_1624_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1, &l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1);
v___x_1625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
lean_ctor_set(v___x_1625_, 1, v___x_1623_);
lean_ctor_set(v___x_1625_, 2, v___x_1622_);
lean_ctor_set(v___x_1625_, 3, v___x_1621_);
lean_ctor_set(v___x_1625_, 4, v___x_1621_);
return v___x_1625_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default(void){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1);
return v___x_1626_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState(void){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_x_1628_, lean_object* v_x_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_){
_start:
{
lean_object* v_ks_1632_; lean_object* v_vs_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1659_; 
v_ks_1632_ = lean_ctor_get(v_x_1628_, 0);
v_vs_1633_ = lean_ctor_get(v_x_1628_, 1);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_x_1628_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1635_ = v_x_1628_;
v_isShared_1636_ = v_isSharedCheck_1659_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_vs_1633_);
lean_inc(v_ks_1632_);
lean_dec(v_x_1628_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1659_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = lean_array_get_size(v_ks_1632_);
v___x_1638_ = lean_nat_dec_lt(v_x_1629_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1642_; 
lean_dec(v_x_1629_);
v___x_1639_ = lean_array_push(v_ks_1632_, v_x_1630_);
v___x_1640_ = lean_array_push(v_vs_1633_, v_x_1631_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 1, v___x_1640_);
lean_ctor_set(v___x_1635_, 0, v___x_1639_);
v___x_1642_ = v___x_1635_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
else
{
lean_object* v_k_x27_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v_k_x27_1644_ = lean_array_fget_borrowed(v_ks_1632_, v_x_1629_);
v___x_1645_ = l_Lean_Meta_Grind_Origin_key(v_x_1630_);
v___x_1646_ = l_Lean_Meta_Grind_Origin_key(v_k_x27_1644_);
v___x_1647_ = lean_name_eq(v___x_1645_, v___x_1646_);
lean_dec(v___x_1646_);
lean_dec(v___x_1645_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1649_; 
if (v_isShared_1636_ == 0)
{
v___x_1649_ = v___x_1635_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_ks_1632_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_vs_1633_);
v___x_1649_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_unsigned_to_nat(1u);
v___x_1651_ = lean_nat_add(v_x_1629_, v___x_1650_);
lean_dec(v_x_1629_);
v_x_1628_ = v___x_1649_;
v_x_1629_ = v___x_1651_;
goto _start;
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1654_ = lean_array_fset(v_ks_1632_, v_x_1629_, v_x_1630_);
v___x_1655_ = lean_array_fset(v_vs_1633_, v_x_1629_, v_x_1631_);
lean_dec(v_x_1629_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 1, v___x_1655_);
lean_ctor_set(v___x_1635_, 0, v___x_1654_);
v___x_1657_ = v___x_1635_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_n_1660_, lean_object* v_k_1661_, lean_object* v_v_1662_){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = lean_unsigned_to_nat(0u);
v___x_1664_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(v_n_1660_, v___x_1663_, v_k_1661_, v_v_1662_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1665_, size_t v_x_1666_, size_t v_x_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_){
_start:
{
if (lean_obj_tag(v_x_1665_) == 0)
{
lean_object* v_es_1670_; size_t v___x_1671_; size_t v___x_1672_; lean_object* v_j_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v_es_1670_ = lean_ctor_get(v_x_1665_, 0);
v___x_1671_ = ((size_t)31ULL);
v___x_1672_ = lean_usize_land(v_x_1666_, v___x_1671_);
v_j_1673_ = lean_usize_to_nat(v___x_1672_);
v___x_1674_ = lean_array_get_size(v_es_1670_);
v___x_1675_ = lean_nat_dec_lt(v_j_1673_, v___x_1674_);
if (v___x_1675_ == 0)
{
lean_dec(v_j_1673_);
lean_dec(v_x_1669_);
lean_dec_ref(v_x_1668_);
return v_x_1665_;
}
else
{
lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1716_; 
lean_inc_ref(v_es_1670_);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_x_1665_);
if (v_isSharedCheck_1716_ == 0)
{
lean_object* v_unused_1717_; 
v_unused_1717_ = lean_ctor_get(v_x_1665_, 0);
lean_dec(v_unused_1717_);
v___x_1677_ = v_x_1665_;
v_isShared_1678_ = v_isSharedCheck_1716_;
goto v_resetjp_1676_;
}
else
{
lean_dec(v_x_1665_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1716_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v_v_1679_; lean_object* v___x_1680_; lean_object* v_xs_x27_1681_; lean_object* v___y_1683_; 
v_v_1679_ = lean_array_fget(v_es_1670_, v_j_1673_);
v___x_1680_ = lean_box(0);
v_xs_x27_1681_ = lean_array_fset(v_es_1670_, v_j_1673_, v___x_1680_);
switch(lean_obj_tag(v_v_1679_))
{
case 0:
{
lean_object* v_key_1688_; lean_object* v_val_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1701_; 
v_key_1688_ = lean_ctor_get(v_v_1679_, 0);
v_val_1689_ = lean_ctor_get(v_v_1679_, 1);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_v_1679_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1691_ = v_v_1679_;
v_isShared_1692_ = v_isSharedCheck_1701_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_val_1689_);
lean_inc(v_key_1688_);
lean_dec(v_v_1679_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1701_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1693_ = l_Lean_Meta_Grind_Origin_key(v_x_1668_);
v___x_1694_ = l_Lean_Meta_Grind_Origin_key(v_key_1688_);
v___x_1695_ = lean_name_eq(v___x_1693_, v___x_1694_);
lean_dec(v___x_1694_);
lean_dec(v___x_1693_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_del_object(v___x_1691_);
v___x_1696_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1688_, v_val_1689_, v_x_1668_, v_x_1669_);
v___x_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
v___y_1683_ = v___x_1697_;
goto v___jp_1682_;
}
else
{
lean_object* v___x_1699_; 
lean_dec(v_val_1689_);
lean_dec(v_key_1688_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 1, v_x_1669_);
lean_ctor_set(v___x_1691_, 0, v_x_1668_);
v___x_1699_ = v___x_1691_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_x_1668_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_x_1669_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
v___y_1683_ = v___x_1699_;
goto v___jp_1682_;
}
}
}
}
case 1:
{
lean_object* v_node_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1714_; 
v_node_1702_ = lean_ctor_get(v_v_1679_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_v_1679_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1704_ = v_v_1679_;
v_isShared_1705_ = v_isSharedCheck_1714_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_node_1702_);
lean_dec(v_v_1679_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1714_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
size_t v___x_1706_; size_t v___x_1707_; size_t v___x_1708_; size_t v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1706_ = ((size_t)5ULL);
v___x_1707_ = lean_usize_shift_right(v_x_1666_, v___x_1706_);
v___x_1708_ = ((size_t)1ULL);
v___x_1709_ = lean_usize_add(v_x_1667_, v___x_1708_);
v___x_1710_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_node_1702_, v___x_1707_, v___x_1709_, v_x_1668_, v_x_1669_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1710_);
v___x_1712_ = v___x_1704_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
v___y_1683_ = v___x_1712_;
goto v___jp_1682_;
}
}
}
default: 
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1715_, 0, v_x_1668_);
lean_ctor_set(v___x_1715_, 1, v_x_1669_);
v___y_1683_ = v___x_1715_;
goto v___jp_1682_;
}
}
v___jp_1682_:
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1684_ = lean_array_fset(v_xs_x27_1681_, v_j_1673_, v___y_1683_);
lean_dec(v_j_1673_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1684_);
v___x_1686_ = v___x_1677_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
else
{
lean_object* v_ks_1718_; lean_object* v_vs_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1737_; 
v_ks_1718_ = lean_ctor_get(v_x_1665_, 0);
v_vs_1719_ = lean_ctor_get(v_x_1665_, 1);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_x_1665_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1721_ = v_x_1665_;
v_isShared_1722_ = v_isSharedCheck_1737_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_vs_1719_);
lean_inc(v_ks_1718_);
lean_dec(v_x_1665_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1737_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_ks_1718_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_vs_1719_);
v___x_1724_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v_newNode_1725_; size_t v___x_1726_; uint8_t v___x_1727_; 
v_newNode_1725_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(v___x_1724_, v_x_1668_, v_x_1669_);
v___x_1726_ = ((size_t)7ULL);
v___x_1727_ = lean_usize_dec_le(v___x_1726_, v_x_1667_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; lean_object* v___x_1729_; uint8_t v___x_1730_; 
v___x_1728_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1725_);
v___x_1729_ = lean_unsigned_to_nat(4u);
v___x_1730_ = lean_nat_dec_lt(v___x_1728_, v___x_1729_);
lean_dec(v___x_1728_);
if (v___x_1730_ == 0)
{
lean_object* v_ks_1731_; lean_object* v_vs_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v_ks_1731_ = lean_ctor_get(v_newNode_1725_, 0);
lean_inc_ref(v_ks_1731_);
v_vs_1732_ = lean_ctor_get(v_newNode_1725_, 1);
lean_inc_ref(v_vs_1732_);
lean_dec_ref(v_newNode_1725_);
v___x_1733_ = lean_unsigned_to_nat(0u);
v___x_1734_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0);
v___x_1735_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_x_1667_, v_ks_1731_, v_vs_1732_, v___x_1733_, v___x_1734_);
lean_dec_ref(v_vs_1732_);
lean_dec_ref(v_ks_1731_);
return v___x_1735_;
}
else
{
return v_newNode_1725_;
}
}
else
{
return v_newNode_1725_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(size_t v_depth_1738_, lean_object* v_keys_1739_, lean_object* v_vals_1740_, lean_object* v_i_1741_, lean_object* v_entries_1742_){
_start:
{
lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1743_ = lean_array_get_size(v_keys_1739_);
v___x_1744_ = lean_nat_dec_lt(v_i_1741_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_dec(v_i_1741_);
return v_entries_1742_;
}
else
{
lean_object* v_k_1745_; lean_object* v_v_1746_; uint64_t v___y_1748_; lean_object* v___x_1759_; 
v_k_1745_ = lean_array_fget_borrowed(v_keys_1739_, v_i_1741_);
v_v_1746_ = lean_array_fget_borrowed(v_vals_1740_, v_i_1741_);
v___x_1759_ = l_Lean_Meta_Grind_Origin_key(v_k_1745_);
if (lean_obj_tag(v___x_1759_) == 0)
{
uint64_t v___x_1760_; 
v___x_1760_ = 1723ULL;
v___y_1748_ = v___x_1760_;
goto v___jp_1747_;
}
else
{
uint64_t v_hash_1761_; 
v_hash_1761_ = lean_ctor_get_uint64(v___x_1759_, sizeof(void*)*2);
lean_dec(v___x_1759_);
v___y_1748_ = v_hash_1761_;
goto v___jp_1747_;
}
v___jp_1747_:
{
size_t v_h_1749_; size_t v___x_1750_; lean_object* v___x_1751_; size_t v___x_1752_; size_t v___x_1753_; size_t v___x_1754_; size_t v_h_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v_h_1749_ = lean_uint64_to_usize(v___y_1748_);
v___x_1750_ = ((size_t)5ULL);
v___x_1751_ = lean_unsigned_to_nat(1u);
v___x_1752_ = ((size_t)1ULL);
v___x_1753_ = lean_usize_sub(v_depth_1738_, v___x_1752_);
v___x_1754_ = lean_usize_mul(v___x_1750_, v___x_1753_);
v_h_1755_ = lean_usize_shift_right(v_h_1749_, v___x_1754_);
v___x_1756_ = lean_nat_add(v_i_1741_, v___x_1751_);
lean_dec(v_i_1741_);
lean_inc(v_v_1746_);
lean_inc(v_k_1745_);
v___x_1757_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_entries_1742_, v_h_1755_, v_depth_1738_, v_k_1745_, v_v_1746_);
v_i_1741_ = v___x_1756_;
v_entries_1742_ = v___x_1757_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_depth_1762_, lean_object* v_keys_1763_, lean_object* v_vals_1764_, lean_object* v_i_1765_, lean_object* v_entries_1766_){
_start:
{
size_t v_depth_boxed_1767_; lean_object* v_res_1768_; 
v_depth_boxed_1767_ = lean_unbox_usize(v_depth_1762_);
lean_dec(v_depth_1762_);
v_res_1768_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_depth_boxed_1767_, v_keys_1763_, v_vals_1764_, v_i_1765_, v_entries_1766_);
lean_dec_ref(v_vals_1764_);
lean_dec_ref(v_keys_1763_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_x_1769_, lean_object* v_x_1770_, lean_object* v_x_1771_, lean_object* v_x_1772_, lean_object* v_x_1773_){
_start:
{
size_t v_x_1258__boxed_1774_; size_t v_x_1259__boxed_1775_; lean_object* v_res_1776_; 
v_x_1258__boxed_1774_ = lean_unbox_usize(v_x_1770_);
lean_dec(v_x_1770_);
v_x_1259__boxed_1775_ = lean_unbox_usize(v_x_1771_);
lean_dec(v_x_1771_);
v_res_1776_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_1769_, v_x_1258__boxed_1774_, v_x_1259__boxed_1775_, v_x_1772_, v_x_1773_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(lean_object* v_x_1777_, lean_object* v_x_1778_, lean_object* v_x_1779_){
_start:
{
uint64_t v___y_1781_; lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_Meta_Grind_Origin_key(v_x_1778_);
if (lean_obj_tag(v___x_1785_) == 0)
{
uint64_t v___x_1786_; 
v___x_1786_ = 1723ULL;
v___y_1781_ = v___x_1786_;
goto v___jp_1780_;
}
else
{
uint64_t v_hash_1787_; 
v_hash_1787_ = lean_ctor_get_uint64(v___x_1785_, sizeof(void*)*2);
lean_dec(v___x_1785_);
v___y_1781_ = v_hash_1787_;
goto v___jp_1780_;
}
v___jp_1780_:
{
size_t v___x_1782_; size_t v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = lean_uint64_to_usize(v___y_1781_);
v___x_1783_ = ((size_t)1ULL);
v___x_1784_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_1777_, v___x_1782_, v___x_1783_, v_x_1778_, v_x_1779_);
return v___x_1784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(lean_object* v_keys_1788_, lean_object* v_vals_1789_, lean_object* v_i_1790_, lean_object* v_k_1791_){
_start:
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = lean_array_get_size(v_keys_1788_);
v___x_1793_ = lean_nat_dec_lt(v_i_1790_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; 
lean_dec(v_i_1790_);
v___x_1794_ = lean_box(0);
return v___x_1794_;
}
else
{
lean_object* v_k_x27_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; 
v_k_x27_1795_ = lean_array_fget_borrowed(v_keys_1788_, v_i_1790_);
v___x_1796_ = l_Lean_Meta_Grind_Origin_key(v_k_1791_);
v___x_1797_ = l_Lean_Meta_Grind_Origin_key(v_k_x27_1795_);
v___x_1798_ = lean_name_eq(v___x_1796_, v___x_1797_);
lean_dec(v___x_1797_);
lean_dec(v___x_1796_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = lean_unsigned_to_nat(1u);
v___x_1800_ = lean_nat_add(v_i_1790_, v___x_1799_);
lean_dec(v_i_1790_);
v_i_1790_ = v___x_1800_;
goto _start;
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = lean_array_fget_borrowed(v_vals_1789_, v_i_1790_);
lean_dec(v_i_1790_);
lean_inc(v___x_1802_);
v___x_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
return v___x_1803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg___boxed(lean_object* v_keys_1804_, lean_object* v_vals_1805_, lean_object* v_i_1806_, lean_object* v_k_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_keys_1804_, v_vals_1805_, v_i_1806_, v_k_1807_);
lean_dec_ref(v_k_1807_);
lean_dec_ref(v_vals_1805_);
lean_dec_ref(v_keys_1804_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(lean_object* v_x_1809_, size_t v_x_1810_, lean_object* v_x_1811_){
_start:
{
if (lean_obj_tag(v_x_1809_) == 0)
{
lean_object* v_es_1812_; lean_object* v___x_1813_; size_t v___x_1814_; size_t v___x_1815_; lean_object* v_j_1816_; lean_object* v___x_1817_; 
v_es_1812_ = lean_ctor_get(v_x_1809_, 0);
v___x_1813_ = lean_box(2);
v___x_1814_ = ((size_t)31ULL);
v___x_1815_ = lean_usize_land(v_x_1810_, v___x_1814_);
v_j_1816_ = lean_usize_to_nat(v___x_1815_);
v___x_1817_ = lean_array_get_borrowed(v___x_1813_, v_es_1812_, v_j_1816_);
lean_dec(v_j_1816_);
switch(lean_obj_tag(v___x_1817_))
{
case 0:
{
lean_object* v_key_1818_; lean_object* v_val_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v_key_1818_ = lean_ctor_get(v___x_1817_, 0);
v_val_1819_ = lean_ctor_get(v___x_1817_, 1);
v___x_1820_ = l_Lean_Meta_Grind_Origin_key(v_x_1811_);
v___x_1821_ = l_Lean_Meta_Grind_Origin_key(v_key_1818_);
v___x_1822_ = lean_name_eq(v___x_1820_, v___x_1821_);
lean_dec(v___x_1821_);
lean_dec(v___x_1820_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_box(0);
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; 
lean_inc(v_val_1819_);
v___x_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_val_1819_);
return v___x_1824_;
}
}
case 1:
{
lean_object* v_node_1825_; size_t v___x_1826_; size_t v___x_1827_; 
v_node_1825_ = lean_ctor_get(v___x_1817_, 0);
v___x_1826_ = ((size_t)5ULL);
v___x_1827_ = lean_usize_shift_right(v_x_1810_, v___x_1826_);
v_x_1809_ = v_node_1825_;
v_x_1810_ = v___x_1827_;
goto _start;
}
default: 
{
lean_object* v___x_1829_; 
v___x_1829_ = lean_box(0);
return v___x_1829_;
}
}
}
else
{
lean_object* v_ks_1830_; lean_object* v_vs_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_ks_1830_ = lean_ctor_get(v_x_1809_, 0);
v_vs_1831_ = lean_ctor_get(v_x_1809_, 1);
v___x_1832_ = lean_unsigned_to_nat(0u);
v___x_1833_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_ks_1830_, v_vs_1831_, v___x_1832_, v_x_1811_);
return v___x_1833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_x_1834_, lean_object* v_x_1835_, lean_object* v_x_1836_){
_start:
{
size_t v_x_1458__boxed_1837_; lean_object* v_res_1838_; 
v_x_1458__boxed_1837_ = lean_unbox_usize(v_x_1835_);
lean_dec(v_x_1835_);
v_res_1838_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_1834_, v_x_1458__boxed_1837_, v_x_1836_);
lean_dec_ref(v_x_1836_);
lean_dec_ref(v_x_1834_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(lean_object* v_x_1839_, lean_object* v_x_1840_){
_start:
{
uint64_t v___y_1842_; lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_Meta_Grind_Origin_key(v_x_1840_);
if (lean_obj_tag(v___x_1845_) == 0)
{
uint64_t v___x_1846_; 
v___x_1846_ = 1723ULL;
v___y_1842_ = v___x_1846_;
goto v___jp_1841_;
}
else
{
uint64_t v_hash_1847_; 
v_hash_1847_ = lean_ctor_get_uint64(v___x_1845_, sizeof(void*)*2);
lean_dec(v___x_1845_);
v___y_1842_ = v_hash_1847_;
goto v___jp_1841_;
}
v___jp_1841_:
{
size_t v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = lean_uint64_to_usize(v___y_1842_);
v___x_1844_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_1839_, v___x_1843_, v_x_1840_);
return v___x_1844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg___boxed(lean_object* v_x_1848_, lean_object* v_x_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_x_1848_, v_x_1849_);
lean_dec_ref(v_x_1849_);
lean_dec_ref(v_x_1848_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(lean_object* v_keys_1851_, lean_object* v_vals_1852_, lean_object* v_i_1853_, lean_object* v_k_1854_){
_start:
{
lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1855_ = lean_array_get_size(v_keys_1851_);
v___x_1856_ = lean_nat_dec_lt(v_i_1853_, v___x_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; 
lean_dec(v_i_1853_);
v___x_1857_ = lean_box(0);
return v___x_1857_;
}
else
{
lean_object* v_k_x27_1858_; uint8_t v___x_1859_; 
v_k_x27_1858_ = lean_array_fget_borrowed(v_keys_1851_, v_i_1853_);
v___x_1859_ = lean_name_eq(v_k_1854_, v_k_x27_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_unsigned_to_nat(1u);
v___x_1861_ = lean_nat_add(v_i_1853_, v___x_1860_);
lean_dec(v_i_1853_);
v_i_1853_ = v___x_1861_;
goto _start;
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_array_fget_borrowed(v_vals_1852_, v_i_1853_);
lean_dec(v_i_1853_);
lean_inc(v___x_1863_);
v___x_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
return v___x_1864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg___boxed(lean_object* v_keys_1865_, lean_object* v_vals_1866_, lean_object* v_i_1867_, lean_object* v_k_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_keys_1865_, v_vals_1866_, v_i_1867_, v_k_1868_);
lean_dec(v_k_1868_);
lean_dec_ref(v_vals_1866_);
lean_dec_ref(v_keys_1865_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(lean_object* v_x_1870_, size_t v_x_1871_, lean_object* v_x_1872_){
_start:
{
if (lean_obj_tag(v_x_1870_) == 0)
{
lean_object* v_es_1873_; lean_object* v___x_1874_; size_t v___x_1875_; size_t v___x_1876_; lean_object* v_j_1877_; lean_object* v___x_1878_; 
v_es_1873_ = lean_ctor_get(v_x_1870_, 0);
v___x_1874_ = lean_box(2);
v___x_1875_ = ((size_t)31ULL);
v___x_1876_ = lean_usize_land(v_x_1871_, v___x_1875_);
v_j_1877_ = lean_usize_to_nat(v___x_1876_);
v___x_1878_ = lean_array_get_borrowed(v___x_1874_, v_es_1873_, v_j_1877_);
lean_dec(v_j_1877_);
switch(lean_obj_tag(v___x_1878_))
{
case 0:
{
lean_object* v_key_1879_; lean_object* v_val_1880_; uint8_t v___x_1881_; 
v_key_1879_ = lean_ctor_get(v___x_1878_, 0);
v_val_1880_ = lean_ctor_get(v___x_1878_, 1);
v___x_1881_ = lean_name_eq(v_x_1872_, v_key_1879_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_box(0);
return v___x_1882_;
}
else
{
lean_object* v___x_1883_; 
lean_inc(v_val_1880_);
v___x_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1883_, 0, v_val_1880_);
return v___x_1883_;
}
}
case 1:
{
lean_object* v_node_1884_; size_t v___x_1885_; size_t v___x_1886_; 
v_node_1884_ = lean_ctor_get(v___x_1878_, 0);
v___x_1885_ = ((size_t)5ULL);
v___x_1886_ = lean_usize_shift_right(v_x_1871_, v___x_1885_);
v_x_1870_ = v_node_1884_;
v_x_1871_ = v___x_1886_;
goto _start;
}
default: 
{
lean_object* v___x_1888_; 
v___x_1888_ = lean_box(0);
return v___x_1888_;
}
}
}
else
{
lean_object* v_ks_1889_; lean_object* v_vs_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_ks_1889_ = lean_ctor_get(v_x_1870_, 0);
v_vs_1890_ = lean_ctor_get(v_x_1870_, 1);
v___x_1891_ = lean_unsigned_to_nat(0u);
v___x_1892_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_ks_1889_, v_vs_1890_, v___x_1891_, v_x_1872_);
return v___x_1892_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg___boxed(lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_){
_start:
{
size_t v_x_1545__boxed_1896_; lean_object* v_res_1897_; 
v_x_1545__boxed_1896_ = lean_unbox_usize(v_x_1894_);
lean_dec(v_x_1894_);
v_res_1897_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_1893_, v_x_1545__boxed_1896_, v_x_1895_);
lean_dec(v_x_1895_);
lean_dec_ref(v_x_1893_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
uint64_t v___y_1901_; 
if (lean_obj_tag(v_x_1899_) == 0)
{
uint64_t v___x_1904_; 
v___x_1904_ = 1723ULL;
v___y_1901_ = v___x_1904_;
goto v___jp_1900_;
}
else
{
uint64_t v_hash_1905_; 
v_hash_1905_ = lean_ctor_get_uint64(v_x_1899_, sizeof(void*)*2);
v___y_1901_ = v_hash_1905_;
goto v___jp_1900_;
}
v___jp_1900_:
{
size_t v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = lean_uint64_to_usize(v___y_1901_);
v___x_1903_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_1898_, v___x_1902_, v_x_1899_);
return v___x_1903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg___boxed(lean_object* v_x_1906_, lean_object* v_x_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_x_1906_, v_x_1907_);
lean_dec(v_x_1907_);
lean_dec_ref(v_x_1906_);
return v_res_1908_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg();
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0(lean_object* v_msg_1917_){
_start:
{
lean_object* v___f_1918_; lean_object* v___f_1919_; lean_object* v___f_1920_; lean_object* v___f_1921_; lean_object* v___f_1922_; lean_object* v___f_1923_; lean_object* v___f_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___f_1918_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0));
v___f_1919_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1));
v___f_1920_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2));
v___f_1921_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3));
v___f_1922_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4));
v___f_1923_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5));
v___f_1924_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6));
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___f_1918_);
lean_ctor_set(v___x_1925_, 1, v___f_1919_);
v___x_1926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
lean_ctor_set(v___x_1926_, 1, v___f_1920_);
lean_ctor_set(v___x_1926_, 2, v___f_1921_);
lean_ctor_set(v___x_1926_, 3, v___f_1922_);
lean_ctor_set(v___x_1926_, 4, v___f_1923_);
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v___f_1924_);
v___x_1928_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7, &l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once, _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7);
v___x_1929_ = l_instInhabitedOfMonad___redArg(v___x_1927_, v___x_1928_);
v___x_1930_ = lean_panic_fn_borrowed(v___x_1929_, v_msg_1917_);
lean_dec(v___x_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(lean_object* v_xs_1931_, lean_object* v_v_1932_, lean_object* v_i_1933_){
_start:
{
lean_object* v___x_1934_; uint8_t v___x_1935_; 
v___x_1934_ = lean_array_get_size(v_xs_1931_);
v___x_1935_ = lean_nat_dec_lt(v_i_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; 
lean_dec(v_i_1933_);
v___x_1936_ = lean_box(0);
return v___x_1936_;
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
v___x_1937_ = lean_array_fget_borrowed(v_xs_1931_, v_i_1933_);
v___x_1938_ = l_Lean_Meta_Grind_Origin_key(v___x_1937_);
v___x_1939_ = l_Lean_Meta_Grind_Origin_key(v_v_1932_);
v___x_1940_ = lean_name_eq(v___x_1938_, v___x_1939_);
lean_dec(v___x_1939_);
lean_dec(v___x_1938_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = lean_unsigned_to_nat(1u);
v___x_1942_ = lean_nat_add(v_i_1933_, v___x_1941_);
lean_dec(v_i_1933_);
v_i_1933_ = v___x_1942_;
goto _start;
}
else
{
lean_object* v___x_1944_; 
v___x_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1944_, 0, v_i_1933_);
return v___x_1944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13___boxed(lean_object* v_xs_1945_, lean_object* v_v_1946_, lean_object* v_i_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(v_xs_1945_, v_v_1946_, v_i_1947_);
lean_dec_ref(v_v_1946_);
lean_dec_ref(v_xs_1945_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(lean_object* v_xs_1949_, lean_object* v_v_1950_){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = lean_unsigned_to_nat(0u);
v___x_1952_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(v_xs_1949_, v_v_1950_, v___x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9___boxed(lean_object* v_xs_1953_, lean_object* v_v_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(v_xs_1953_, v_v_1954_);
lean_dec_ref(v_v_1954_);
lean_dec_ref(v_xs_1953_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(lean_object* v_x_1956_, size_t v_x_1957_, lean_object* v_x_1958_){
_start:
{
if (lean_obj_tag(v_x_1956_) == 0)
{
lean_object* v_es_1959_; lean_object* v___x_1960_; size_t v___x_1961_; size_t v___x_1962_; lean_object* v_j_1963_; lean_object* v_entry_1964_; 
v_es_1959_ = lean_ctor_get(v_x_1956_, 0);
v___x_1960_ = lean_box(2);
v___x_1961_ = ((size_t)31ULL);
v___x_1962_ = lean_usize_land(v_x_1957_, v___x_1961_);
v_j_1963_ = lean_usize_to_nat(v___x_1962_);
v_entry_1964_ = lean_array_get(v___x_1960_, v_es_1959_, v_j_1963_);
switch(lean_obj_tag(v_entry_1964_))
{
case 0:
{
lean_object* v_key_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v_key_1965_ = lean_ctor_get(v_entry_1964_, 0);
lean_inc(v_key_1965_);
lean_dec_ref_known(v_entry_1964_, 2);
v___x_1966_ = l_Lean_Meta_Grind_Origin_key(v_x_1958_);
v___x_1967_ = l_Lean_Meta_Grind_Origin_key(v_key_1965_);
lean_dec(v_key_1965_);
v___x_1968_ = lean_name_eq(v___x_1966_, v___x_1967_);
lean_dec(v___x_1967_);
lean_dec(v___x_1966_);
if (v___x_1968_ == 0)
{
lean_dec(v_j_1963_);
return v_x_1956_;
}
else
{
lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1976_; 
lean_inc_ref(v_es_1959_);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_x_1956_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; 
v_unused_1977_ = lean_ctor_get(v_x_1956_, 0);
lean_dec(v_unused_1977_);
v___x_1970_ = v_x_1956_;
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
else
{
lean_dec(v_x_1956_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v___x_1974_; 
v___x_1972_ = lean_array_set(v_es_1959_, v_j_1963_, v___x_1960_);
lean_dec(v_j_1963_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1972_);
v___x_1974_ = v___x_1970_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
case 1:
{
lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2012_; 
lean_inc_ref(v_es_1959_);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_x_1956_);
if (v_isSharedCheck_2012_ == 0)
{
lean_object* v_unused_2013_; 
v_unused_2013_ = lean_ctor_get(v_x_1956_, 0);
lean_dec(v_unused_2013_);
v___x_1979_ = v_x_1956_;
v_isShared_1980_ = v_isSharedCheck_2012_;
goto v_resetjp_1978_;
}
else
{
lean_dec(v_x_1956_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2012_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v_node_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2011_; 
v_node_1981_ = lean_ctor_get(v_entry_1964_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_entry_1964_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1983_ = v_entry_1964_;
v_isShared_1984_ = v_isSharedCheck_2011_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_node_1981_);
lean_dec(v_entry_1964_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2011_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
size_t v___x_1985_; lean_object* v_entries_1986_; size_t v___x_1987_; lean_object* v_newNode_1988_; lean_object* v___x_1989_; 
v___x_1985_ = ((size_t)5ULL);
v_entries_1986_ = lean_array_set(v_es_1959_, v_j_1963_, v___x_1960_);
v___x_1987_ = lean_usize_shift_right(v_x_1957_, v___x_1985_);
v_newNode_1988_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_node_1981_, v___x_1987_, v_x_1958_);
lean_inc_ref(v_newNode_1988_);
v___x_1989_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1988_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v___x_1991_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v_newNode_1988_);
v___x_1991_ = v___x_1983_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_newNode_1988_);
v___x_1991_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1992_ = lean_array_set(v_entries_1986_, v_j_1963_, v___x_1991_);
lean_dec(v_j_1963_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_1992_);
v___x_1994_ = v___x_1979_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1992_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
else
{
lean_object* v_val_1997_; lean_object* v_fst_1998_; lean_object* v_snd_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2010_; 
lean_dec_ref(v_newNode_1988_);
lean_del_object(v___x_1983_);
v_val_1997_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_val_1997_);
lean_dec_ref_known(v___x_1989_, 1);
v_fst_1998_ = lean_ctor_get(v_val_1997_, 0);
v_snd_1999_ = lean_ctor_get(v_val_1997_, 1);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_val_1997_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2001_ = v_val_1997_;
v_isShared_2002_ = v_isSharedCheck_2010_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_snd_1999_);
lean_inc(v_fst_1998_);
lean_dec(v_val_1997_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2010_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_fst_1998_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_snd_1999_);
v___x_2004_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_array_set(v_entries_1986_, v_j_1963_, v___x_2004_);
lean_dec(v_j_1963_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_2005_);
v___x_2007_ = v___x_1979_;
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
}
}
}
default: 
{
lean_dec(v_j_1963_);
return v_x_1956_;
}
}
}
else
{
lean_object* v_ks_2014_; lean_object* v_vs_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2029_; 
v_ks_2014_ = lean_ctor_get(v_x_1956_, 0);
v_vs_2015_ = lean_ctor_get(v_x_1956_, 1);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_x_1956_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2017_ = v_x_1956_;
v_isShared_2018_ = v_isSharedCheck_2029_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_vs_2015_);
lean_inc(v_ks_2014_);
lean_dec(v_x_1956_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2029_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(v_ks_2014_, v_x_1958_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v___x_2021_; 
if (v_isShared_2018_ == 0)
{
v___x_2021_ = v___x_2017_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_ks_2014_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_vs_2015_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
else
{
lean_object* v_val_2023_; lean_object* v_keys_x27_2024_; lean_object* v_vals_x27_2025_; lean_object* v___x_2027_; 
v_val_2023_ = lean_ctor_get(v___x_2019_, 0);
lean_inc_n(v_val_2023_, 2);
lean_dec_ref_known(v___x_2019_, 1);
v_keys_x27_2024_ = l_Array_eraseIdx___redArg(v_ks_2014_, v_val_2023_);
v_vals_x27_2025_ = l_Array_eraseIdx___redArg(v_vs_2015_, v_val_2023_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 1, v_vals_x27_2025_);
lean_ctor_set(v___x_2017_, 0, v_keys_x27_2024_);
v___x_2027_ = v___x_2017_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_keys_x27_2024_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_vals_x27_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2030_, lean_object* v_x_2031_, lean_object* v_x_2032_){
_start:
{
size_t v_x_1684__boxed_2033_; lean_object* v_res_2034_; 
v_x_1684__boxed_2033_ = lean_unbox_usize(v_x_2031_);
lean_dec(v_x_2031_);
v_res_2034_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2030_, v_x_1684__boxed_2033_, v_x_2032_);
lean_dec_ref(v_x_2032_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(lean_object* v_x_2035_, lean_object* v_x_2036_){
_start:
{
uint64_t v___y_2038_; lean_object* v___x_2041_; 
v___x_2041_ = l_Lean_Meta_Grind_Origin_key(v_x_2036_);
if (lean_obj_tag(v___x_2041_) == 0)
{
uint64_t v___x_2042_; 
v___x_2042_ = 1723ULL;
v___y_2038_ = v___x_2042_;
goto v___jp_2037_;
}
else
{
uint64_t v_hash_2043_; 
v_hash_2043_ = lean_ctor_get_uint64(v___x_2041_, sizeof(void*)*2);
lean_dec(v___x_2041_);
v___y_2038_ = v_hash_2043_;
goto v___jp_2037_;
}
v___jp_2037_:
{
size_t v_h_2039_; lean_object* v___x_2040_; 
v_h_2039_ = lean_uint64_to_usize(v___y_2038_);
v___x_2040_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2035_, v_h_2039_, v_x_2036_);
return v___x_2040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg___boxed(lean_object* v_x_2044_, lean_object* v_x_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_x_2044_, v_x_2045_);
lean_dec_ref(v_x_2045_);
return v_res_2046_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2050_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2));
v___x_2051_ = lean_unsigned_to_nat(6u);
v___x_2052_ = lean_unsigned_to_nat(82u);
v___x_2053_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__1));
v___x_2054_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__0));
v___x_2055_ = l_mkPanicMessageWithDecl(v___x_2054_, v___x_2053_, v___x_2052_, v___x_2051_, v___x_2050_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0(lean_object* v_s_2056_, lean_object* v_thm_2057_){
_start:
{
lean_object* v_symbols_2061_; 
v_symbols_2061_ = lean_ctor_get(v_thm_2057_, 4);
lean_inc(v_symbols_2061_);
if (lean_obj_tag(v_symbols_2061_) == 1)
{
lean_object* v_head_2062_; 
v_head_2062_ = lean_ctor_get(v_symbols_2061_, 0);
lean_inc(v_head_2062_);
if (lean_obj_tag(v_head_2062_) == 2)
{
lean_object* v_levelParams_2063_; lean_object* v_proof_2064_; lean_object* v_numParams_2065_; lean_object* v_patterns_2066_; lean_object* v_origin_2067_; lean_object* v_kind_2068_; uint8_t v_minIndexable_2069_; lean_object* v_cnstrs_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2121_; 
v_levelParams_2063_ = lean_ctor_get(v_thm_2057_, 0);
v_proof_2064_ = lean_ctor_get(v_thm_2057_, 1);
v_numParams_2065_ = lean_ctor_get(v_thm_2057_, 2);
v_patterns_2066_ = lean_ctor_get(v_thm_2057_, 3);
v_origin_2067_ = lean_ctor_get(v_thm_2057_, 5);
v_kind_2068_ = lean_ctor_get(v_thm_2057_, 6);
v_minIndexable_2069_ = lean_ctor_get_uint8(v_thm_2057_, sizeof(void*)*8);
v_cnstrs_2070_ = lean_ctor_get(v_thm_2057_, 7);
v_isSharedCheck_2121_ = !lean_is_exclusive(v_thm_2057_);
if (v_isSharedCheck_2121_ == 0)
{
lean_object* v_unused_2122_; 
v_unused_2122_ = lean_ctor_get(v_thm_2057_, 4);
lean_dec(v_unused_2122_);
v___x_2072_ = v_thm_2057_;
v_isShared_2073_ = v_isSharedCheck_2121_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_cnstrs_2070_);
lean_inc(v_kind_2068_);
lean_inc(v_origin_2067_);
lean_inc(v_patterns_2066_);
lean_inc(v_numParams_2065_);
lean_inc(v_proof_2064_);
lean_inc(v_levelParams_2063_);
lean_dec(v_thm_2057_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2121_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v_tail_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2119_; 
v_tail_2074_ = lean_ctor_get(v_symbols_2061_, 1);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_symbols_2061_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; 
v_unused_2120_ = lean_ctor_get(v_symbols_2061_, 0);
lean_dec(v_unused_2120_);
v___x_2076_ = v_symbols_2061_;
v_isShared_2077_ = v_isSharedCheck_2119_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_tail_2074_);
lean_dec(v_symbols_2061_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2119_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v_constName_2078_; lean_object* v_smap_2079_; lean_object* v_origins_2080_; lean_object* v_erased_2081_; lean_object* v_omap_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2118_; 
v_constName_2078_ = lean_ctor_get(v_head_2062_, 0);
lean_inc(v_constName_2078_);
lean_dec_ref_known(v_head_2062_, 1);
v_smap_2079_ = lean_ctor_get(v_s_2056_, 0);
v_origins_2080_ = lean_ctor_get(v_s_2056_, 1);
v_erased_2081_ = lean_ctor_get(v_s_2056_, 2);
v_omap_2082_ = lean_ctor_get(v_s_2056_, 3);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_s_2056_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2084_ = v_s_2056_;
v_isShared_2085_ = v_isSharedCheck_2118_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_omap_2082_);
lean_inc(v_erased_2081_);
lean_inc(v_origins_2080_);
lean_inc(v_smap_2079_);
lean_dec(v_s_2056_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2118_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v_thm_2087_; 
lean_inc_ref(v_origin_2067_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 4, v_tail_2074_);
v_thm_2087_ = v___x_2072_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_levelParams_2063_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_proof_2064_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v_numParams_2065_);
lean_ctor_set(v_reuseFailAlloc_2117_, 3, v_patterns_2066_);
lean_ctor_set(v_reuseFailAlloc_2117_, 4, v_tail_2074_);
lean_ctor_set(v_reuseFailAlloc_2117_, 5, v_origin_2067_);
lean_ctor_set(v_reuseFailAlloc_2117_, 6, v_kind_2068_);
lean_ctor_set(v_reuseFailAlloc_2117_, 7, v_cnstrs_2070_);
lean_ctor_set_uint8(v_reuseFailAlloc_2117_, sizeof(void*)*8, v_minIndexable_2069_);
v_thm_2087_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2088_; lean_object* v_origins_2089_; lean_object* v_erased_2090_; lean_object* v___y_2092_; lean_object* v___x_2110_; 
v___x_2088_ = lean_box(0);
lean_inc_ref(v_origin_2067_);
v_origins_2089_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_origins_2080_, v_origin_2067_, v___x_2088_);
v_erased_2090_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_erased_2081_, v_origin_2067_);
v___x_2110_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_smap_2079_, v_constName_2078_);
if (lean_obj_tag(v___x_2110_) == 1)
{
lean_object* v_val_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v_val_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_val_2111_);
lean_dec_ref_known(v___x_2110_, 1);
lean_inc_ref(v_thm_2087_);
v___x_2112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2112_, 0, v_thm_2087_);
lean_ctor_set(v___x_2112_, 1, v_val_2111_);
v___x_2113_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2079_, v_constName_2078_, v___x_2112_);
v___y_2092_ = v___x_2113_;
goto v___jp_2091_;
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec(v___x_2110_);
v___x_2114_ = lean_box(0);
lean_inc_ref(v_thm_2087_);
v___x_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2115_, 0, v_thm_2087_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2079_, v_constName_2078_, v___x_2115_);
v___y_2092_ = v___x_2116_;
goto v___jp_2091_;
}
v___jp_2091_:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_omap_2082_, v_origin_2067_);
if (lean_obj_tag(v___x_2093_) == 1)
{
lean_object* v_val_2094_; lean_object* v___x_2096_; 
v_val_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_val_2094_);
lean_dec_ref_known(v___x_2093_, 1);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 1, v_val_2094_);
lean_ctor_set(v___x_2076_, 0, v_thm_2087_);
v___x_2096_ = v___x_2076_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_thm_2087_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_val_2094_);
v___x_2096_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2097_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2082_, v_origin_2067_, v___x_2096_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 3, v___x_2097_);
lean_ctor_set(v___x_2084_, 2, v_erased_2090_);
lean_ctor_set(v___x_2084_, 1, v_origins_2089_);
lean_ctor_set(v___x_2084_, 0, v___y_2092_);
v___x_2099_ = v___x_2084_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___y_2092_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_origins_2089_);
lean_ctor_set(v_reuseFailAlloc_2100_, 2, v_erased_2090_);
lean_ctor_set(v_reuseFailAlloc_2100_, 3, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2104_; 
lean_dec(v___x_2093_);
v___x_2102_ = lean_box(0);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 1, v___x_2102_);
lean_ctor_set(v___x_2076_, 0, v_thm_2087_);
v___x_2104_ = v___x_2076_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_thm_2087_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2105_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2082_, v_origin_2067_, v___x_2104_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 3, v___x_2105_);
lean_ctor_set(v___x_2084_, 2, v_erased_2090_);
lean_ctor_set(v___x_2084_, 1, v_origins_2089_);
lean_ctor_set(v___x_2084_, 0, v___y_2092_);
v___x_2107_ = v___x_2084_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___y_2092_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_origins_2089_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_erased_2090_);
lean_ctor_set(v_reuseFailAlloc_2108_, 3, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
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
lean_dec(v_head_2062_);
lean_dec_ref_known(v_symbols_2061_, 2);
lean_dec_ref(v_thm_2057_);
lean_dec_ref(v_s_2056_);
goto v___jp_2058_;
}
}
else
{
lean_dec(v_symbols_2061_);
lean_dec_ref(v_thm_2057_);
lean_dec_ref(v_s_2056_);
goto v___jp_2058_;
}
v___jp_2058_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3, &l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3);
v___x_2060_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0(v___x_2059_);
return v___x_2060_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1_spec__6(lean_object* v_msg_2123_){
_start:
{
lean_object* v___f_2124_; lean_object* v___f_2125_; lean_object* v___f_2126_; lean_object* v___f_2127_; lean_object* v___f_2128_; lean_object* v___f_2129_; lean_object* v___f_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___f_2124_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0));
v___f_2125_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1));
v___f_2126_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2));
v___f_2127_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3));
v___f_2128_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4));
v___f_2129_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5));
v___f_2130_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6));
v___x_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___f_2124_);
lean_ctor_set(v___x_2131_, 1, v___f_2125_);
v___x_2132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v___f_2126_);
lean_ctor_set(v___x_2132_, 2, v___f_2127_);
lean_ctor_set(v___x_2132_, 3, v___f_2128_);
lean_ctor_set(v___x_2132_, 4, v___f_2129_);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_ctor_set(v___x_2133_, 1, v___f_2130_);
v___x_2134_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7, &l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once, _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7);
v___x_2135_ = l_instInhabitedOfMonad___redArg(v___x_2133_, v___x_2134_);
v___x_2136_ = lean_panic_fn_borrowed(v___x_2135_, v_msg_2123_);
lean_dec(v___x_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1(lean_object* v_s_2137_, lean_object* v_thm_2138_){
_start:
{
lean_object* v_symbols_2142_; 
v_symbols_2142_ = lean_ctor_get(v_thm_2138_, 2);
lean_inc(v_symbols_2142_);
if (lean_obj_tag(v_symbols_2142_) == 1)
{
lean_object* v_head_2143_; 
v_head_2143_ = lean_ctor_get(v_symbols_2142_, 0);
lean_inc(v_head_2143_);
if (lean_obj_tag(v_head_2143_) == 2)
{
lean_object* v_levelParams_2144_; lean_object* v_proof_2145_; lean_object* v_origin_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2197_; 
v_levelParams_2144_ = lean_ctor_get(v_thm_2138_, 0);
v_proof_2145_ = lean_ctor_get(v_thm_2138_, 1);
v_origin_2146_ = lean_ctor_get(v_thm_2138_, 3);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_thm_2138_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; 
v_unused_2198_ = lean_ctor_get(v_thm_2138_, 2);
lean_dec(v_unused_2198_);
v___x_2148_ = v_thm_2138_;
v_isShared_2149_ = v_isSharedCheck_2197_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_origin_2146_);
lean_inc(v_proof_2145_);
lean_inc(v_levelParams_2144_);
lean_dec(v_thm_2138_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2197_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v_tail_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2195_; 
v_tail_2150_ = lean_ctor_get(v_symbols_2142_, 1);
v_isSharedCheck_2195_ = !lean_is_exclusive(v_symbols_2142_);
if (v_isSharedCheck_2195_ == 0)
{
lean_object* v_unused_2196_; 
v_unused_2196_ = lean_ctor_get(v_symbols_2142_, 0);
lean_dec(v_unused_2196_);
v___x_2152_ = v_symbols_2142_;
v_isShared_2153_ = v_isSharedCheck_2195_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_tail_2150_);
lean_dec(v_symbols_2142_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2195_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v_constName_2154_; lean_object* v_smap_2155_; lean_object* v_origins_2156_; lean_object* v_erased_2157_; lean_object* v_omap_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2194_; 
v_constName_2154_ = lean_ctor_get(v_head_2143_, 0);
lean_inc(v_constName_2154_);
lean_dec_ref_known(v_head_2143_, 1);
v_smap_2155_ = lean_ctor_get(v_s_2137_, 0);
v_origins_2156_ = lean_ctor_get(v_s_2137_, 1);
v_erased_2157_ = lean_ctor_get(v_s_2137_, 2);
v_omap_2158_ = lean_ctor_get(v_s_2137_, 3);
v_isSharedCheck_2194_ = !lean_is_exclusive(v_s_2137_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2160_ = v_s_2137_;
v_isShared_2161_ = v_isSharedCheck_2194_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_omap_2158_);
lean_inc(v_erased_2157_);
lean_inc(v_origins_2156_);
lean_inc(v_smap_2155_);
lean_dec(v_s_2137_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2194_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v_thm_2163_; 
lean_inc_ref(v_origin_2146_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 2, v_tail_2150_);
v_thm_2163_ = v___x_2148_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_levelParams_2144_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_proof_2145_);
lean_ctor_set(v_reuseFailAlloc_2193_, 2, v_tail_2150_);
lean_ctor_set(v_reuseFailAlloc_2193_, 3, v_origin_2146_);
v_thm_2163_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2164_; lean_object* v_origins_2165_; lean_object* v_erased_2166_; lean_object* v___y_2168_; lean_object* v___x_2186_; 
v___x_2164_ = lean_box(0);
lean_inc_ref(v_origin_2146_);
v_origins_2165_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_origins_2156_, v_origin_2146_, v___x_2164_);
v_erased_2166_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_erased_2157_, v_origin_2146_);
v___x_2186_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_smap_2155_, v_constName_2154_);
if (lean_obj_tag(v___x_2186_) == 1)
{
lean_object* v_val_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v_val_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_val_2187_);
lean_dec_ref_known(v___x_2186_, 1);
lean_inc_ref(v_thm_2163_);
v___x_2188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2188_, 0, v_thm_2163_);
lean_ctor_set(v___x_2188_, 1, v_val_2187_);
v___x_2189_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2155_, v_constName_2154_, v___x_2188_);
v___y_2168_ = v___x_2189_;
goto v___jp_2167_;
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_dec(v___x_2186_);
v___x_2190_ = lean_box(0);
lean_inc_ref(v_thm_2163_);
v___x_2191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2191_, 0, v_thm_2163_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2155_, v_constName_2154_, v___x_2191_);
v___y_2168_ = v___x_2192_;
goto v___jp_2167_;
}
v___jp_2167_:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_omap_2158_, v_origin_2146_);
if (lean_obj_tag(v___x_2169_) == 1)
{
lean_object* v_val_2170_; lean_object* v___x_2172_; 
v_val_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_val_2170_);
lean_dec_ref_known(v___x_2169_, 1);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 1, v_val_2170_);
lean_ctor_set(v___x_2152_, 0, v_thm_2163_);
v___x_2172_ = v___x_2152_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_thm_2163_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_val_2170_);
v___x_2172_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v___x_2173_; lean_object* v___x_2175_; 
v___x_2173_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2158_, v_origin_2146_, v___x_2172_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 3, v___x_2173_);
lean_ctor_set(v___x_2160_, 2, v_erased_2166_);
lean_ctor_set(v___x_2160_, 1, v_origins_2165_);
lean_ctor_set(v___x_2160_, 0, v___y_2168_);
v___x_2175_ = v___x_2160_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___y_2168_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_origins_2165_);
lean_ctor_set(v_reuseFailAlloc_2176_, 2, v_erased_2166_);
lean_ctor_set(v_reuseFailAlloc_2176_, 3, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2180_; 
lean_dec(v___x_2169_);
v___x_2178_ = lean_box(0);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 1, v___x_2178_);
lean_ctor_set(v___x_2152_, 0, v_thm_2163_);
v___x_2180_ = v___x_2152_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_thm_2163_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2181_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2158_, v_origin_2146_, v___x_2180_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 3, v___x_2181_);
lean_ctor_set(v___x_2160_, 2, v_erased_2166_);
lean_ctor_set(v___x_2160_, 1, v_origins_2165_);
lean_ctor_set(v___x_2160_, 0, v___y_2168_);
v___x_2183_ = v___x_2160_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___y_2168_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_origins_2165_);
lean_ctor_set(v_reuseFailAlloc_2184_, 2, v_erased_2166_);
lean_ctor_set(v_reuseFailAlloc_2184_, 3, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
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
lean_dec_ref_known(v_symbols_2142_, 2);
lean_dec(v_head_2143_);
lean_dec_ref(v_thm_2138_);
lean_dec_ref(v_s_2137_);
goto v___jp_2139_;
}
}
else
{
lean_dec(v_symbols_2142_);
lean_dec_ref(v_thm_2138_);
lean_dec_ref(v_s_2137_);
goto v___jp_2139_;
}
v___jp_2139_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3, &l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3);
v___x_2141_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1_spec__6(v___x_2140_);
return v___x_2141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionState_addEntry(lean_object* v_s_2199_, lean_object* v_e_2200_){
_start:
{
switch(lean_obj_tag(v_e_2200_))
{
case 0:
{
lean_object* v_declName_2201_; lean_object* v_casesTypes_2202_; lean_object* v_extThms_2203_; lean_object* v_funCC_2204_; lean_object* v_ematch_2205_; lean_object* v_inj_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2215_; 
v_declName_2201_ = lean_ctor_get(v_e_2200_, 0);
lean_inc(v_declName_2201_);
lean_dec_ref_known(v_e_2200_, 1);
v_casesTypes_2202_ = lean_ctor_get(v_s_2199_, 0);
v_extThms_2203_ = lean_ctor_get(v_s_2199_, 1);
v_funCC_2204_ = lean_ctor_get(v_s_2199_, 2);
v_ematch_2205_ = lean_ctor_get(v_s_2199_, 3);
v_inj_2206_ = lean_ctor_get(v_s_2199_, 4);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_s_2199_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2208_ = v_s_2199_;
v_isShared_2209_ = v_isSharedCheck_2215_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_inj_2206_);
lean_inc(v_ematch_2205_);
lean_inc(v_funCC_2204_);
lean_inc(v_extThms_2203_);
lean_inc(v_casesTypes_2202_);
lean_dec(v_s_2199_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2215_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2210_ = lean_box(0);
v___x_2211_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_extThms_2203_, v_declName_2201_, v___x_2210_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 1, v___x_2211_);
v___x_2213_ = v___x_2208_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_casesTypes_2202_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2214_, 2, v_funCC_2204_);
lean_ctor_set(v_reuseFailAlloc_2214_, 3, v_ematch_2205_);
lean_ctor_set(v_reuseFailAlloc_2214_, 4, v_inj_2206_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
case 1:
{
lean_object* v_declName_2216_; lean_object* v_casesTypes_2217_; lean_object* v_extThms_2218_; lean_object* v_funCC_2219_; lean_object* v_ematch_2220_; lean_object* v_inj_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2229_; 
v_declName_2216_ = lean_ctor_get(v_e_2200_, 0);
lean_inc(v_declName_2216_);
lean_dec_ref_known(v_e_2200_, 1);
v_casesTypes_2217_ = lean_ctor_get(v_s_2199_, 0);
v_extThms_2218_ = lean_ctor_get(v_s_2199_, 1);
v_funCC_2219_ = lean_ctor_get(v_s_2199_, 2);
v_ematch_2220_ = lean_ctor_get(v_s_2199_, 3);
v_inj_2221_ = lean_ctor_get(v_s_2199_, 4);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_s_2199_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2223_ = v_s_2199_;
v_isShared_2224_ = v_isSharedCheck_2229_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_inj_2221_);
lean_inc(v_ematch_2220_);
lean_inc(v_funCC_2219_);
lean_inc(v_extThms_2218_);
lean_inc(v_casesTypes_2217_);
lean_dec(v_s_2199_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2229_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2225_ = l_Lean_NameSet_insert(v_funCC_2219_, v_declName_2216_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 2, v___x_2225_);
v___x_2227_ = v___x_2223_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_casesTypes_2217_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_extThms_2218_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v___x_2225_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v_ematch_2220_);
lean_ctor_set(v_reuseFailAlloc_2228_, 4, v_inj_2221_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
case 2:
{
lean_object* v_declName_2230_; uint8_t v_eager_2231_; lean_object* v_casesTypes_2232_; lean_object* v_extThms_2233_; lean_object* v_funCC_2234_; lean_object* v_ematch_2235_; lean_object* v_inj_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2245_; 
v_declName_2230_ = lean_ctor_get(v_e_2200_, 0);
lean_inc(v_declName_2230_);
v_eager_2231_ = lean_ctor_get_uint8(v_e_2200_, sizeof(void*)*1);
lean_dec_ref_known(v_e_2200_, 1);
v_casesTypes_2232_ = lean_ctor_get(v_s_2199_, 0);
v_extThms_2233_ = lean_ctor_get(v_s_2199_, 1);
v_funCC_2234_ = lean_ctor_get(v_s_2199_, 2);
v_ematch_2235_ = lean_ctor_get(v_s_2199_, 3);
v_inj_2236_ = lean_ctor_get(v_s_2199_, 4);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_s_2199_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2238_ = v_s_2199_;
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
lean_dec(v_s_2199_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2245_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2243_; 
v___x_2240_ = lean_box(v_eager_2231_);
v___x_2241_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_casesTypes_2232_, v_declName_2230_, v___x_2240_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2241_);
v___x_2243_ = v___x_2238_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2241_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_extThms_2233_);
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
case 3:
{
lean_object* v_thm_2246_; lean_object* v_casesTypes_2247_; lean_object* v_extThms_2248_; lean_object* v_funCC_2249_; lean_object* v_ematch_2250_; lean_object* v_inj_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2259_; 
v_thm_2246_ = lean_ctor_get(v_e_2200_, 0);
lean_inc_ref(v_thm_2246_);
lean_dec_ref_known(v_e_2200_, 1);
v_casesTypes_2247_ = lean_ctor_get(v_s_2199_, 0);
v_extThms_2248_ = lean_ctor_get(v_s_2199_, 1);
v_funCC_2249_ = lean_ctor_get(v_s_2199_, 2);
v_ematch_2250_ = lean_ctor_get(v_s_2199_, 3);
v_inj_2251_ = lean_ctor_get(v_s_2199_, 4);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_s_2199_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2253_ = v_s_2199_;
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
lean_dec(v_s_2199_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2259_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; lean_object* v___x_2257_; 
v___x_2255_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0(v_ematch_2250_, v_thm_2246_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 3, v___x_2255_);
v___x_2257_ = v___x_2253_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_casesTypes_2247_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_extThms_2248_);
lean_ctor_set(v_reuseFailAlloc_2258_, 2, v_funCC_2249_);
lean_ctor_set(v_reuseFailAlloc_2258_, 3, v___x_2255_);
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
default: 
{
lean_object* v_thm_2260_; lean_object* v_casesTypes_2261_; lean_object* v_extThms_2262_; lean_object* v_funCC_2263_; lean_object* v_ematch_2264_; lean_object* v_inj_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2273_; 
v_thm_2260_ = lean_ctor_get(v_e_2200_, 0);
lean_inc_ref(v_thm_2260_);
lean_dec_ref_known(v_e_2200_, 1);
v_casesTypes_2261_ = lean_ctor_get(v_s_2199_, 0);
v_extThms_2262_ = lean_ctor_get(v_s_2199_, 1);
v_funCC_2263_ = lean_ctor_get(v_s_2199_, 2);
v_ematch_2264_ = lean_ctor_get(v_s_2199_, 3);
v_inj_2265_ = lean_ctor_get(v_s_2199_, 4);
v_isSharedCheck_2273_ = !lean_is_exclusive(v_s_2199_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2267_ = v_s_2199_;
v_isShared_2268_ = v_isSharedCheck_2273_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_inj_2265_);
lean_inc(v_ematch_2264_);
lean_inc(v_funCC_2263_);
lean_inc(v_extThms_2262_);
lean_inc(v_casesTypes_2261_);
lean_dec(v_s_2199_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2273_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2269_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1(v_inj_2265_, v_thm_2260_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 4, v___x_2269_);
v___x_2271_ = v___x_2267_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_casesTypes_2261_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v_extThms_2262_);
lean_ctor_set(v_reuseFailAlloc_2272_, 2, v_funCC_2263_);
lean_ctor_set(v_reuseFailAlloc_2272_, 3, v_ematch_2264_);
lean_ctor_set(v_reuseFailAlloc_2272_, 4, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1(lean_object* v_00_u03b2_2274_, lean_object* v_x_2275_, lean_object* v_x_2276_, lean_object* v_x_2277_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_x_2275_, v_x_2276_, v_x_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2(lean_object* v_00_u03b2_2279_, lean_object* v_x_2280_, lean_object* v_x_2281_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_x_2280_, v_x_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2283_, lean_object* v_x_2284_, lean_object* v_x_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2(v_00_u03b2_2283_, v_x_2284_, v_x_2285_);
lean_dec_ref(v_x_2285_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3(lean_object* v_00_u03b2_2287_, lean_object* v_x_2288_, lean_object* v_x_2289_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_x_2288_, v_x_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2291_, lean_object* v_x_2292_, lean_object* v_x_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3(v_00_u03b2_2291_, v_x_2292_, v_x_2293_);
lean_dec_ref(v_x_2293_);
lean_dec_ref(v_x_2292_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4(lean_object* v_00_u03b2_2295_, lean_object* v_x_2296_, lean_object* v_x_2297_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_x_2296_, v_x_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___boxed(lean_object* v_00_u03b2_2299_, lean_object* v_x_2300_, lean_object* v_x_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4(v_00_u03b2_2299_, v_x_2300_, v_x_2301_);
lean_dec(v_x_2301_);
lean_dec_ref(v_x_2300_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2303_, lean_object* v_x_2304_, size_t v_x_2305_, size_t v_x_2306_, lean_object* v_x_2307_, lean_object* v_x_2308_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_2304_, v_x_2305_, v_x_2306_, v_x_2307_, v_x_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2310_, lean_object* v_x_2311_, lean_object* v_x_2312_, lean_object* v_x_2313_, lean_object* v_x_2314_, lean_object* v_x_2315_){
_start:
{
size_t v_x_2255__boxed_2316_; size_t v_x_2256__boxed_2317_; lean_object* v_res_2318_; 
v_x_2255__boxed_2316_ = lean_unbox_usize(v_x_2312_);
lean_dec(v_x_2312_);
v_x_2256__boxed_2317_ = lean_unbox_usize(v_x_2313_);
lean_dec(v_x_2313_);
v_res_2318_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(v_00_u03b2_2310_, v_x_2311_, v_x_2255__boxed_2316_, v_x_2256__boxed_2317_, v_x_2314_, v_x_2315_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2319_, lean_object* v_x_2320_, size_t v_x_2321_, lean_object* v_x_2322_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2320_, v_x_2321_, v_x_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2324_, lean_object* v_x_2325_, lean_object* v_x_2326_, lean_object* v_x_2327_){
_start:
{
size_t v_x_2272__boxed_2328_; lean_object* v_res_2329_; 
v_x_2272__boxed_2328_ = lean_unbox_usize(v_x_2326_);
lean_dec(v_x_2326_);
v_res_2329_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(v_00_u03b2_2324_, v_x_2325_, v_x_2272__boxed_2328_, v_x_2327_);
lean_dec_ref(v_x_2327_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(lean_object* v_00_u03b2_2330_, lean_object* v_x_2331_, size_t v_x_2332_, lean_object* v_x_2333_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_2331_, v_x_2332_, v_x_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2335_, lean_object* v_x_2336_, lean_object* v_x_2337_, lean_object* v_x_2338_){
_start:
{
size_t v_x_2283__boxed_2339_; lean_object* v_res_2340_; 
v_x_2283__boxed_2339_ = lean_unbox_usize(v_x_2337_);
lean_dec(v_x_2337_);
v_res_2340_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(v_00_u03b2_2335_, v_x_2336_, v_x_2283__boxed_2339_, v_x_2338_);
lean_dec_ref(v_x_2338_);
lean_dec_ref(v_x_2336_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(lean_object* v_00_u03b2_2341_, lean_object* v_x_2342_, size_t v_x_2343_, lean_object* v_x_2344_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_2342_, v_x_2343_, v_x_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_, lean_object* v_x_2349_){
_start:
{
size_t v_x_2294__boxed_2350_; lean_object* v_res_2351_; 
v_x_2294__boxed_2350_ = lean_unbox_usize(v_x_2348_);
lean_dec(v_x_2348_);
v_res_2351_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(v_00_u03b2_2346_, v_x_2347_, v_x_2294__boxed_2350_, v_x_2349_);
lean_dec(v_x_2349_);
lean_dec_ref(v_x_2347_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2352_, lean_object* v_n_2353_, lean_object* v_k_2354_, lean_object* v_v_2355_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(v_n_2353_, v_k_2354_, v_v_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2357_, size_t v_depth_2358_, lean_object* v_keys_2359_, lean_object* v_vals_2360_, lean_object* v_heq_2361_, lean_object* v_i_2362_, lean_object* v_entries_2363_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_depth_2358_, v_keys_2359_, v_vals_2360_, v_i_2362_, v_entries_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2365_, lean_object* v_depth_2366_, lean_object* v_keys_2367_, lean_object* v_vals_2368_, lean_object* v_heq_2369_, lean_object* v_i_2370_, lean_object* v_entries_2371_){
_start:
{
size_t v_depth_boxed_2372_; lean_object* v_res_2373_; 
v_depth_boxed_2372_ = lean_unbox_usize(v_depth_2366_);
lean_dec(v_depth_2366_);
v_res_2373_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(v_00_u03b2_2365_, v_depth_boxed_2372_, v_keys_2367_, v_vals_2368_, v_heq_2369_, v_i_2370_, v_entries_2371_);
lean_dec_ref(v_vals_2368_);
lean_dec_ref(v_keys_2367_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12(lean_object* v_00_u03b2_2374_, lean_object* v_keys_2375_, lean_object* v_vals_2376_, lean_object* v_heq_2377_, lean_object* v_i_2378_, lean_object* v_k_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_keys_2375_, v_vals_2376_, v_i_2378_, v_k_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___boxed(lean_object* v_00_u03b2_2381_, lean_object* v_keys_2382_, lean_object* v_vals_2383_, lean_object* v_heq_2384_, lean_object* v_i_2385_, lean_object* v_k_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12(v_00_u03b2_2381_, v_keys_2382_, v_vals_2383_, v_heq_2384_, v_i_2385_, v_k_2386_);
lean_dec_ref(v_k_2386_);
lean_dec_ref(v_vals_2383_);
lean_dec_ref(v_keys_2382_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15(lean_object* v_00_u03b2_2388_, lean_object* v_keys_2389_, lean_object* v_vals_2390_, lean_object* v_heq_2391_, lean_object* v_i_2392_, lean_object* v_k_2393_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_keys_2389_, v_vals_2390_, v_i_2392_, v_k_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___boxed(lean_object* v_00_u03b2_2395_, lean_object* v_keys_2396_, lean_object* v_vals_2397_, lean_object* v_heq_2398_, lean_object* v_i_2399_, lean_object* v_k_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15(v_00_u03b2_2395_, v_keys_2396_, v_vals_2397_, v_heq_2398_, v_i_2399_, v_k_2400_);
lean_dec(v_k_2400_);
lean_dec_ref(v_vals_2397_);
lean_dec_ref(v_keys_2396_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_2402_, lean_object* v_x_2403_, lean_object* v_x_2404_, lean_object* v_x_2405_, lean_object* v_x_2406_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(v_x_2403_, v_x_2404_, v_x_2405_, v_x_2406_);
return v___x_2407_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__10));
v___x_2435_ = l_Lean_mkAtom(v___x_2434_);
return v___x_2435_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2436_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__12, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__12_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__12);
v___x_2437_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2438_ = lean_array_push(v___x_2437_, v___x_2436_);
return v___x_2438_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__17));
v___x_2448_ = l_Lean_mkAtom(v___x_2447_);
return v___x_2448_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2449_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__18, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__18_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__18);
v___x_2450_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2451_ = lean_array_push(v___x_2450_, v___x_2449_);
return v___x_2451_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__20(void){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2452_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__19, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__19_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__19);
v___x_2453_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__16));
v___x_2454_ = lean_box(2);
v___x_2455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2454_);
lean_ctor_set(v___x_2455_, 1, v___x_2453_);
lean_ctor_set(v___x_2455_, 2, v___x_2452_);
return v___x_2455_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__21(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2456_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__20, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__20_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__20);
v___x_2457_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__13, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__13_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__13);
v___x_2458_ = lean_array_push(v___x_2457_, v___x_2456_);
return v___x_2458_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__22(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2459_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__21, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__21_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__21);
v___x_2460_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__11));
v___x_2461_ = lean_box(2);
v___x_2462_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
lean_ctor_set(v___x_2462_, 1, v___x_2460_);
lean_ctor_set(v___x_2462_, 2, v___x_2459_);
return v___x_2462_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2463_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__22, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__22_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__22);
v___x_2464_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2465_ = lean_array_push(v___x_2464_, v___x_2463_);
return v___x_2465_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2466_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__23, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__23_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__23);
v___x_2467_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__9));
v___x_2468_ = lean_box(2);
v___x_2469_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
lean_ctor_set(v___x_2469_, 1, v___x_2467_);
lean_ctor_set(v___x_2469_, 2, v___x_2466_);
return v___x_2469_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__25(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__24, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__24_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__24);
v___x_2471_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2472_ = lean_array_push(v___x_2471_, v___x_2470_);
return v___x_2472_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__26(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2473_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__25, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__25_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__25);
v___x_2474_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__7));
v___x_2475_ = lean_box(2);
v___x_2476_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
lean_ctor_set(v___x_2476_, 1, v___x_2474_);
lean_ctor_set(v___x_2476_, 2, v___x_2473_);
return v___x_2476_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__27(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__26, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__26_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__26);
v___x_2478_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2479_ = lean_array_push(v___x_2478_, v___x_2477_);
return v___x_2479_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__28(void){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2480_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__27, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__27_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__27);
v___x_2481_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__4));
v___x_2482_ = lean_box(2);
v___x_2483_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
lean_ctor_set(v___x_2483_, 1, v___x_2481_);
lean_ctor_set(v___x_2483_, 2, v___x_2480_);
return v___x_2483_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1(void){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__28, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__28_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__28);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(lean_object* v_msg_2485_){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = lean_box(0);
v___x_2487_ = lean_panic_fn_borrowed(v___x_2486_, v_msg_2485_);
return v___x_2487_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2490_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2));
v___x_2491_ = lean_unsigned_to_nat(17u);
v___x_2492_ = lean_unsigned_to_nat(203u);
v___x_2493_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___lam__0___closed__1));
v___x_2494_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___lam__0___closed__0));
v___x_2495_ = l_mkPanicMessageWithDecl(v___x_2494_, v___x_2493_, v___x_2492_, v___x_2491_, v___x_2490_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__0(lean_object* v_x_2496_, lean_object* v_e_2497_){
_start:
{
lean_object* v___y_2499_; 
switch(lean_obj_tag(v_e_2497_))
{
case 3:
{
lean_object* v_thm_2506_; lean_object* v_origin_2507_; 
v_thm_2506_ = lean_ctor_get(v_e_2497_, 0);
v_origin_2507_ = lean_ctor_get(v_thm_2506_, 5);
if (lean_obj_tag(v_origin_2507_) == 0)
{
lean_object* v_declName_2508_; 
v_declName_2508_ = lean_ctor_get(v_origin_2507_, 0);
lean_inc(v_declName_2508_);
v___y_2499_ = v_declName_2508_;
goto v___jp_2498_;
}
else
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___lam__0___closed__2, &l_Lean_Meta_Grind_mkExtension___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2);
v___x_2510_ = l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(v___x_2509_);
v___y_2499_ = v___x_2510_;
goto v___jp_2498_;
}
}
case 4:
{
lean_object* v_thm_2511_; lean_object* v_origin_2512_; 
v_thm_2511_ = lean_ctor_get(v_e_2497_, 0);
v_origin_2512_ = lean_ctor_get(v_thm_2511_, 3);
if (lean_obj_tag(v_origin_2512_) == 0)
{
lean_object* v_declName_2513_; 
v_declName_2513_ = lean_ctor_get(v_origin_2512_, 0);
lean_inc(v_declName_2513_);
v___y_2499_ = v_declName_2513_;
goto v___jp_2498_;
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___lam__0___closed__2, &l_Lean_Meta_Grind_mkExtension___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2);
v___x_2515_ = l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(v___x_2514_);
v___y_2499_ = v___x_2515_;
goto v___jp_2498_;
}
}
default: 
{
lean_object* v_declName_2516_; 
v_declName_2516_ = lean_ctor_get(v_e_2497_, 0);
lean_inc(v_declName_2516_);
v___y_2499_ = v_declName_2516_;
goto v___jp_2498_;
}
}
v___jp_2498_:
{
uint8_t v___x_2500_; 
v___x_2500_ = l_Lean_isPrivateName(v___y_2499_);
lean_dec(v___y_2499_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2501_, 0, v_e_2497_);
lean_inc_ref_n(v___x_2501_, 2);
v___x_2502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
lean_ctor_set(v___x_2502_, 2, v___x_2501_);
return v___x_2502_;
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = lean_box(0);
v___x_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2504_, 0, v_e_2497_);
v___x_2505_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set(v___x_2505_, 1, v___x_2503_);
lean_ctor_set(v___x_2505_, 2, v___x_2504_);
return v___x_2505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__0___boxed(lean_object* v_x_2517_, lean_object* v_e_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_Meta_Grind_mkExtension___lam__0(v_x_2517_, v_e_2518_);
lean_dec_ref(v_x_2517_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__1(lean_object* v___y_2520_){
_start:
{
lean_inc_ref(v___y_2520_);
return v___y_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__1___boxed(lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_Meta_Grind_mkExtension___lam__1(v___y_2521_);
lean_dec_ref(v___y_2521_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension(lean_object* v_name_2526_){
_start:
{
lean_object* v___f_2528_; lean_object* v___f_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___f_2528_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__0));
v___f_2529_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__1));
v___x_2530_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__2));
v___x_2531_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1);
v___x_2532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2532_, 0, v_name_2526_);
lean_ctor_set(v___x_2532_, 1, v___x_2530_);
lean_ctor_set(v___x_2532_, 2, v___x_2531_);
lean_ctor_set(v___x_2532_, 3, v___f_2529_);
lean_ctor_set(v___x_2532_, 4, v___f_2528_);
v___x_2533_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2532_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___boxed(lean_object* v_name_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_Meta_Grind_mkExtension(v_name_2534_);
return v_res_2536_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0, &l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0);
v___x_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
return v___x_2538_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2539_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0);
v___x_2540_ = lean_unsigned_to_nat(0u);
v___x_2541_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
lean_ctor_set(v___x_2541_, 2, v___x_2540_);
lean_ctor_set(v___x_2541_, 3, v___x_2540_);
lean_ctor_set(v___x_2541_, 4, v___x_2539_);
lean_ctor_set(v___x_2541_, 5, v___x_2539_);
lean_ctor_set(v___x_2541_, 6, v___x_2539_);
lean_ctor_set(v___x_2541_, 7, v___x_2539_);
lean_ctor_set(v___x_2541_, 8, v___x_2539_);
lean_ctor_set(v___x_2541_, 9, v___x_2539_);
lean_ctor_set(v___x_2541_, 10, v___x_2539_);
return v___x_2541_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = lean_unsigned_to_nat(32u);
v___x_2543_ = lean_mk_empty_array_with_capacity(v___x_2542_);
v___x_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
return v___x_2544_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2545_ = ((size_t)5ULL);
v___x_2546_ = lean_unsigned_to_nat(0u);
v___x_2547_ = lean_unsigned_to_nat(32u);
v___x_2548_ = lean_mk_empty_array_with_capacity(v___x_2547_);
v___x_2549_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2);
v___x_2550_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set(v___x_2550_, 1, v___x_2548_);
lean_ctor_set(v___x_2550_, 2, v___x_2546_);
lean_ctor_set(v___x_2550_, 3, v___x_2546_);
lean_ctor_set_usize(v___x_2550_, 4, v___x_2545_);
return v___x_2550_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2551_ = lean_box(1);
v___x_2552_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3);
v___x_2553_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0);
v___x_2554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
lean_ctor_set(v___x_2554_, 1, v___x_2552_);
lean_ctor_set(v___x_2554_, 2, v___x_2551_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(lean_object* v_msgData_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v___x_2559_; lean_object* v_toCold_2560_; lean_object* v_env_2561_; lean_object* v_options_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2559_ = lean_st_ref_get(v___y_2557_);
v_toCold_2560_ = lean_ctor_get(v___y_2556_, 0);
v_env_2561_ = lean_ctor_get(v___x_2559_, 0);
lean_inc_ref(v_env_2561_);
lean_dec(v___x_2559_);
v_options_2562_ = lean_ctor_get(v_toCold_2560_, 2);
v___x_2563_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1);
v___x_2564_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4);
lean_inc_ref(v_options_2562_);
v___x_2565_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2565_, 0, v_env_2561_);
lean_ctor_set(v___x_2565_, 1, v___x_2563_);
lean_ctor_set(v___x_2565_, 2, v___x_2564_);
lean_ctor_set(v___x_2565_, 3, v_options_2562_);
v___x_2566_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
lean_ctor_set(v___x_2566_, 1, v_msgData_2555_);
v___x_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___boxed(lean_object* v_msgData_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(v_msgData_2568_, v___y_2569_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(lean_object* v_msg_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v_ref_2577_; lean_object* v___x_2578_; lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2587_; 
v_ref_2577_ = lean_ctor_get(v___y_2574_, 2);
v___x_2578_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(v_msg_2573_, v___y_2574_, v___y_2575_);
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2587_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2587_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2585_; 
lean_inc(v_ref_2577_);
v___x_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2583_, 0, v_ref_2577_);
lean_ctor_set(v___x_2583_, 1, v_a_2579_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set_tag(v___x_2581_, 1);
lean_ctor_set(v___x_2581_, 0, v___x_2583_);
v___x_2585_ = v___x_2581_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg___boxed(lean_object* v_msg_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v_msg_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
return v_res_2592_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = ((lean_object*)(l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__0));
v___x_2595_ = l_Lean_stringToMessageData(v___x_2594_);
return v___x_2595_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3(void){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2597_ = ((lean_object*)(l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__2));
v___x_2598_ = l_Lean_stringToMessageData(v___x_2597_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object* v_declName_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v___x_2603_; uint8_t v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2603_ = lean_obj_once(&l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1, &l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1);
v___x_2604_ = 0;
v___x_2605_ = l_Lean_MessageData_ofConstName(v_declName_2599_, v___x_2604_);
v___x_2606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2603_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
v___x_2607_ = lean_obj_once(&l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3, &l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3_once, _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3);
v___x_2608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2606_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v___x_2608_, v_a_2600_, v_a_2601_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___boxed(lean_object* v_declName_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2610_, v_a_2611_, v_a_2612_);
lean_dec(v_a_2612_);
lean_dec_ref(v_a_2611_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(lean_object* v_00_u03b1_2615_, lean_object* v_declName_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2616_, v_a_2617_, v_a_2618_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___boxed(lean_object* v_00_u03b1_2621_, lean_object* v_declName_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(v_00_u03b1_2621_, v_declName_2622_, v_a_2623_, v_a_2624_);
lean_dec(v_a_2624_);
lean_dec_ref(v_a_2623_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(lean_object* v_00_u03b1_2627_, lean_object* v_msg_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v_msg_2628_, v___y_2629_, v___y_2630_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___boxed(lean_object* v_00_u03b1_2633_, lean_object* v_msg_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(v_00_u03b1_2633_, v_msg_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
return v_res_2638_;
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
