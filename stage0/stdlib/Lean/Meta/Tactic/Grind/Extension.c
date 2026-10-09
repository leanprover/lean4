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
lean_object* lean_obj_tag_nat(lean_object*);
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorIdx___impl___boxed(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(lean_object* v_x_42_, size_t v_x_43_, size_t v_x_44_, lean_object* v_x_45_, lean_object* v_x_46_){
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
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_42_ = stack[0].m_obj;
size_t v_x_43_ = stack[1].m_num;
size_t v_x_44_ = stack[2].m_num;
lean_object* v_x_45_ = stack[3].m_obj;
lean_object* v_x_46_ = stack[4].m_obj;
lean_object* v_res_113_;
v_res_113_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_42_, v_x_43_, v_x_44_, v_x_45_, v_x_46_);
stack->m_obj
 = v_res_113_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(size_t v_depth_114_, lean_object* v_keys_115_, lean_object* v_vals_116_, lean_object* v_i_117_, lean_object* v_entries_118_){
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
lean_object* v_k_121_; lean_object* v_v_122_; uint64_t v___y_124_; 
v_k_121_ = lean_array_fget_borrowed(v_keys_115_, v_i_117_);
v_v_122_ = lean_array_fget_borrowed(v_vals_116_, v_i_117_);
if (lean_obj_tag(v_k_121_) == 0)
{
uint64_t v___x_135_; 
v___x_135_ = 1723ULL;
v___y_124_ = v___x_135_;
goto v___jp_123_;
}
else
{
uint64_t v_hash_136_; 
v_hash_136_ = lean_ctor_get_uint64(v_k_121_, sizeof(void*)*2);
v___y_124_ = v_hash_136_;
goto v___jp_123_;
}
v___jp_123_:
{
size_t v_h_125_; size_t v___x_126_; lean_object* v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v_h_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_h_125_ = lean_uint64_to_usize(v___y_124_);
v___x_126_ = ((size_t)5ULL);
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_sub(v_depth_114_, v___x_128_);
v___x_130_ = lean_usize_mul(v___x_126_, v___x_129_);
v_h_131_ = lean_usize_shift_right(v_h_125_, v___x_130_);
v___x_132_ = lean_nat_add(v_i_117_, v___x_127_);
lean_dec(v_i_117_);
lean_inc(v_v_122_);
lean_inc(v_k_121_);
v___x_133_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_entries_118_, v_h_131_, v_depth_114_, v_k_121_, v_v_122_);
v_i_117_ = v___x_132_;
v_entries_118_ = v___x_133_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_114_ = stack[0].m_num;
lean_object* v_keys_115_ = stack[1].m_obj;
lean_object* v_vals_116_ = stack[2].m_obj;
lean_object* v_i_117_ = stack[3].m_obj;
lean_object* v_entries_118_ = stack[4].m_obj;
lean_object* v_res_137_;
v_res_137_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_depth_114_, v_keys_115_, v_vals_116_, v_i_117_, v_entries_118_);
stack->m_obj
 = v_res_137_;
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
size_t v_x_389__boxed_150_; size_t v_x_390__boxed_151_; lean_object* v_res_152_; 
v_x_389__boxed_150_ = lean_unbox_usize(v_x_146_);
lean_dec(v_x_146_);
v_x_390__boxed_151_ = lean_unbox_usize(v_x_147_);
lean_dec(v_x_147_);
v_res_152_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_145_, v_x_389__boxed_150_, v_x_390__boxed_151_, v_x_148_, v_x_149_);
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
lean_object* l_Lean_Meta_Grind_CasesTypes_insert(lean_object* v_s_163_, lean_object* v_declName_164_, uint8_t v_eager_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_box(v_eager_165_);
v___x_167_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_s_163_, v_declName_164_, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_CasesTypes_insert_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_163_ = stack[0].m_obj;
lean_object* v_declName_164_ = stack[1].m_obj;
uint8_t v_eager_165_ = stack[2].m_num;
lean_object* v_res_168_;
v_res_168_ = l_Lean_Meta_Grind_CasesTypes_insert(v_s_163_, v_declName_164_, v_eager_165_);
stack->m_obj
 = v_res_168_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_CasesTypes_insert___boxed(lean_object* v_s_169_, lean_object* v_declName_170_, lean_object* v_eager_171_){
_start:
{
uint8_t v_eager_boxed_172_; lean_object* v_res_173_; 
v_eager_boxed_172_ = lean_unbox(v_eager_171_);
v_res_173_ = l_Lean_Meta_Grind_CasesTypes_insert(v_s_169_, v_declName_170_, v_eager_boxed_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0(lean_object* v_00_u03b2_174_, lean_object* v_x_175_, lean_object* v_x_176_, lean_object* v_x_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_x_175_, v_x_176_, v_x_177_);
return v___x_178_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0(lean_object* v_00_u03b2_179_, lean_object* v_x_180_, size_t v_x_181_, size_t v_x_182_, lean_object* v_x_183_, lean_object* v_x_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg(v_x_180_, v_x_181_, v_x_182_, v_x_183_, v_x_184_);
return v___x_185_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_180_ = stack[1].m_obj;
size_t v_x_181_ = stack[2].m_num;
size_t v_x_182_ = stack[3].m_num;
lean_object* v_x_183_ = stack[4].m_obj;
lean_object* v_x_184_ = stack[5].m_obj;
lean_object* v_res_186_;
v_res_186_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0(lean_box(0), v_x_180_, v_x_181_, v_x_182_, v_x_183_, v_x_184_);
stack->m_obj
 = v_res_186_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
size_t v_x_674__boxed_193_; size_t v_x_675__boxed_194_; lean_object* v_res_195_; 
v_x_674__boxed_193_ = lean_unbox_usize(v_x_189_);
lean_dec(v_x_189_);
v_x_675__boxed_194_ = lean_unbox_usize(v_x_190_);
lean_dec(v_x_190_);
v_res_195_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0(v_00_u03b2_187_, v_x_188_, v_x_674__boxed_193_, v_x_675__boxed_194_, v_x_191_, v_x_192_);
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
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_201_, size_t v_depth_202_, lean_object* v_keys_203_, lean_object* v_vals_204_, lean_object* v_heq_205_, lean_object* v_i_206_, lean_object* v_entries_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___redArg(v_depth_202_, v_keys_203_, v_vals_204_, v_i_206_, v_entries_207_);
return v___x_208_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_202_ = stack[1].m_num;
lean_object* v_keys_203_ = stack[2].m_obj;
lean_object* v_vals_204_ = stack[3].m_obj;
lean_object* v_i_206_ = stack[5].m_obj;
lean_object* v_entries_207_ = stack[6].m_obj;
lean_object* v_res_209_;
v_res_209_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2(lean_box(0), v_depth_202_, v_keys_203_, v_vals_204_, lean_box(0), v_i_206_, v_entries_207_);
stack->m_obj
 = v_res_209_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_210_, lean_object* v_depth_211_, lean_object* v_keys_212_, lean_object* v_vals_213_, lean_object* v_heq_214_, lean_object* v_i_215_, lean_object* v_entries_216_){
_start:
{
size_t v_depth_boxed_217_; lean_object* v_res_218_; 
v_depth_boxed_217_ = lean_unbox_usize(v_depth_211_);
lean_dec(v_depth_211_);
v_res_218_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__2(v_00_u03b2_210_, v_depth_boxed_217_, v_keys_212_, v_vals_213_, v_heq_214_, v_i_215_, v_entries_216_);
lean_dec_ref(v_vals_213_);
lean_dec_ref(v_keys_212_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_219_, lean_object* v_x_220_, lean_object* v_x_221_, lean_object* v_x_222_, lean_object* v_x_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_220_, v_x_221_, v_x_222_, v_x_223_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0, &l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default(void){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0, &l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedSymbolPriorities_default___closed__0);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx___impl(lean_object* v_x_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_obj_tag_nat(v_x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx___impl___boxed(lean_object* v_x_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorIdx___impl(v_x_235_);
lean_dec(v_x_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(lean_object* v_t_237_, lean_object* v_k_238_){
_start:
{
switch(lean_obj_tag(v_t_237_))
{
case 0:
{
uint8_t v_gen_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_gen_239_ = lean_ctor_get_uint8(v_t_237_, 0);
v___x_240_ = lean_box(v_gen_239_);
v___x_241_ = lean_apply_1(v_k_238_, v___x_240_);
return v___x_241_;
}
case 1:
{
uint8_t v_gen_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_gen_242_ = lean_ctor_get_uint8(v_t_237_, 0);
v___x_243_ = lean_box(v_gen_242_);
v___x_244_ = lean_apply_1(v_k_238_, v___x_243_);
return v___x_244_;
}
case 2:
{
uint8_t v_gen_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_gen_245_ = lean_ctor_get_uint8(v_t_237_, 0);
v___x_246_ = lean_box(v_gen_245_);
v___x_247_ = lean_apply_1(v_k_238_, v___x_246_);
return v___x_247_;
}
case 5:
{
uint8_t v_gen_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_gen_248_ = lean_ctor_get_uint8(v_t_237_, 0);
v___x_249_ = lean_box(v_gen_248_);
v___x_250_ = lean_apply_1(v_k_238_, v___x_249_);
return v___x_250_;
}
case 8:
{
uint8_t v_gen_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_gen_251_ = lean_ctor_get_uint8(v_t_237_, 0);
v___x_252_ = lean_box(v_gen_251_);
v___x_253_ = lean_apply_1(v_k_238_, v___x_252_);
return v___x_253_;
}
default: 
{
return v_k_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg___boxed(lean_object* v_t_254_, lean_object* v_k_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_254_, v_k_255_);
lean_dec(v_t_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim(lean_object* v_motive_257_, lean_object* v_ctorIdx_258_, lean_object* v_t_259_, lean_object* v_h_260_, lean_object* v_k_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_259_, v_k_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___boxed(lean_object* v_motive_263_, lean_object* v_ctorIdx_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_k_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim(v_motive_263_, v_ctorIdx_264_, v_t_265_, v_h_266_, v_k_267_);
lean_dec(v_t_265_);
lean_dec(v_ctorIdx_264_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg(lean_object* v_t_269_, lean_object* v_eqLhs_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_269_, v_eqLhs_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg___boxed(lean_object* v_t_272_, lean_object* v_eqLhs_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___redArg(v_t_272_, v_eqLhs_273_);
lean_dec(v_t_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim(lean_object* v_motive_275_, lean_object* v_t_276_, lean_object* v_h_277_, lean_object* v_eqLhs_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_276_, v_eqLhs_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim___boxed(lean_object* v_motive_280_, lean_object* v_t_281_, lean_object* v_h_282_, lean_object* v_eqLhs_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqLhs_elim(v_motive_280_, v_t_281_, v_h_282_, v_eqLhs_283_);
lean_dec(v_t_281_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg(lean_object* v_t_285_, lean_object* v_eqRhs_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_285_, v_eqRhs_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg___boxed(lean_object* v_t_288_, lean_object* v_eqRhs_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___redArg(v_t_288_, v_eqRhs_289_);
lean_dec(v_t_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim(lean_object* v_motive_291_, lean_object* v_t_292_, lean_object* v_h_293_, lean_object* v_eqRhs_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_292_, v_eqRhs_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim___boxed(lean_object* v_motive_296_, lean_object* v_t_297_, lean_object* v_h_298_, lean_object* v_eqRhs_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqRhs_elim(v_motive_296_, v_t_297_, v_h_298_, v_eqRhs_299_);
lean_dec(v_t_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg(lean_object* v_t_301_, lean_object* v_eqBoth_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_301_, v_eqBoth_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg___boxed(lean_object* v_t_304_, lean_object* v_eqBoth_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___redArg(v_t_304_, v_eqBoth_305_);
lean_dec(v_t_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim(lean_object* v_motive_307_, lean_object* v_t_308_, lean_object* v_h_309_, lean_object* v_eqBoth_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_308_, v_eqBoth_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim___boxed(lean_object* v_motive_312_, lean_object* v_t_313_, lean_object* v_h_314_, lean_object* v_eqBoth_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBoth_elim(v_motive_312_, v_t_313_, v_h_314_, v_eqBoth_315_);
lean_dec(v_t_313_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg(lean_object* v_t_317_, lean_object* v_eqBwd_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_317_, v_eqBwd_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg___boxed(lean_object* v_t_320_, lean_object* v_eqBwd_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___redArg(v_t_320_, v_eqBwd_321_);
lean_dec(v_t_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim(lean_object* v_motive_323_, lean_object* v_t_324_, lean_object* v_h_325_, lean_object* v_eqBwd_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_324_, v_eqBwd_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim___boxed(lean_object* v_motive_328_, lean_object* v_t_329_, lean_object* v_h_330_, lean_object* v_eqBwd_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_Meta_Grind_EMatchTheoremKind_eqBwd_elim(v_motive_328_, v_t_329_, v_h_330_, v_eqBwd_331_);
lean_dec(v_t_329_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg(lean_object* v_t_333_, lean_object* v_fwd_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_333_, v_fwd_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg___boxed(lean_object* v_t_336_, lean_object* v_fwd_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___redArg(v_t_336_, v_fwd_337_);
lean_dec(v_t_336_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim(lean_object* v_motive_339_, lean_object* v_t_340_, lean_object* v_h_341_, lean_object* v_fwd_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_340_, v_fwd_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim___boxed(lean_object* v_motive_344_, lean_object* v_t_345_, lean_object* v_h_346_, lean_object* v_fwd_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Meta_Grind_EMatchTheoremKind_fwd_elim(v_motive_344_, v_t_345_, v_h_346_, v_fwd_347_);
lean_dec(v_t_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg(lean_object* v_t_349_, lean_object* v_bwd_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_349_, v_bwd_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg___boxed(lean_object* v_t_352_, lean_object* v_bwd_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___redArg(v_t_352_, v_bwd_353_);
lean_dec(v_t_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim(lean_object* v_motive_355_, lean_object* v_t_356_, lean_object* v_h_357_, lean_object* v_bwd_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_356_, v_bwd_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim___boxed(lean_object* v_motive_360_, lean_object* v_t_361_, lean_object* v_h_362_, lean_object* v_bwd_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Meta_Grind_EMatchTheoremKind_bwd_elim(v_motive_360_, v_t_361_, v_h_362_, v_bwd_363_);
lean_dec(v_t_361_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg(lean_object* v_t_365_, lean_object* v_leftRight_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_365_, v_leftRight_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg___boxed(lean_object* v_t_368_, lean_object* v_leftRight_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___redArg(v_t_368_, v_leftRight_369_);
lean_dec(v_t_368_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim(lean_object* v_motive_371_, lean_object* v_t_372_, lean_object* v_h_373_, lean_object* v_leftRight_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_372_, v_leftRight_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim___boxed(lean_object* v_motive_376_, lean_object* v_t_377_, lean_object* v_h_378_, lean_object* v_leftRight_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Meta_Grind_EMatchTheoremKind_leftRight_elim(v_motive_376_, v_t_377_, v_h_378_, v_leftRight_379_);
lean_dec(v_t_377_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg(lean_object* v_t_381_, lean_object* v_rightLeft_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_381_, v_rightLeft_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg___boxed(lean_object* v_t_384_, lean_object* v_rightLeft_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___redArg(v_t_384_, v_rightLeft_385_);
lean_dec(v_t_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim(lean_object* v_motive_387_, lean_object* v_t_388_, lean_object* v_h_389_, lean_object* v_rightLeft_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_388_, v_rightLeft_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim___boxed(lean_object* v_motive_392_, lean_object* v_t_393_, lean_object* v_h_394_, lean_object* v_rightLeft_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Meta_Grind_EMatchTheoremKind_rightLeft_elim(v_motive_392_, v_t_393_, v_h_394_, v_rightLeft_395_);
lean_dec(v_t_393_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg(lean_object* v_t_397_, lean_object* v_default_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_397_, v_default_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg___boxed(lean_object* v_t_400_, lean_object* v_default_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___redArg(v_t_400_, v_default_401_);
lean_dec(v_t_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim(lean_object* v_motive_403_, lean_object* v_t_404_, lean_object* v_h_405_, lean_object* v_default_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_404_, v_default_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_default_elim___boxed(lean_object* v_motive_408_, lean_object* v_t_409_, lean_object* v_h_410_, lean_object* v_default_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Meta_Grind_EMatchTheoremKind_default_elim(v_motive_408_, v_t_409_, v_h_410_, v_default_411_);
lean_dec(v_t_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg(lean_object* v_t_413_, lean_object* v_user_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_413_, v_user_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg___boxed(lean_object* v_t_416_, lean_object* v_user_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___redArg(v_t_416_, v_user_417_);
lean_dec(v_t_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim(lean_object* v_motive_419_, lean_object* v_t_420_, lean_object* v_h_421_, lean_object* v_user_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Meta_Grind_EMatchTheoremKind_ctorElim___redArg(v_t_420_, v_user_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_user_elim___boxed(lean_object* v_motive_424_, lean_object* v_t_425_, lean_object* v_h_426_, lean_object* v_user_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Meta_Grind_EMatchTheoremKind_user_elim(v_motive_424_, v_t_425_, v_h_426_, v_user_427_);
lean_dec(v_t_425_);
return v_res_428_;
}
}
uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v_decide_437_; uint8_t v_gen_439_; uint8_t v_gen_x27_440_; 
v___x_435_ = lean_obj_tag_nat(v_x_433_);
v___x_436_ = lean_obj_tag_nat(v_x_434_);
v_decide_437_ = lean_nat_dec_eq(v___x_435_, v___x_436_);
if (v_decide_437_ == 0)
{
return v_decide_437_;
}
else
{
switch(lean_obj_tag(v_x_433_))
{
case 0:
{
uint8_t v_gen_441_; uint8_t v_gen_442_; 
v_gen_441_ = lean_ctor_get_uint8(v_x_433_, 0);
v_gen_442_ = lean_ctor_get_uint8(v_x_434_, 0);
v_gen_439_ = v_gen_441_;
v_gen_x27_440_ = v_gen_442_;
goto v___jp_438_;
}
case 1:
{
uint8_t v_gen_443_; uint8_t v_gen_444_; 
v_gen_443_ = lean_ctor_get_uint8(v_x_433_, 0);
v_gen_444_ = lean_ctor_get_uint8(v_x_434_, 0);
v_gen_439_ = v_gen_443_;
v_gen_x27_440_ = v_gen_444_;
goto v___jp_438_;
}
case 2:
{
uint8_t v_gen_445_; uint8_t v_gen_446_; 
v_gen_445_ = lean_ctor_get_uint8(v_x_433_, 0);
v_gen_446_ = lean_ctor_get_uint8(v_x_434_, 0);
v_gen_439_ = v_gen_445_;
v_gen_x27_440_ = v_gen_446_;
goto v___jp_438_;
}
case 5:
{
uint8_t v_gen_447_; uint8_t v_gen_448_; 
v_gen_447_ = lean_ctor_get_uint8(v_x_433_, 0);
v_gen_448_ = lean_ctor_get_uint8(v_x_434_, 0);
v_gen_439_ = v_gen_447_;
v_gen_x27_440_ = v_gen_448_;
goto v___jp_438_;
}
case 8:
{
uint8_t v_gen_449_; uint8_t v_gen_450_; 
v_gen_449_ = lean_ctor_get_uint8(v_x_433_, 0);
v_gen_450_ = lean_ctor_get_uint8(v_x_434_, 0);
v_gen_439_ = v_gen_449_;
v_gen_x27_440_ = v_gen_450_;
goto v___jp_438_;
}
default: 
{
return v_decide_437_;
}
}
}
v___jp_438_:
{
if (v_gen_x27_440_ == 0)
{
if (v_gen_439_ == 0)
{
return v_decide_437_;
}
else
{
return v_gen_x27_440_;
}
}
else
{
return v_gen_439_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_433_ = stack[0].m_obj;
lean_object* v_x_434_ = stack[1].m_obj;
uint8_t v_res_451_;
v_res_451_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_x_433_, v_x_434_);
stack->m_num = v_res_451_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq___boxed(lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
uint8_t v_res_454_; lean_object* v_r_455_; 
v_res_454_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(v_x_452_, v_x_453_);
lean_dec(v_x_453_);
lean_dec(v_x_452_);
v_r_455_ = lean_box(v_res_454_);
return v_r_455_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(2u);
v___x_480_ = lean_nat_to_int(v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = lean_nat_to_int(v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr(lean_object* v_x_507_, lean_object* v_prec_508_){
_start:
{
lean_object* v___y_510_; lean_object* v___y_517_; lean_object* v___y_524_; lean_object* v___y_531_; lean_object* v___y_538_; 
switch(lean_obj_tag(v_x_507_))
{
case 0:
{
uint8_t v_gen_544_; lean_object* v___y_546_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_gen_544_ = lean_ctor_get_uint8(v_x_507_, 0);
v___x_554_ = lean_unsigned_to_nat(1024u);
v___x_555_ = lean_nat_dec_le(v___x_554_, v_prec_508_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
v___x_556_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_546_ = v___x_556_;
goto v___jp_545_;
}
else
{
lean_object* v___x_557_; 
v___x_557_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_546_ = v___x_557_;
goto v___jp_545_;
}
v___jp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_547_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__12));
v___x_548_ = l_Bool_repr___redArg(v_gen_544_);
v___x_549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
lean_inc(v___y_546_);
v___x_550_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_550_, 0, v___y_546_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = 0;
v___x_552_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*1, v___x_551_);
v___x_553_ = l_Repr_addAppParen(v___x_552_, v_prec_508_);
return v___x_553_;
}
}
case 1:
{
uint8_t v_gen_558_; lean_object* v___y_560_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_gen_558_ = lean_ctor_get_uint8(v_x_507_, 0);
v___x_568_ = lean_unsigned_to_nat(1024u);
v___x_569_ = lean_nat_dec_le(v___x_568_, v_prec_508_);
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
v___x_561_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__17));
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
v___x_567_ = l_Repr_addAppParen(v___x_566_, v_prec_508_);
return v___x_567_;
}
}
case 2:
{
uint8_t v_gen_572_; lean_object* v___y_574_; lean_object* v___x_582_; uint8_t v___x_583_; 
v_gen_572_ = lean_ctor_get_uint8(v_x_507_, 0);
v___x_582_ = lean_unsigned_to_nat(1024u);
v___x_583_ = lean_nat_dec_le(v___x_582_, v_prec_508_);
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
v___x_575_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__20));
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
v___x_581_ = l_Repr_addAppParen(v___x_580_, v_prec_508_);
return v___x_581_;
}
}
case 3:
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(1024u);
v___x_587_ = lean_nat_dec_le(v___x_586_, v_prec_508_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
v___x_588_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_524_ = v___x_588_;
goto v___jp_523_;
}
else
{
lean_object* v___x_589_; 
v___x_589_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_524_ = v___x_589_;
goto v___jp_523_;
}
}
case 4:
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_unsigned_to_nat(1024u);
v___x_591_ = lean_nat_dec_le(v___x_590_, v_prec_508_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_531_ = v___x_592_;
goto v___jp_530_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_531_ = v___x_593_;
goto v___jp_530_;
}
}
case 5:
{
uint8_t v_gen_594_; lean_object* v___y_596_; lean_object* v___x_604_; uint8_t v___x_605_; 
v_gen_594_ = lean_ctor_get_uint8(v_x_507_, 0);
v___x_604_ = lean_unsigned_to_nat(1024u);
v___x_605_ = lean_nat_dec_le(v___x_604_, v_prec_508_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; 
v___x_606_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_596_ = v___x_606_;
goto v___jp_595_;
}
else
{
lean_object* v___x_607_; 
v___x_607_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_596_ = v___x_607_;
goto v___jp_595_;
}
v___jp_595_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_597_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__23));
v___x_598_ = l_Bool_repr___redArg(v_gen_594_);
v___x_599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
lean_inc(v___y_596_);
v___x_600_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_600_, 0, v___y_596_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = 0;
v___x_602_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set_uint8(v___x_602_, sizeof(void*)*1, v___x_601_);
v___x_603_ = l_Repr_addAppParen(v___x_602_, v_prec_508_);
return v___x_603_;
}
}
case 6:
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_unsigned_to_nat(1024u);
v___x_609_ = lean_nat_dec_le(v___x_608_, v_prec_508_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; 
v___x_610_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_517_ = v___x_610_;
goto v___jp_516_;
}
else
{
lean_object* v___x_611_; 
v___x_611_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_517_ = v___x_611_;
goto v___jp_516_;
}
}
case 7:
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_unsigned_to_nat(1024u);
v___x_613_ = lean_nat_dec_le(v___x_612_, v_prec_508_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
v___x_614_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_510_ = v___x_614_;
goto v___jp_509_;
}
else
{
lean_object* v___x_615_; 
v___x_615_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_510_ = v___x_615_;
goto v___jp_509_;
}
}
case 8:
{
uint8_t v_gen_616_; lean_object* v___y_618_; lean_object* v___x_626_; uint8_t v___x_627_; 
v_gen_616_ = lean_ctor_get_uint8(v_x_507_, 0);
v___x_626_ = lean_unsigned_to_nat(1024u);
v___x_627_ = lean_nat_dec_le(v___x_626_, v_prec_508_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
v___x_628_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_618_ = v___x_628_;
goto v___jp_617_;
}
else
{
lean_object* v___x_629_; 
v___x_629_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_618_ = v___x_629_;
goto v___jp_617_;
}
v___jp_617_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_619_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__26));
v___x_620_ = l_Bool_repr___redArg(v_gen_616_);
v___x_621_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
lean_inc(v___y_618_);
v___x_622_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_622_, 0, v___y_618_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = 0;
v___x_624_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set_uint8(v___x_624_, sizeof(void*)*1, v___x_623_);
v___x_625_ = l_Repr_addAppParen(v___x_624_, v_prec_508_);
return v___x_625_;
}
}
default: 
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = lean_unsigned_to_nat(1024u);
v___x_631_ = lean_nat_dec_le(v___x_630_, v_prec_508_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; 
v___x_632_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_538_ = v___x_632_;
goto v___jp_537_;
}
else
{
lean_object* v___x_633_; 
v___x_633_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_538_ = v___x_633_;
goto v___jp_537_;
}
}
}
v___jp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_511_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__1));
lean_inc(v___y_510_);
v___x_512_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_512_, 0, v___y_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = 0;
v___x_514_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*1, v___x_513_);
v___x_515_ = l_Repr_addAppParen(v___x_514_, v_prec_508_);
return v___x_515_;
}
v___jp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_518_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__3));
lean_inc(v___y_517_);
v___x_519_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_519_, 0, v___y_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = 0;
v___x_521_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*1, v___x_520_);
v___x_522_ = l_Repr_addAppParen(v___x_521_, v_prec_508_);
return v___x_522_;
}
v___jp_523_:
{
lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_525_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__5));
lean_inc(v___y_524_);
v___x_526_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_526_, 0, v___y_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = 0;
v___x_528_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*1, v___x_527_);
v___x_529_ = l_Repr_addAppParen(v___x_528_, v_prec_508_);
return v___x_529_;
}
v___jp_530_:
{
lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_532_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__7));
lean_inc(v___y_531_);
v___x_533_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_533_, 0, v___y_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = 0;
v___x_535_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*1, v___x_534_);
v___x_536_ = l_Repr_addAppParen(v___x_535_, v_prec_508_);
return v___x_536_;
}
v___jp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_539_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__9));
lean_inc(v___y_538_);
v___x_540_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_540_, 0, v___y_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = 0;
v___x_542_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*1, v___x_541_);
v___x_543_ = l_Repr_addAppParen(v___x_542_, v_prec_508_);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___boxed(lean_object* v_x_634_, lean_object* v_prec_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr(v_x_634_, v_prec_635_);
lean_dec(v_prec_635_);
lean_dec(v_x_634_);
return v_res_636_;
}
}
uint64_t l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(lean_object* v_x_639_){
_start:
{
switch(lean_obj_tag(v_x_639_))
{
case 0:
{
uint8_t v_gen_640_; 
v_gen_640_ = lean_ctor_get_uint8(v_x_639_, 0);
if (v_gen_640_ == 0)
{
uint64_t v___x_641_; 
v___x_641_ = 2501231519204769793ULL;
return v___x_641_;
}
else
{
uint64_t v___x_642_; 
v___x_642_ = 10067447881416919396ULL;
return v___x_642_;
}
}
case 1:
{
uint8_t v_gen_643_; 
v_gen_643_ = lean_ctor_get_uint8(v_x_639_, 0);
if (v_gen_643_ == 0)
{
uint64_t v___x_644_; 
v___x_644_ = 6634225825881527916ULL;
return v___x_644_;
}
else
{
uint64_t v___x_645_; 
v___x_645_ = 5934453574740161273ULL;
return v___x_645_;
}
}
case 2:
{
uint8_t v_gen_646_; 
v_gen_646_ = lean_ctor_get_uint8(v_x_639_, 0);
if (v_gen_646_ == 0)
{
uint64_t v___x_647_; 
v___x_647_ = 12681986979560805163ULL;
return v___x_647_;
}
else
{
uint64_t v___x_648_; 
v___x_648_ = 1801459268063403150ULL;
return v___x_648_;
}
}
case 3:
{
uint64_t v___x_649_; 
v___x_649_ = 3ULL;
return v___x_649_;
}
case 4:
{
uint64_t v___x_650_; 
v___x_650_ = 4ULL;
return v___x_650_;
}
case 5:
{
uint8_t v_gen_651_; 
v_gen_651_ = lean_ctor_get_uint8(v_x_639_, 0);
if (v_gen_651_ == 0)
{
uint64_t v___x_652_; 
v___x_652_ = 4719458978879008792ULL;
return v___x_652_;
}
else
{
uint64_t v___x_653_; 
v___x_653_ = 4019686727737642149ULL;
return v___x_653_;
}
}
case 6:
{
uint64_t v___x_654_; 
v___x_654_ = 6ULL;
return v___x_654_;
}
case 7:
{
uint64_t v___x_655_; 
v___x_655_ = 7ULL;
return v___x_655_;
}
case 8:
{
uint8_t v_gen_656_; 
v_gen_656_ = lean_ctor_get_uint8(v_x_639_, 0);
if (v_gen_656_ == 0)
{
uint64_t v___x_657_; 
v___x_657_ = 17118441898909283161ULL;
return v___x_657_;
}
else
{
uint64_t v___x_658_; 
v___x_658_ = 13896981575421957644ULL;
return v___x_658_;
}
}
default: 
{
uint64_t v___x_659_; 
v___x_659_ = 9ULL;
return v___x_659_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_639_ = stack[0].m_obj;
uint64_t v_res_660_;
v_res_660_ = l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(v_x_639_);
stack->m_num = v_res_660_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash___boxed(lean_object* v_x_661_){
_start:
{
uint64_t v_res_662_; lean_object* v_r_663_; 
v_res_662_ = l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(v_x_661_);
lean_dec(v_x_661_);
v_r_663_ = lean_box_uint64(v_res_662_);
return v_r_663_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = lean_box(0);
v___x_672_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__2));
v___x_673_ = l_Lean_Expr_const___override(v___x_672_, v___x_671_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_674_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v___x_675_);
lean_ctor_set(v___x_677_, 2, v___x_674_);
return v___x_677_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default(void){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__4);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS(void){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default;
return v___x_679_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(lean_object* v_xs_680_, lean_object* v_ys_681_, lean_object* v_x_682_){
_start:
{
lean_object* v_zero_683_; uint8_t v_isZero_684_; 
v_zero_683_ = lean_unsigned_to_nat(0u);
v_isZero_684_ = lean_nat_dec_eq(v_x_682_, v_zero_683_);
if (v_isZero_684_ == 1)
{
lean_dec(v_x_682_);
return v_isZero_684_;
}
else
{
lean_object* v_one_685_; lean_object* v_n_686_; lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v_one_685_ = lean_unsigned_to_nat(1u);
v_n_686_ = lean_nat_sub(v_x_682_, v_one_685_);
lean_dec(v_x_682_);
v___x_687_ = lean_array_fget_borrowed(v_xs_680_, v_n_686_);
v___x_688_ = lean_array_fget_borrowed(v_ys_681_, v_n_686_);
v___x_689_ = lean_name_eq(v___x_687_, v___x_688_);
if (v___x_689_ == 0)
{
lean_dec(v_n_686_);
return v___x_689_;
}
else
{
v_x_682_ = v_n_686_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_680_ = stack[0].m_obj;
lean_object* v_ys_681_ = stack[1].m_obj;
lean_object* v_x_682_ = stack[2].m_obj;
uint8_t v_res_691_;
v_res_691_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_xs_680_, v_ys_681_, v_x_682_);
stack->m_num = v_res_691_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg___boxed(lean_object* v_xs_692_, lean_object* v_ys_693_, lean_object* v_x_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_xs_692_, v_ys_693_, v_x_694_);
lean_dec_ref(v_ys_693_);
lean_dec_ref(v_xs_692_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
uint8_t l_Lean_Meta_Grind_instBEqCnstrRHS_beq(lean_object* v_x_697_, lean_object* v_x_698_){
_start:
{
lean_object* v_levelNames_699_; lean_object* v_numMVars_700_; lean_object* v_expr_701_; lean_object* v_levelNames_702_; lean_object* v_numMVars_703_; lean_object* v_expr_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v_levelNames_699_ = lean_ctor_get(v_x_697_, 0);
v_numMVars_700_ = lean_ctor_get(v_x_697_, 1);
v_expr_701_ = lean_ctor_get(v_x_697_, 2);
v_levelNames_702_ = lean_ctor_get(v_x_698_, 0);
v_numMVars_703_ = lean_ctor_get(v_x_698_, 1);
v_expr_704_ = lean_ctor_get(v_x_698_, 2);
v___x_705_ = lean_array_get_size(v_levelNames_699_);
v___x_706_ = lean_array_get_size(v_levelNames_702_);
v___x_707_ = lean_nat_dec_eq(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
return v___x_707_;
}
else
{
uint8_t v___x_708_; 
v___x_708_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_levelNames_699_, v_levelNames_702_, v___x_705_);
if (v___x_708_ == 0)
{
return v___x_708_;
}
else
{
uint8_t v___x_709_; 
v___x_709_ = lean_nat_dec_eq(v_numMVars_700_, v_numMVars_703_);
if (v___x_709_ == 0)
{
return v___x_709_;
}
else
{
uint8_t v___x_710_; 
v___x_710_ = lean_expr_eqv(v_expr_701_, v_expr_704_);
return v___x_710_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_instBEqCnstrRHS_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_697_ = stack[0].m_obj;
lean_object* v_x_698_ = stack[1].m_obj;
uint8_t v_res_711_;
v_res_711_ = l_Lean_Meta_Grind_instBEqCnstrRHS_beq(v_x_697_, v_x_698_);
stack->m_num = v_res_711_;
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
uint8_t l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(lean_object* v_xs_716_, lean_object* v_ys_717_, lean_object* v_hsz_718_, lean_object* v_x_719_, lean_object* v_x_720_){
_start:
{
uint8_t v___x_721_; 
v___x_721_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___redArg(v_xs_716_, v_ys_717_, v_x_719_);
return v___x_721_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_716_ = stack[0].m_obj;
lean_object* v_ys_717_ = stack[1].m_obj;
lean_object* v_x_719_ = stack[3].m_obj;
uint8_t v_res_722_;
v_res_722_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(v_xs_716_, v_ys_717_, lean_box(0), v_x_719_, lean_box(0));
stack->m_num = v_res_722_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0___boxed(lean_object* v_xs_723_, lean_object* v_ys_724_, lean_object* v_hsz_725_, lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
uint8_t v_res_728_; lean_object* v_r_729_; 
v_res_728_ = l_Array_isEqvAux___at___00Lean_Meta_Grind_instBEqCnstrRHS_beq_spec__0(v_xs_723_, v_ys_724_, v_hsz_725_, v_x_726_, v_x_727_);
lean_dec_ref(v_ys_724_);
lean_dec_ref(v_xs_723_);
v_r_729_ = lean_box(v_res_728_);
return v_r_729_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__1(lean_object* v_a_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = lean_nat_to_int(v_a_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_734_, lean_object* v_x_735_, lean_object* v_x_736_){
_start:
{
if (lean_obj_tag(v_x_736_) == 0)
{
lean_dec(v_x_734_);
return v_x_735_;
}
else
{
lean_object* v_head_737_; lean_object* v_tail_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_749_; 
v_head_737_ = lean_ctor_get(v_x_736_, 0);
v_tail_738_ = lean_ctor_get(v_x_736_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v_x_736_);
if (v_isSharedCheck_749_ == 0)
{
v___x_740_ = v_x_736_;
v_isShared_741_ = v_isSharedCheck_749_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_tail_738_);
lean_inc(v_head_737_);
lean_dec(v_x_736_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_749_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
lean_inc(v_x_734_);
if (v_isShared_741_ == 0)
{
lean_ctor_set_tag(v___x_740_, 5);
lean_ctor_set(v___x_740_, 1, v_x_734_);
lean_ctor_set(v___x_740_, 0, v_x_735_);
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_x_735_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_x_734_);
v___x_743_ = v_reuseFailAlloc_748_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = l_Lean_Name_reprPrec(v_head_737_, v___x_744_);
v___x_746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_743_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v_x_735_ = v___x_746_;
v_x_736_ = v_tail_738_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2(lean_object* v_x_750_, lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
if (lean_obj_tag(v_x_752_) == 0)
{
lean_dec(v_x_750_);
return v_x_751_;
}
else
{
lean_object* v_head_753_; lean_object* v_tail_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_765_; 
v_head_753_ = lean_ctor_get(v_x_752_, 0);
v_tail_754_ = lean_ctor_get(v_x_752_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_x_752_);
if (v_isSharedCheck_765_ == 0)
{
v___x_756_ = v_x_752_;
v_isShared_757_ = v_isSharedCheck_765_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_tail_754_);
lean_inc(v_head_753_);
lean_dec(v_x_752_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_765_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
lean_inc(v_x_750_);
if (v_isShared_757_ == 0)
{
lean_ctor_set_tag(v___x_756_, 5);
lean_ctor_set(v___x_756_, 1, v_x_750_);
lean_ctor_set(v___x_756_, 0, v_x_751_);
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_x_751_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_x_750_);
v___x_759_ = v_reuseFailAlloc_764_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = l_Lean_Name_reprPrec(v_head_753_, v___x_760_);
v___x_762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_759_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2_spec__3(v_x_750_, v___x_762_, v_tail_754_);
return v___x_763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(lean_object* v___y_766_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = l_Lean_Name_reprPrec(v___y_766_, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0(lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
if (lean_obj_tag(v_x_769_) == 0)
{
lean_object* v___x_771_; 
lean_dec(v_x_770_);
v___x_771_ = lean_box(0);
return v___x_771_;
}
else
{
lean_object* v_tail_772_; 
v_tail_772_ = lean_ctor_get(v_x_769_, 1);
if (lean_obj_tag(v_tail_772_) == 0)
{
lean_object* v_head_773_; lean_object* v___x_774_; 
lean_dec(v_x_770_);
v_head_773_ = lean_ctor_get(v_x_769_, 0);
lean_inc(v_head_773_);
lean_dec_ref_known(v_x_769_, 2);
v___x_774_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(v_head_773_);
return v___x_774_;
}
else
{
lean_object* v_head_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
lean_inc(v_tail_772_);
v_head_775_ = lean_ctor_get(v_x_769_, 0);
lean_inc(v_head_775_);
lean_dec_ref_known(v_x_769_, 2);
v___x_776_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0___lam__0(v_head_775_);
v___x_777_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0_spec__2(v_x_770_, v___x_776_, v_tail_772_);
return v___x_777_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__0));
v___x_787_ = lean_string_length(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5, &l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__5);
v___x_789_ = lean_nat_to_int(v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0(lean_object* v_xs_797_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_798_ = lean_array_get_size(v_xs_797_);
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_nat_dec_eq(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_801_ = lean_array_to_list(v_xs_797_);
v___x_802_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__3));
v___x_803_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0_spec__0(v___x_801_, v___x_802_);
v___x_804_ = lean_obj_once(&l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6, &l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__6);
v___x_805_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__7));
v___x_806_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
lean_ctor_set(v___x_806_, 1, v___x_803_);
v___x_807_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__8));
v___x_808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_804_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = l_Std_Format_fill(v___x_809_);
return v___x_810_;
}
else
{
lean_object* v___x_811_; 
lean_dec_ref(v_xs_797_);
v___x_811_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__10));
return v___x_811_;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_unsigned_to_nat(14u);
v___x_826_ = lean_nat_to_int(v___x_825_);
return v___x_826_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_unsigned_to_nat(12u);
v___x_831_ = lean_nat_to_int(v___x_830_);
return v___x_831_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_unsigned_to_nat(8u);
v___x_836_ = lean_nat_to_int(v___x_835_);
return v___x_836_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__0));
v___x_839_ = lean_string_length(v___x_838_);
return v___x_839_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__15);
v___x_841_ = lean_nat_to_int(v___x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(lean_object* v_x_846_){
_start:
{
lean_object* v_levelNames_847_; lean_object* v_numMVars_848_; lean_object* v_expr_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_levelNames_847_ = lean_ctor_get(v_x_846_, 0);
lean_inc_ref(v_levelNames_847_);
v_numMVars_848_ = lean_ctor_get(v_x_846_, 1);
lean_inc(v_numMVars_848_);
v_expr_849_ = lean_ctor_get(v_x_846_, 2);
lean_inc_ref(v_expr_849_);
lean_dec_ref(v_x_846_);
v___x_850_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__5));
v___x_851_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__6));
v___x_852_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__7);
v___x_853_ = l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0(v_levelNames_847_);
v___x_854_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_852_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = 0;
v___x_856_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*1, v___x_855_);
v___x_857_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_851_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = ((lean_object*)(l_Array_repr___at___00Lean_Meta_Grind_instReprCnstrRHS_repr_spec__0___closed__2));
v___x_859_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_857_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = lean_box(1);
v___x_861_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__9));
v___x_863_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___x_850_);
v___x_865_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__10);
v___x_866_ = l_Nat_reprFast(v_numMVars_848_);
v___x_867_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
v___x_868_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_865_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set_uint8(v___x_869_, sizeof(void*)*1, v___x_855_);
v___x_870_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_864_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_858_);
v___x_872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v___x_860_);
v___x_873_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__12));
v___x_874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v___x_850_);
v___x_876_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__13);
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = l_Lean_instReprExpr_repr(v_expr_849_, v___x_877_);
v___x_879_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_876_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set_uint8(v___x_880_, sizeof(void*)*1, v___x_855_);
v___x_881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_875_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = lean_obj_once(&l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16, &l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16_once, _init_l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__16);
v___x_883_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__17));
v___x_884_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v___x_881_);
v___x_885_ = ((lean_object*)(l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg___closed__18));
v___x_886_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_882_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set_uint8(v___x_888_, sizeof(void*)*1, v___x_855_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr(lean_object* v_x_889_, lean_object* v_prec_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_x_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprCnstrRHS_repr___boxed(lean_object* v_x_892_, lean_object* v_prec_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr(v_x_892_, v_prec_893_);
lean_dec(v_prec_893_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx___impl(lean_object* v_x_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = lean_obj_tag_nat(v_x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx___impl___boxed(lean_object* v_x_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorIdx___impl(v_x_899_);
lean_dec_ref(v_x_899_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(lean_object* v_t_901_, lean_object* v_k_902_){
_start:
{
switch(lean_obj_tag(v_t_901_))
{
case 0:
{
lean_object* v_lhs_903_; lean_object* v_rhs_904_; lean_object* v___x_905_; 
v_lhs_903_ = lean_ctor_get(v_t_901_, 0);
lean_inc(v_lhs_903_);
v_rhs_904_ = lean_ctor_get(v_t_901_, 1);
lean_inc_ref(v_rhs_904_);
lean_dec_ref_known(v_t_901_, 2);
v___x_905_ = lean_apply_2(v_k_902_, v_lhs_903_, v_rhs_904_);
return v___x_905_;
}
case 1:
{
lean_object* v_lhs_906_; lean_object* v_rhs_907_; lean_object* v___x_908_; 
v_lhs_906_ = lean_ctor_get(v_t_901_, 0);
lean_inc(v_lhs_906_);
v_rhs_907_ = lean_ctor_get(v_t_901_, 1);
lean_inc_ref(v_rhs_907_);
lean_dec_ref_known(v_t_901_, 2);
v___x_908_ = lean_apply_2(v_k_902_, v_lhs_906_, v_rhs_907_);
return v___x_908_;
}
case 2:
{
lean_object* v_lhs_909_; lean_object* v_n_910_; lean_object* v___x_911_; 
v_lhs_909_ = lean_ctor_get(v_t_901_, 0);
lean_inc(v_lhs_909_);
v_n_910_ = lean_ctor_get(v_t_901_, 1);
lean_inc(v_n_910_);
lean_dec_ref_known(v_t_901_, 2);
v___x_911_ = lean_apply_2(v_k_902_, v_lhs_909_, v_n_910_);
return v___x_911_;
}
case 3:
{
lean_object* v_lhs_912_; lean_object* v_n_913_; lean_object* v___x_914_; 
v_lhs_912_ = lean_ctor_get(v_t_901_, 0);
lean_inc(v_lhs_912_);
v_n_913_ = lean_ctor_get(v_t_901_, 1);
lean_inc(v_n_913_);
lean_dec_ref_known(v_t_901_, 2);
v___x_914_ = lean_apply_2(v_k_902_, v_lhs_912_, v_n_913_);
return v___x_914_;
}
case 6:
{
lean_object* v_bvarIdx_915_; uint8_t v_strict_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_bvarIdx_915_ = lean_ctor_get(v_t_901_, 0);
lean_inc(v_bvarIdx_915_);
v_strict_916_ = lean_ctor_get_uint8(v_t_901_, sizeof(void*)*1);
lean_dec_ref_known(v_t_901_, 1);
v___x_917_ = lean_box(v_strict_916_);
v___x_918_ = lean_apply_2(v_k_902_, v_bvarIdx_915_, v___x_917_);
return v___x_918_;
}
case 8:
{
lean_object* v_e_919_; lean_object* v___x_920_; 
v_e_919_ = lean_ctor_get(v_t_901_, 0);
lean_inc_ref(v_e_919_);
lean_dec_ref_known(v_t_901_, 1);
v___x_920_ = lean_apply_1(v_k_902_, v_e_919_);
return v___x_920_;
}
case 9:
{
lean_object* v_e_921_; lean_object* v___x_922_; 
v_e_921_ = lean_ctor_get(v_t_901_, 0);
lean_inc_ref(v_e_921_);
lean_dec_ref_known(v_t_901_, 1);
v___x_922_ = lean_apply_1(v_k_902_, v_e_921_);
return v___x_922_;
}
case 10:
{
lean_object* v_bvarIdx_923_; uint8_t v_strict_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_bvarIdx_923_ = lean_ctor_get(v_t_901_, 0);
lean_inc(v_bvarIdx_923_);
v_strict_924_ = lean_ctor_get_uint8(v_t_901_, sizeof(void*)*1);
lean_dec_ref_known(v_t_901_, 1);
v___x_925_ = lean_box(v_strict_924_);
v___x_926_ = lean_apply_2(v_k_902_, v_bvarIdx_923_, v___x_925_);
return v___x_926_;
}
default: 
{
lean_object* v_n_927_; lean_object* v___x_928_; 
v_n_927_ = lean_ctor_get(v_t_901_, 0);
lean_inc(v_n_927_);
lean_dec_ref(v_t_901_);
v___x_928_ = lean_apply_1(v_k_902_, v_n_927_);
return v___x_928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim(lean_object* v_motive_929_, lean_object* v_ctorIdx_930_, lean_object* v_t_931_, lean_object* v_h_932_, lean_object* v_k_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_931_, v_k_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___boxed(lean_object* v_motive_935_, lean_object* v_ctorIdx_936_, lean_object* v_t_937_, lean_object* v_h_938_, lean_object* v_k_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim(v_motive_935_, v_ctorIdx_936_, v_t_937_, v_h_938_, v_k_939_);
lean_dec(v_ctorIdx_936_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim___redArg(lean_object* v_t_941_, lean_object* v_notDefEq_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_941_, v_notDefEq_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notDefEq_elim(lean_object* v_motive_944_, lean_object* v_t_945_, lean_object* v_h_946_, lean_object* v_notDefEq_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_945_, v_notDefEq_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim___redArg(lean_object* v_t_949_, lean_object* v_defEq_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_949_, v_defEq_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_defEq_elim(lean_object* v_motive_952_, lean_object* v_t_953_, lean_object* v_h_954_, lean_object* v_defEq_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_953_, v_defEq_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim___redArg(lean_object* v_t_957_, lean_object* v_sizeLt_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_957_, v_sizeLt_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_sizeLt_elim(lean_object* v_motive_960_, lean_object* v_t_961_, lean_object* v_h_962_, lean_object* v_sizeLt_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_961_, v_sizeLt_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim___redArg(lean_object* v_t_965_, lean_object* v_depthLt_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_965_, v_depthLt_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_depthLt_elim(lean_object* v_motive_968_, lean_object* v_t_969_, lean_object* v_h_970_, lean_object* v_depthLt_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_969_, v_depthLt_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim___redArg(lean_object* v_t_973_, lean_object* v_genLt_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_973_, v_genLt_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_genLt_elim(lean_object* v_motive_976_, lean_object* v_t_977_, lean_object* v_h_978_, lean_object* v_genLt_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_977_, v_genLt_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim___redArg(lean_object* v_t_981_, lean_object* v_isGround_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_981_, v_isGround_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isGround_elim(lean_object* v_motive_984_, lean_object* v_t_985_, lean_object* v_h_986_, lean_object* v_isGround_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_985_, v_isGround_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim___redArg(lean_object* v_t_989_, lean_object* v_isValue_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_989_, v_isValue_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_isValue_elim(lean_object* v_motive_992_, lean_object* v_t_993_, lean_object* v_h_994_, lean_object* v_isValue_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_993_, v_isValue_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim___redArg(lean_object* v_t_997_, lean_object* v_maxInsts_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_997_, v_maxInsts_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_maxInsts_elim(lean_object* v_motive_1000_, lean_object* v_t_1001_, lean_object* v_h_1002_, lean_object* v_maxInsts_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1001_, v_maxInsts_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim___redArg(lean_object* v_t_1005_, lean_object* v_guard_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1005_, v_guard_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_guard_elim(lean_object* v_motive_1008_, lean_object* v_t_1009_, lean_object* v_h_1010_, lean_object* v_guard_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1009_, v_guard_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim___redArg(lean_object* v_t_1013_, lean_object* v_check_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1013_, v_check_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_check_elim(lean_object* v_motive_1016_, lean_object* v_t_1017_, lean_object* v_h_1018_, lean_object* v_check_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1017_, v_check_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim___redArg(lean_object* v_t_1021_, lean_object* v_notValue_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1021_, v_notValue_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremConstraint_notValue_elim(lean_object* v_motive_1024_, lean_object* v_t_1025_, lean_object* v_h_1026_, lean_object* v_notValue_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_Meta_Grind_EMatchTheoremConstraint_ctorElim___redArg(v_t_1025_, v_notValue_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = l_Lean_Meta_Grind_instInhabitedCnstrRHS_default;
v___x_1030_ = lean_unsigned_to_nat(0u);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v___x_1029_);
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default(void){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0, &l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default___closed__0);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint(void){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_Meta_Grind_instInhabitedEMatchTheoremConstraint_default;
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr(lean_object* v_x_1100_, lean_object* v_prec_1101_){
_start:
{
switch(lean_obj_tag(v_x_1100_))
{
case 0:
{
lean_object* v_lhs_1102_; lean_object* v_rhs_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1127_; 
v_lhs_1102_ = lean_ctor_get(v_x_1100_, 0);
v_rhs_1103_ = lean_ctor_get(v_x_1100_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_x_1100_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1105_ = v_x_1100_;
v_isShared_1106_ = v_isSharedCheck_1127_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_rhs_1103_);
lean_inc(v_lhs_1102_);
lean_dec(v_x_1100_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1127_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___y_1108_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = lean_unsigned_to_nat(1024u);
v___x_1124_ = lean_nat_dec_le(v___x_1123_, v_prec_1101_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1108_ = v___x_1125_;
goto v___jp_1107_;
}
else
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1108_ = v___x_1126_;
goto v___jp_1107_;
}
v___jp_1107_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1109_ = lean_box(1);
v___x_1110_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__2));
v___x_1111_ = l_Nat_reprFast(v_lhs_1102_);
v___x_1112_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set_tag(v___x_1105_, 5);
lean_ctor_set(v___x_1105_, 1, v___x_1112_);
lean_ctor_set(v___x_1105_, 0, v___x_1110_);
v___x_1114_ = v___x_1105_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
lean_ctor_set(v___x_1115_, 1, v___x_1109_);
v___x_1116_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_rhs_1103_);
v___x_1117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1115_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
lean_inc(v___y_1108_);
v___x_1118_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___y_1108_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = 0;
v___x_1120_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*1, v___x_1119_);
v___x_1121_ = l_Repr_addAppParen(v___x_1120_, v_prec_1101_);
return v___x_1121_;
}
}
}
}
case 1:
{
lean_object* v_lhs_1128_; lean_object* v_rhs_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1153_; 
v_lhs_1128_ = lean_ctor_get(v_x_1100_, 0);
v_rhs_1129_ = lean_ctor_get(v_x_1100_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_x_1100_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1131_ = v_x_1100_;
v_isShared_1132_ = v_isSharedCheck_1153_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_rhs_1129_);
lean_inc(v_lhs_1128_);
lean_dec(v_x_1100_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1153_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___y_1134_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = lean_unsigned_to_nat(1024u);
v___x_1150_ = lean_nat_dec_le(v___x_1149_, v_prec_1101_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1134_ = v___x_1151_;
goto v___jp_1133_;
}
else
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1134_ = v___x_1152_;
goto v___jp_1133_;
}
v___jp_1133_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1135_ = lean_box(1);
v___x_1136_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__5));
v___x_1137_ = l_Nat_reprFast(v_lhs_1128_);
v___x_1138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set_tag(v___x_1131_, 5);
lean_ctor_set(v___x_1131_, 1, v___x_1138_);
lean_ctor_set(v___x_1131_, 0, v___x_1136_);
v___x_1140_ = v___x_1131_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1141_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v___x_1135_);
v___x_1142_ = l_Lean_Meta_Grind_instReprCnstrRHS_repr___redArg(v_rhs_1129_);
v___x_1143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
lean_inc(v___y_1134_);
v___x_1144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___y_1134_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = 0;
v___x_1146_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set_uint8(v___x_1146_, sizeof(void*)*1, v___x_1145_);
v___x_1147_ = l_Repr_addAppParen(v___x_1146_, v_prec_1101_);
return v___x_1147_;
}
}
}
}
case 2:
{
lean_object* v_lhs_1154_; lean_object* v_n_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1180_; 
v_lhs_1154_ = lean_ctor_get(v_x_1100_, 0);
v_n_1155_ = lean_ctor_get(v_x_1100_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_x_1100_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1157_ = v_x_1100_;
v_isShared_1158_ = v_isSharedCheck_1180_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_n_1155_);
lean_inc(v_lhs_1154_);
lean_dec(v_x_1100_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1180_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___y_1160_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = lean_unsigned_to_nat(1024u);
v___x_1177_ = lean_nat_dec_le(v___x_1176_, v_prec_1101_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1160_ = v___x_1178_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1160_ = v___x_1179_;
goto v___jp_1159_;
}
v___jp_1159_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1161_ = lean_box(1);
v___x_1162_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__8));
v___x_1163_ = l_Nat_reprFast(v_lhs_1154_);
v___x_1164_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set_tag(v___x_1157_, 5);
lean_ctor_set(v___x_1157_, 1, v___x_1164_);
lean_ctor_set(v___x_1157_, 0, v___x_1162_);
v___x_1166_ = v___x_1157_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1167_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
lean_ctor_set(v___x_1167_, 1, v___x_1161_);
v___x_1168_ = l_Nat_reprFast(v_n_1155_);
v___x_1169_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
v___x_1170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1167_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
lean_inc(v___y_1160_);
v___x_1171_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___y_1160_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = 0;
v___x_1173_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*1, v___x_1172_);
v___x_1174_ = l_Repr_addAppParen(v___x_1173_, v_prec_1101_);
return v___x_1174_;
}
}
}
}
case 3:
{
lean_object* v_lhs_1181_; lean_object* v_n_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1207_; 
v_lhs_1181_ = lean_ctor_get(v_x_1100_, 0);
v_n_1182_ = lean_ctor_get(v_x_1100_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_x_1100_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1184_ = v_x_1100_;
v_isShared_1185_ = v_isSharedCheck_1207_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_n_1182_);
lean_inc(v_lhs_1181_);
lean_dec(v_x_1100_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1207_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___y_1187_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = lean_unsigned_to_nat(1024u);
v___x_1204_ = lean_nat_dec_le(v___x_1203_, v_prec_1101_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1187_ = v___x_1205_;
goto v___jp_1186_;
}
else
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1187_ = v___x_1206_;
goto v___jp_1186_;
}
v___jp_1186_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1188_ = lean_box(1);
v___x_1189_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__11));
v___x_1190_ = l_Nat_reprFast(v_lhs_1181_);
v___x_1191_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set_tag(v___x_1184_, 5);
lean_ctor_set(v___x_1184_, 1, v___x_1191_);
lean_ctor_set(v___x_1184_, 0, v___x_1189_);
v___x_1193_ = v___x_1184_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set(v___x_1194_, 1, v___x_1188_);
v___x_1195_ = l_Nat_reprFast(v_n_1182_);
v___x_1196_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
v___x_1197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1194_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
lean_inc(v___y_1187_);
v___x_1198_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___y_1187_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = 0;
v___x_1200_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set_uint8(v___x_1200_, sizeof(void*)*1, v___x_1199_);
v___x_1201_ = l_Repr_addAppParen(v___x_1200_, v_prec_1101_);
return v___x_1201_;
}
}
}
}
case 4:
{
lean_object* v_n_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1228_; 
v_n_1208_ = lean_ctor_get(v_x_1100_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_x_1100_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1210_ = v_x_1100_;
v_isShared_1211_ = v_isSharedCheck_1228_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_n_1208_);
lean_dec(v_x_1100_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1228_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___y_1213_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = lean_unsigned_to_nat(1024u);
v___x_1225_ = lean_nat_dec_le(v___x_1224_, v_prec_1101_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1213_ = v___x_1226_;
goto v___jp_1212_;
}
else
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1213_ = v___x_1227_;
goto v___jp_1212_;
}
v___jp_1212_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1214_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__14));
v___x_1215_ = l_Nat_reprFast(v_n_1208_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set_tag(v___x_1210_, 3);
lean_ctor_set(v___x_1210_, 0, v___x_1215_);
v___x_1217_ = v___x_1210_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1214_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
lean_inc(v___y_1213_);
v___x_1219_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___y_1213_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = 0;
v___x_1221_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set_uint8(v___x_1221_, sizeof(void*)*1, v___x_1220_);
v___x_1222_ = l_Repr_addAppParen(v___x_1221_, v_prec_1101_);
return v___x_1222_;
}
}
}
}
case 5:
{
lean_object* v_bvarIdx_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1249_; 
v_bvarIdx_1229_ = lean_ctor_get(v_x_1100_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_x_1100_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1231_ = v_x_1100_;
v_isShared_1232_ = v_isSharedCheck_1249_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_bvarIdx_1229_);
lean_dec(v_x_1100_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1249_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___y_1234_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = lean_unsigned_to_nat(1024u);
v___x_1246_ = lean_nat_dec_le(v___x_1245_, v_prec_1101_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; 
v___x_1247_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1234_ = v___x_1247_;
goto v___jp_1233_;
}
else
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1234_ = v___x_1248_;
goto v___jp_1233_;
}
v___jp_1233_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1235_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__17));
v___x_1236_ = l_Nat_reprFast(v_bvarIdx_1229_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set_tag(v___x_1231_, 3);
lean_ctor_set(v___x_1231_, 0, v___x_1236_);
v___x_1238_ = v___x_1231_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1235_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
lean_inc(v___y_1234_);
v___x_1240_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___y_1234_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = 0;
v___x_1242_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1242_, 0, v___x_1240_);
lean_ctor_set_uint8(v___x_1242_, sizeof(void*)*1, v___x_1241_);
v___x_1243_ = l_Repr_addAppParen(v___x_1242_, v_prec_1101_);
return v___x_1243_;
}
}
}
}
case 6:
{
lean_object* v_bvarIdx_1250_; uint8_t v_strict_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1275_; 
v_bvarIdx_1250_ = lean_ctor_get(v_x_1100_, 0);
v_strict_1251_ = lean_ctor_get_uint8(v_x_1100_, sizeof(void*)*1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_x_1100_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1253_ = v_x_1100_;
v_isShared_1254_ = v_isSharedCheck_1275_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_bvarIdx_1250_);
lean_dec(v_x_1100_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1275_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___y_1256_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = lean_unsigned_to_nat(1024u);
v___x_1272_ = lean_nat_dec_le(v___x_1271_, v_prec_1101_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; 
v___x_1273_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1256_ = v___x_1273_;
goto v___jp_1255_;
}
else
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1256_ = v___x_1274_;
goto v___jp_1255_;
}
v___jp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; lean_object* v___x_1268_; 
v___x_1257_ = lean_box(1);
v___x_1258_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__20));
v___x_1259_ = l_Nat_reprFast(v_bvarIdx_1250_);
v___x_1260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
v___x_1261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1258_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v___x_1257_);
v___x_1263_ = l_Bool_repr___redArg(v_strict_1251_);
v___x_1264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
lean_inc(v___y_1256_);
v___x_1265_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___y_1256_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = 0;
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1265_);
v___x_1268_ = v___x_1253_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1265_);
v___x_1268_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1269_; 
lean_ctor_set_uint8(v___x_1268_, sizeof(void*)*1, v___x_1266_);
v___x_1269_ = l_Repr_addAppParen(v___x_1268_, v_prec_1101_);
return v___x_1269_;
}
}
}
}
case 7:
{
lean_object* v_n_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1296_; 
v_n_1276_ = lean_ctor_get(v_x_1100_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_x_1100_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1278_ = v_x_1100_;
v_isShared_1279_ = v_isSharedCheck_1296_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_n_1276_);
lean_dec(v_x_1100_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1296_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___y_1281_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = lean_unsigned_to_nat(1024u);
v___x_1293_ = lean_nat_dec_le(v___x_1292_, v_prec_1101_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1281_ = v___x_1294_;
goto v___jp_1280_;
}
else
{
lean_object* v___x_1295_; 
v___x_1295_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1281_ = v___x_1295_;
goto v___jp_1280_;
}
v___jp_1280_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1282_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__23));
v___x_1283_ = l_Nat_reprFast(v_n_1276_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set_tag(v___x_1278_, 3);
lean_ctor_set(v___x_1278_, 0, v___x_1283_);
v___x_1285_ = v___x_1278_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1282_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
lean_inc(v___y_1281_);
v___x_1287_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___y_1281_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = 0;
v___x_1289_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1289_, 0, v___x_1287_);
lean_ctor_set_uint8(v___x_1289_, sizeof(void*)*1, v___x_1288_);
v___x_1290_ = l_Repr_addAppParen(v___x_1289_, v_prec_1101_);
return v___x_1290_;
}
}
}
}
case 8:
{
lean_object* v_e_1297_; lean_object* v___y_1299_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v_e_1297_ = lean_ctor_get(v_x_1100_, 0);
lean_inc_ref(v_e_1297_);
lean_dec_ref_known(v_x_1100_, 1);
v___x_1308_ = lean_unsigned_to_nat(1024u);
v___x_1309_ = lean_nat_dec_le(v___x_1308_, v_prec_1101_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1299_ = v___x_1310_;
goto v___jp_1298_;
}
else
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1299_ = v___x_1311_;
goto v___jp_1298_;
}
v___jp_1298_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1300_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__26));
v___x_1301_ = lean_unsigned_to_nat(1024u);
v___x_1302_ = l_Lean_instReprExpr_repr(v_e_1297_, v___x_1301_);
v___x_1303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1300_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
lean_inc(v___y_1299_);
v___x_1304_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___y_1299_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = 0;
v___x_1306_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1306_, 0, v___x_1304_);
lean_ctor_set_uint8(v___x_1306_, sizeof(void*)*1, v___x_1305_);
v___x_1307_ = l_Repr_addAppParen(v___x_1306_, v_prec_1101_);
return v___x_1307_;
}
}
case 9:
{
lean_object* v_e_1312_; lean_object* v___y_1314_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v_e_1312_ = lean_ctor_get(v_x_1100_, 0);
lean_inc_ref(v_e_1312_);
lean_dec_ref_known(v_x_1100_, 1);
v___x_1323_ = lean_unsigned_to_nat(1024u);
v___x_1324_ = lean_nat_dec_le(v___x_1323_, v_prec_1101_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1314_ = v___x_1325_;
goto v___jp_1313_;
}
else
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1314_ = v___x_1326_;
goto v___jp_1313_;
}
v___jp_1313_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1315_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__29));
v___x_1316_ = lean_unsigned_to_nat(1024u);
v___x_1317_ = l_Lean_instReprExpr_repr(v_e_1312_, v___x_1316_);
v___x_1318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1315_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
lean_inc(v___y_1314_);
v___x_1319_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___y_1314_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = 0;
v___x_1321_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1321_, 0, v___x_1319_);
lean_ctor_set_uint8(v___x_1321_, sizeof(void*)*1, v___x_1320_);
v___x_1322_ = l_Repr_addAppParen(v___x_1321_, v_prec_1101_);
return v___x_1322_;
}
}
default: 
{
lean_object* v_bvarIdx_1327_; uint8_t v_strict_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1352_; 
v_bvarIdx_1327_ = lean_ctor_get(v_x_1100_, 0);
v_strict_1328_ = lean_ctor_get_uint8(v_x_1100_, sizeof(void*)*1);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_x_1100_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1330_ = v_x_1100_;
v_isShared_1331_ = v_isSharedCheck_1352_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_bvarIdx_1327_);
lean_dec(v_x_1100_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1352_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___y_1333_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1348_ = lean_unsigned_to_nat(1024u);
v___x_1349_ = lean_nat_dec_le(v___x_1348_, v_prec_1101_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__13);
v___y_1333_ = v___x_1350_;
goto v___jp_1332_;
}
else
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_obj_once(&l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14, &l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14_once, _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind_repr___closed__14);
v___y_1333_ = v___x_1351_;
goto v___jp_1332_;
}
v___jp_1332_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; lean_object* v___x_1345_; 
v___x_1334_ = lean_box(1);
v___x_1335_ = ((lean_object*)(l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___closed__32));
v___x_1336_ = l_Nat_reprFast(v_bvarIdx_1327_);
v___x_1337_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
v___x_1338_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1335_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
v___x_1339_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
lean_ctor_set(v___x_1339_, 1, v___x_1334_);
v___x_1340_ = l_Bool_repr___redArg(v_strict_1328_);
v___x_1341_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1339_);
lean_ctor_set(v___x_1341_, 1, v___x_1340_);
lean_inc(v___y_1333_);
v___x_1342_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___y_1333_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = 0;
if (v_isShared_1331_ == 0)
{
lean_ctor_set_tag(v___x_1330_, 6);
lean_ctor_set(v___x_1330_, 0, v___x_1342_);
v___x_1345_ = v___x_1330_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1342_);
v___x_1345_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1346_; 
lean_ctor_set_uint8(v___x_1345_, sizeof(void*)*1, v___x_1343_);
v___x_1346_ = l_Repr_addAppParen(v___x_1345_, v_prec_1101_);
return v___x_1346_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr___boxed(lean_object* v_x_1353_, lean_object* v_prec_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_Meta_Grind_instReprEMatchTheoremConstraint_repr(v_x_1353_, v_prec_1354_);
lean_dec(v_prec_1354_);
return v_res_1355_;
}
}
uint8_t l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(lean_object* v_x_1358_, lean_object* v_x_1359_){
_start:
{
lean_object* v_lhs_1361_; lean_object* v_rhs_1362_; lean_object* v_lhs_x27_1363_; lean_object* v_rhs_x27_1364_; lean_object* v_lhs_1368_; lean_object* v_n_1369_; lean_object* v_lhs_x27_1370_; lean_object* v_n_x27_1371_; lean_object* v_bvarIdx_1375_; uint8_t v_strict_1376_; lean_object* v_bvarIdx_x27_1377_; uint8_t v_strict_x27_1378_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v_decide_1382_; 
v___x_1380_ = lean_obj_tag_nat(v_x_1358_);
v___x_1381_ = lean_obj_tag_nat(v_x_1359_);
v_decide_1382_ = lean_nat_dec_eq(v___x_1380_, v___x_1381_);
if (v_decide_1382_ == 0)
{
return v_decide_1382_;
}
else
{
switch(lean_obj_tag(v_x_1358_))
{
case 0:
{
lean_object* v_lhs_1383_; lean_object* v_rhs_1384_; lean_object* v_lhs_1385_; lean_object* v_rhs_1386_; 
v_lhs_1383_ = lean_ctor_get(v_x_1358_, 0);
v_rhs_1384_ = lean_ctor_get(v_x_1358_, 1);
v_lhs_1385_ = lean_ctor_get(v_x_1359_, 0);
v_rhs_1386_ = lean_ctor_get(v_x_1359_, 1);
v_lhs_1361_ = v_lhs_1383_;
v_rhs_1362_ = v_rhs_1384_;
v_lhs_x27_1363_ = v_lhs_1385_;
v_rhs_x27_1364_ = v_rhs_1386_;
goto v___jp_1360_;
}
case 1:
{
lean_object* v_lhs_1387_; lean_object* v_rhs_1388_; lean_object* v_lhs_1389_; lean_object* v_rhs_1390_; 
v_lhs_1387_ = lean_ctor_get(v_x_1358_, 0);
v_rhs_1388_ = lean_ctor_get(v_x_1358_, 1);
v_lhs_1389_ = lean_ctor_get(v_x_1359_, 0);
v_rhs_1390_ = lean_ctor_get(v_x_1359_, 1);
v_lhs_1361_ = v_lhs_1387_;
v_rhs_1362_ = v_rhs_1388_;
v_lhs_x27_1363_ = v_lhs_1389_;
v_rhs_x27_1364_ = v_rhs_1390_;
goto v___jp_1360_;
}
case 2:
{
lean_object* v_lhs_1391_; lean_object* v_n_1392_; lean_object* v_lhs_1393_; lean_object* v_n_1394_; 
v_lhs_1391_ = lean_ctor_get(v_x_1358_, 0);
v_n_1392_ = lean_ctor_get(v_x_1358_, 1);
v_lhs_1393_ = lean_ctor_get(v_x_1359_, 0);
v_n_1394_ = lean_ctor_get(v_x_1359_, 1);
v_lhs_1368_ = v_lhs_1391_;
v_n_1369_ = v_n_1392_;
v_lhs_x27_1370_ = v_lhs_1393_;
v_n_x27_1371_ = v_n_1394_;
goto v___jp_1367_;
}
case 3:
{
lean_object* v_lhs_1395_; lean_object* v_n_1396_; lean_object* v_lhs_1397_; lean_object* v_n_1398_; 
v_lhs_1395_ = lean_ctor_get(v_x_1358_, 0);
v_n_1396_ = lean_ctor_get(v_x_1358_, 1);
v_lhs_1397_ = lean_ctor_get(v_x_1359_, 0);
v_n_1398_ = lean_ctor_get(v_x_1359_, 1);
v_lhs_1368_ = v_lhs_1395_;
v_n_1369_ = v_n_1396_;
v_lhs_x27_1370_ = v_lhs_1397_;
v_n_x27_1371_ = v_n_1398_;
goto v___jp_1367_;
}
case 6:
{
lean_object* v_bvarIdx_1399_; uint8_t v_strict_1400_; lean_object* v_bvarIdx_1401_; uint8_t v_strict_1402_; 
v_bvarIdx_1399_ = lean_ctor_get(v_x_1358_, 0);
v_strict_1400_ = lean_ctor_get_uint8(v_x_1358_, sizeof(void*)*1);
v_bvarIdx_1401_ = lean_ctor_get(v_x_1359_, 0);
v_strict_1402_ = lean_ctor_get_uint8(v_x_1359_, sizeof(void*)*1);
v_bvarIdx_1375_ = v_bvarIdx_1399_;
v_strict_1376_ = v_strict_1400_;
v_bvarIdx_x27_1377_ = v_bvarIdx_1401_;
v_strict_x27_1378_ = v_strict_1402_;
goto v___jp_1374_;
}
case 8:
{
lean_object* v_e_1403_; lean_object* v_e_1404_; uint8_t v___x_1405_; 
v_e_1403_ = lean_ctor_get(v_x_1358_, 0);
v_e_1404_ = lean_ctor_get(v_x_1359_, 0);
v___x_1405_ = lean_expr_eqv(v_e_1403_, v_e_1404_);
return v___x_1405_;
}
case 9:
{
lean_object* v_e_1406_; lean_object* v_e_1407_; uint8_t v___x_1408_; 
v_e_1406_ = lean_ctor_get(v_x_1358_, 0);
v_e_1407_ = lean_ctor_get(v_x_1359_, 0);
v___x_1408_ = lean_expr_eqv(v_e_1406_, v_e_1407_);
return v___x_1408_;
}
case 10:
{
lean_object* v_bvarIdx_1409_; uint8_t v_strict_1410_; lean_object* v_bvarIdx_1411_; uint8_t v_strict_1412_; 
v_bvarIdx_1409_ = lean_ctor_get(v_x_1358_, 0);
v_strict_1410_ = lean_ctor_get_uint8(v_x_1358_, sizeof(void*)*1);
v_bvarIdx_1411_ = lean_ctor_get(v_x_1359_, 0);
v_strict_1412_ = lean_ctor_get_uint8(v_x_1359_, sizeof(void*)*1);
v_bvarIdx_1375_ = v_bvarIdx_1409_;
v_strict_1376_ = v_strict_1410_;
v_bvarIdx_x27_1377_ = v_bvarIdx_1411_;
v_strict_x27_1378_ = v_strict_1412_;
goto v___jp_1374_;
}
default: 
{
lean_object* v_n_1413_; lean_object* v_n_1414_; uint8_t v___x_1415_; 
v_n_1413_ = lean_ctor_get(v_x_1358_, 0);
v_n_1414_ = lean_ctor_get(v_x_1359_, 0);
v___x_1415_ = lean_nat_dec_eq(v_n_1413_, v_n_1414_);
return v___x_1415_;
}
}
}
v___jp_1360_:
{
uint8_t v___x_1365_; 
v___x_1365_ = lean_nat_dec_eq(v_lhs_1361_, v_lhs_x27_1363_);
if (v___x_1365_ == 0)
{
return v___x_1365_;
}
else
{
uint8_t v___x_1366_; 
v___x_1366_ = l_Lean_Meta_Grind_instBEqCnstrRHS_beq(v_rhs_1362_, v_rhs_x27_1364_);
return v___x_1366_;
}
}
v___jp_1367_:
{
uint8_t v___x_1372_; 
v___x_1372_ = lean_nat_dec_eq(v_lhs_1368_, v_lhs_x27_1370_);
if (v___x_1372_ == 0)
{
return v___x_1372_;
}
else
{
uint8_t v___x_1373_; 
v___x_1373_ = lean_nat_dec_eq(v_n_1369_, v_n_x27_1371_);
return v___x_1373_;
}
}
v___jp_1374_:
{
uint8_t v___x_1379_; 
v___x_1379_ = lean_nat_dec_eq(v_bvarIdx_1375_, v_bvarIdx_x27_1377_);
if (v___x_1379_ == 0)
{
return v___x_1379_;
}
else
{
if (v_strict_x27_1378_ == 0)
{
if (v_strict_1376_ == 0)
{
return v___x_1379_;
}
else
{
return v_strict_x27_1378_;
}
}
else
{
return v_strict_1376_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1358_ = stack[0].m_obj;
lean_object* v_x_1359_ = stack[1].m_obj;
uint8_t v_res_1416_;
v_res_1416_ = l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(v_x_1358_, v_x_1359_);
stack->m_num = v_res_1416_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq___boxed(lean_object* v_x_1417_, lean_object* v_x_1418_){
_start:
{
uint8_t v_res_1419_; lean_object* v_r_1420_; 
v_res_1419_ = l_Lean_Meta_Grind_instBEqEMatchTheoremConstraint_beq(v_x_1417_, v_x_1418_);
lean_dec_ref(v_x_1418_);
lean_dec_ref(v_x_1417_);
v_r_1420_ = lean_box(v_res_1419_);
return v_r_1420_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0(void){
_start:
{
uint8_t v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1423_ = 0;
v___x_1424_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind_default));
v___x_1425_ = l_Lean_Meta_Grind_instInhabitedOrigin_default;
v___x_1426_ = lean_box(0);
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_1429_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_1430_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v___x_1428_);
lean_ctor_set(v___x_1430_, 2, v___x_1427_);
lean_ctor_set(v___x_1430_, 3, v___x_1426_);
lean_ctor_set(v___x_1430_, 4, v___x_1426_);
lean_ctor_set(v___x_1430_, 5, v___x_1425_);
lean_ctor_set(v___x_1430_, 6, v___x_1424_);
lean_ctor_set(v___x_1430_, 7, v___x_1426_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*8, v___x_1423_);
return v___x_1430_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default(void){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0, &l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default___closed__0);
return v___x_1431_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem(void){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default;
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0(lean_object* v_thm_1433_){
_start:
{
lean_object* v_symbols_1434_; 
v_symbols_1434_ = lean_ctor_get(v_thm_1433_, 4);
lean_inc(v_symbols_1434_);
return v_symbols_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0___boxed(lean_object* v_thm_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__0(v_thm_1435_);
lean_dec_ref(v_thm_1435_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__1(lean_object* v_thm_1437_, lean_object* v_symbols_1438_){
_start:
{
lean_object* v_levelParams_1439_; lean_object* v_proof_1440_; lean_object* v_numParams_1441_; lean_object* v_patterns_1442_; lean_object* v_origin_1443_; lean_object* v_kind_1444_; uint8_t v_minIndexable_1445_; lean_object* v_cnstrs_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
v_levelParams_1439_ = lean_ctor_get(v_thm_1437_, 0);
v_proof_1440_ = lean_ctor_get(v_thm_1437_, 1);
v_numParams_1441_ = lean_ctor_get(v_thm_1437_, 2);
v_patterns_1442_ = lean_ctor_get(v_thm_1437_, 3);
v_origin_1443_ = lean_ctor_get(v_thm_1437_, 5);
v_kind_1444_ = lean_ctor_get(v_thm_1437_, 6);
v_minIndexable_1445_ = lean_ctor_get_uint8(v_thm_1437_, sizeof(void*)*8);
v_cnstrs_1446_ = lean_ctor_get(v_thm_1437_, 7);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_thm_1437_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v_thm_1437_, 4);
lean_dec(v_unused_1454_);
v___x_1448_ = v_thm_1437_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_cnstrs_1446_);
lean_inc(v_kind_1444_);
lean_inc(v_origin_1443_);
lean_inc(v_patterns_1442_);
lean_inc(v_numParams_1441_);
lean_inc(v_proof_1440_);
lean_inc(v_levelParams_1439_);
lean_dec(v_thm_1437_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 4, v_symbols_1438_);
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_levelParams_1439_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_proof_1440_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_numParams_1441_);
lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_patterns_1442_);
lean_ctor_set(v_reuseFailAlloc_1452_, 4, v_symbols_1438_);
lean_ctor_set(v_reuseFailAlloc_1452_, 5, v_origin_1443_);
lean_ctor_set(v_reuseFailAlloc_1452_, 6, v_kind_1444_);
lean_ctor_set(v_reuseFailAlloc_1452_, 7, v_cnstrs_1446_);
lean_ctor_set_uint8(v_reuseFailAlloc_1452_, sizeof(void*)*8, v_minIndexable_1445_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2(lean_object* v_thm_1455_){
_start:
{
lean_object* v_origin_1456_; 
v_origin_1456_ = lean_ctor_get(v_thm_1455_, 5);
lean_inc_ref(v_origin_1456_);
return v_origin_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2___boxed(lean_object* v_thm_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__2(v_thm_1457_);
lean_dec_ref(v_thm_1457_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3(lean_object* v_thm_1459_){
_start:
{
lean_object* v_proof_1460_; 
v_proof_1460_ = lean_ctor_get(v_thm_1459_, 1);
lean_inc_ref(v_proof_1460_);
return v_proof_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3___boxed(lean_object* v_thm_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__3(v_thm_1461_);
lean_dec_ref(v_thm_1461_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4(lean_object* v_thm_1463_){
_start:
{
lean_object* v_levelParams_1464_; 
v_levelParams_1464_ = lean_ctor_get(v_thm_1463_, 0);
lean_inc_ref(v_levelParams_1464_);
return v_levelParams_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4___boxed(lean_object* v_thm_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Meta_Grind_instTheoremLikeEMatchTheorem___lam__4(v_thm_1465_);
lean_dec_ref(v_thm_1465_);
return v_res_1466_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1479_ = l_Lean_Meta_Grind_instInhabitedOrigin_default;
v___x_1480_ = lean_box(0);
v___x_1481_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3, &l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3_once, _init_l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__3);
v___x_1482_ = ((lean_object*)(l_Lean_Meta_Grind_instInhabitedCnstrRHS_default___closed__0));
v___x_1483_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
lean_ctor_set(v___x_1483_, 1, v___x_1481_);
lean_ctor_set(v___x_1483_, 2, v___x_1480_);
lean_ctor_set(v___x_1483_, 3, v___x_1479_);
return v___x_1483_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default(void){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0, &l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default___closed__0);
return v___x_1484_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedInjectiveTheorem(void){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_Meta_Grind_instInhabitedInjectiveTheorem_default;
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0(lean_object* v_thm_1486_){
_start:
{
lean_object* v_symbols_1487_; 
v_symbols_1487_ = lean_ctor_get(v_thm_1486_, 2);
lean_inc(v_symbols_1487_);
return v_symbols_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0___boxed(lean_object* v_thm_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__0(v_thm_1488_);
lean_dec_ref(v_thm_1488_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__1(lean_object* v_thm_1490_, lean_object* v_symbols_1491_){
_start:
{
lean_object* v_levelParams_1492_; lean_object* v_proof_1493_; lean_object* v_origin_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
v_levelParams_1492_ = lean_ctor_get(v_thm_1490_, 0);
v_proof_1493_ = lean_ctor_get(v_thm_1490_, 1);
v_origin_1494_ = lean_ctor_get(v_thm_1490_, 3);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_thm_1490_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v_thm_1490_, 2);
lean_dec(v_unused_1502_);
v___x_1496_ = v_thm_1490_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_origin_1494_);
lean_inc(v_proof_1493_);
lean_inc(v_levelParams_1492_);
lean_dec(v_thm_1490_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 2, v_symbols_1491_);
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_levelParams_1492_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_proof_1493_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_symbols_1491_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_origin_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2(lean_object* v_thm_1503_){
_start:
{
lean_object* v_origin_1504_; 
v_origin_1504_ = lean_ctor_get(v_thm_1503_, 3);
lean_inc_ref(v_origin_1504_);
return v_origin_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2___boxed(lean_object* v_thm_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__2(v_thm_1505_);
lean_dec_ref(v_thm_1505_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3(lean_object* v_thm_1507_){
_start:
{
lean_object* v_proof_1508_; 
v_proof_1508_ = lean_ctor_get(v_thm_1507_, 1);
lean_inc_ref(v_proof_1508_);
return v_proof_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3___boxed(lean_object* v_thm_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__3(v_thm_1509_);
lean_dec_ref(v_thm_1509_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4(lean_object* v_thm_1511_){
_start:
{
lean_object* v_levelParams_1512_; 
v_levelParams_1512_ = lean_ctor_get(v_thm_1511_, 0);
lean_inc_ref(v_levelParams_1512_);
return v_levelParams_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4___boxed(lean_object* v_thm_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_Meta_Grind_instTheoremLikeInjectiveTheorem___lam__4(v_thm_1513_);
lean_dec_ref(v_thm_1513_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorIdx___impl(lean_object* v_x_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_obj_tag_nat(v_x_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorIdx___impl___boxed(lean_object* v_x_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_Meta_Grind_Entry_ctorIdx___impl(v_x_1529_);
lean_dec_ref(v_x_1529_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim___redArg(lean_object* v_t_1531_, lean_object* v_k_1532_){
_start:
{
switch(lean_obj_tag(v_t_1531_))
{
case 2:
{
lean_object* v_declName_1533_; uint8_t v_eager_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_declName_1533_ = lean_ctor_get(v_t_1531_, 0);
lean_inc(v_declName_1533_);
v_eager_1534_ = lean_ctor_get_uint8(v_t_1531_, sizeof(void*)*1);
lean_dec_ref_known(v_t_1531_, 1);
v___x_1535_ = lean_box(v_eager_1534_);
v___x_1536_ = lean_apply_2(v_k_1532_, v_declName_1533_, v___x_1535_);
return v___x_1536_;
}
case 3:
{
lean_object* v_thm_1537_; lean_object* v___x_1538_; 
v_thm_1537_ = lean_ctor_get(v_t_1531_, 0);
lean_inc_ref(v_thm_1537_);
lean_dec_ref_known(v_t_1531_, 1);
v___x_1538_ = lean_apply_1(v_k_1532_, v_thm_1537_);
return v___x_1538_;
}
case 4:
{
lean_object* v_thm_1539_; lean_object* v___x_1540_; 
v_thm_1539_ = lean_ctor_get(v_t_1531_, 0);
lean_inc_ref(v_thm_1539_);
lean_dec_ref_known(v_t_1531_, 1);
v___x_1540_ = lean_apply_1(v_k_1532_, v_thm_1539_);
return v___x_1540_;
}
default: 
{
lean_object* v_declName_1541_; lean_object* v___x_1542_; 
v_declName_1541_ = lean_ctor_get(v_t_1531_, 0);
lean_inc(v_declName_1541_);
lean_dec_ref(v_t_1531_);
v___x_1542_ = lean_apply_1(v_k_1532_, v_declName_1541_);
return v___x_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim(lean_object* v_motive_1543_, lean_object* v_ctorIdx_1544_, lean_object* v_t_1545_, lean_object* v_h_1546_, lean_object* v_k_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1545_, v_k_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ctorElim___boxed(lean_object* v_motive_1549_, lean_object* v_ctorIdx_1550_, lean_object* v_t_1551_, lean_object* v_h_1552_, lean_object* v_k_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_Meta_Grind_Entry_ctorElim(v_motive_1549_, v_ctorIdx_1550_, v_t_1551_, v_h_1552_, v_k_1553_);
lean_dec(v_ctorIdx_1550_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ext_elim___redArg(lean_object* v_t_1555_, lean_object* v_ext_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1555_, v_ext_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ext_elim(lean_object* v_motive_1558_, lean_object* v_t_1559_, lean_object* v_h_1560_, lean_object* v_ext_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1559_, v_ext_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_funCC_elim___redArg(lean_object* v_t_1563_, lean_object* v_funCC_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1563_, v_funCC_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_funCC_elim(lean_object* v_motive_1566_, lean_object* v_t_1567_, lean_object* v_h_1568_, lean_object* v_funCC_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1567_, v_funCC_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_cases_elim___redArg(lean_object* v_t_1571_, lean_object* v_cases_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1571_, v_cases_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_cases_elim(lean_object* v_motive_1574_, lean_object* v_t_1575_, lean_object* v_h_1576_, lean_object* v_cases_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1575_, v_cases_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ematch_elim___redArg(lean_object* v_t_1579_, lean_object* v_ematch_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1579_, v_ematch_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_ematch_elim(lean_object* v_motive_1582_, lean_object* v_t_1583_, lean_object* v_h_1584_, lean_object* v_ematch_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1583_, v_ematch_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_inj_elim___redArg(lean_object* v_t_1587_, lean_object* v_inj_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1587_, v_inj_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Entry_inj_elim(lean_object* v_motive_1590_, lean_object* v_t_1591_, lean_object* v_h_1592_, lean_object* v_inj_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Meta_Grind_Entry_ctorElim___redArg(v_t_1591_, v_inj_1593_);
return v___x_1594_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0, &l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0);
v___x_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
return v___x_1600_;
}
}
lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg(){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___closed__0);
return v___x_1602_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1603_;
v_res_1603_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg();
stack->m_obj
 = v_res_1603_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg___boxed(lean_object* v___dummy_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg();
return v_res_1605_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___redArg();
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0(lean_object* v_00_u03b2_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0);
return v___x_1608_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_Meta_Grind_Theorems_mkEmpty___redArg();
return v___x_1609_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1610_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__0);
v___x_1611_ = l_Lean_NameSet_empty;
v___x_1612_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_instInhabitedExtensionState_default_spec__0___closed__0);
v___x_1613_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1, &l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__1);
v___x_1614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v___x_1612_);
lean_ctor_set(v___x_1614_, 2, v___x_1611_);
lean_ctor_set(v___x_1614_, 3, v___x_1610_);
lean_ctor_set(v___x_1614_, 4, v___x_1610_);
return v___x_1614_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default(void){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1);
return v___x_1615_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedExtensionState(void){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_x_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_, lean_object* v_x_1620_){
_start:
{
lean_object* v_ks_1621_; lean_object* v_vs_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1648_; 
v_ks_1621_ = lean_ctor_get(v_x_1617_, 0);
v_vs_1622_ = lean_ctor_get(v_x_1617_, 1);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_x_1617_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1624_ = v_x_1617_;
v_isShared_1625_ = v_isSharedCheck_1648_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_vs_1622_);
lean_inc(v_ks_1621_);
lean_dec(v_x_1617_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1648_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = lean_array_get_size(v_ks_1621_);
v___x_1627_ = lean_nat_dec_lt(v_x_1618_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
lean_dec(v_x_1618_);
v___x_1628_ = lean_array_push(v_ks_1621_, v_x_1619_);
v___x_1629_ = lean_array_push(v_vs_1622_, v_x_1620_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 1, v___x_1629_);
lean_ctor_set(v___x_1624_, 0, v___x_1628_);
v___x_1631_ = v___x_1624_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
else
{
lean_object* v_k_x27_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v_k_x27_1633_ = lean_array_fget_borrowed(v_ks_1621_, v_x_1618_);
v___x_1634_ = l_Lean_Meta_Grind_Origin_key(v_x_1619_);
v___x_1635_ = l_Lean_Meta_Grind_Origin_key(v_k_x27_1633_);
v___x_1636_ = lean_name_eq(v___x_1634_, v___x_1635_);
lean_dec(v___x_1635_);
lean_dec(v___x_1634_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1638_; 
if (v_isShared_1625_ == 0)
{
v___x_1638_ = v___x_1624_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_ks_1621_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_vs_1622_);
v___x_1638_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = lean_unsigned_to_nat(1u);
v___x_1640_ = lean_nat_add(v_x_1618_, v___x_1639_);
lean_dec(v_x_1618_);
v_x_1617_ = v___x_1638_;
v_x_1618_ = v___x_1640_;
goto _start;
}
}
else
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1643_ = lean_array_fset(v_ks_1621_, v_x_1618_, v_x_1619_);
v___x_1644_ = lean_array_fset(v_vs_1622_, v_x_1618_, v_x_1620_);
lean_dec(v_x_1618_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 1, v___x_1644_);
lean_ctor_set(v___x_1624_, 0, v___x_1643_);
v___x_1646_ = v___x_1624_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_n_1649_, lean_object* v_k_1650_, lean_object* v_v_1651_){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = lean_unsigned_to_nat(0u);
v___x_1653_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(v_n_1649_, v___x_1652_, v_k_1650_, v_v_1651_);
return v___x_1653_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1654_, size_t v_x_1655_, size_t v_x_1656_, lean_object* v_x_1657_, lean_object* v_x_1658_){
_start:
{
if (lean_obj_tag(v_x_1654_) == 0)
{
lean_object* v_es_1659_; size_t v___x_1660_; size_t v___x_1661_; lean_object* v_j_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; 
v_es_1659_ = lean_ctor_get(v_x_1654_, 0);
v___x_1660_ = ((size_t)31ULL);
v___x_1661_ = lean_usize_land(v_x_1655_, v___x_1660_);
v_j_1662_ = lean_usize_to_nat(v___x_1661_);
v___x_1663_ = lean_array_get_size(v_es_1659_);
v___x_1664_ = lean_nat_dec_lt(v_j_1662_, v___x_1663_);
if (v___x_1664_ == 0)
{
lean_dec(v_j_1662_);
lean_dec(v_x_1658_);
lean_dec_ref(v_x_1657_);
return v_x_1654_;
}
else
{
lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1705_; 
lean_inc_ref(v_es_1659_);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_x_1654_);
if (v_isSharedCheck_1705_ == 0)
{
lean_object* v_unused_1706_; 
v_unused_1706_ = lean_ctor_get(v_x_1654_, 0);
lean_dec(v_unused_1706_);
v___x_1666_ = v_x_1654_;
v_isShared_1667_ = v_isSharedCheck_1705_;
goto v_resetjp_1665_;
}
else
{
lean_dec(v_x_1654_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1705_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v_v_1668_; lean_object* v___x_1669_; lean_object* v_xs_x27_1670_; lean_object* v___y_1672_; 
v_v_1668_ = lean_array_fget(v_es_1659_, v_j_1662_);
v___x_1669_ = lean_box(0);
v_xs_x27_1670_ = lean_array_fset(v_es_1659_, v_j_1662_, v___x_1669_);
switch(lean_obj_tag(v_v_1668_))
{
case 0:
{
lean_object* v_key_1677_; lean_object* v_val_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1690_; 
v_key_1677_ = lean_ctor_get(v_v_1668_, 0);
v_val_1678_ = lean_ctor_get(v_v_1668_, 1);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_v_1668_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1680_ = v_v_1668_;
v_isShared_1681_ = v_isSharedCheck_1690_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_val_1678_);
lean_inc(v_key_1677_);
lean_dec(v_v_1668_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1690_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; 
v___x_1682_ = l_Lean_Meta_Grind_Origin_key(v_x_1657_);
v___x_1683_ = l_Lean_Meta_Grind_Origin_key(v_key_1677_);
v___x_1684_ = lean_name_eq(v___x_1682_, v___x_1683_);
lean_dec(v___x_1683_);
lean_dec(v___x_1682_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_del_object(v___x_1680_);
v___x_1685_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1677_, v_val_1678_, v_x_1657_, v_x_1658_);
v___x_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
v___y_1672_ = v___x_1686_;
goto v___jp_1671_;
}
else
{
lean_object* v___x_1688_; 
lean_dec(v_val_1678_);
lean_dec(v_key_1677_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 1, v_x_1658_);
lean_ctor_set(v___x_1680_, 0, v_x_1657_);
v___x_1688_ = v___x_1680_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_x_1657_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_x_1658_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
v___y_1672_ = v___x_1688_;
goto v___jp_1671_;
}
}
}
}
case 1:
{
lean_object* v_node_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1703_; 
v_node_1691_ = lean_ctor_get(v_v_1668_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_v_1668_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1693_ = v_v_1668_;
v_isShared_1694_ = v_isSharedCheck_1703_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_node_1691_);
lean_dec(v_v_1668_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1703_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
size_t v___x_1695_; size_t v___x_1696_; size_t v___x_1697_; size_t v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1695_ = ((size_t)5ULL);
v___x_1696_ = lean_usize_shift_right(v_x_1655_, v___x_1695_);
v___x_1697_ = ((size_t)1ULL);
v___x_1698_ = lean_usize_add(v_x_1656_, v___x_1697_);
v___x_1699_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_node_1691_, v___x_1696_, v___x_1698_, v_x_1657_, v_x_1658_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1699_);
v___x_1701_ = v___x_1693_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
v___y_1672_ = v___x_1701_;
goto v___jp_1671_;
}
}
}
default: 
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v_x_1657_);
lean_ctor_set(v___x_1704_, 1, v_x_1658_);
v___y_1672_ = v___x_1704_;
goto v___jp_1671_;
}
}
v___jp_1671_:
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1673_ = lean_array_fset(v_xs_x27_1670_, v_j_1662_, v___y_1672_);
lean_dec(v_j_1662_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1673_);
v___x_1675_ = v___x_1666_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
else
{
lean_object* v_ks_1707_; lean_object* v_vs_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1726_; 
v_ks_1707_ = lean_ctor_get(v_x_1654_, 0);
v_vs_1708_ = lean_ctor_get(v_x_1654_, 1);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_x_1654_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1710_ = v_x_1654_;
v_isShared_1711_ = v_isSharedCheck_1726_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_vs_1708_);
lean_inc(v_ks_1707_);
lean_dec(v_x_1654_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1726_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_ks_1707_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_vs_1708_);
v___x_1713_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v_newNode_1714_; size_t v___x_1715_; uint8_t v___x_1716_; 
v_newNode_1714_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(v___x_1713_, v_x_1657_, v_x_1658_);
v___x_1715_ = ((size_t)7ULL);
v___x_1716_ = lean_usize_dec_le(v___x_1715_, v_x_1656_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1717_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1714_);
v___x_1718_ = lean_unsigned_to_nat(4u);
v___x_1719_ = lean_nat_dec_lt(v___x_1717_, v___x_1718_);
lean_dec(v___x_1717_);
if (v___x_1719_ == 0)
{
lean_object* v_ks_1720_; lean_object* v_vs_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v_ks_1720_ = lean_ctor_get(v_newNode_1714_, 0);
lean_inc_ref(v_ks_1720_);
v_vs_1721_ = lean_ctor_get(v_newNode_1714_, 1);
lean_inc_ref(v_vs_1721_);
lean_dec_ref(v_newNode_1714_);
v___x_1722_ = lean_unsigned_to_nat(0u);
v___x_1723_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0_spec__0___redArg___closed__0);
v___x_1724_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_x_1656_, v_ks_1720_, v_vs_1721_, v___x_1722_, v___x_1723_);
lean_dec_ref(v_vs_1721_);
lean_dec_ref(v_ks_1720_);
return v___x_1724_;
}
else
{
return v_newNode_1714_;
}
}
else
{
return v_newNode_1714_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1654_ = stack[0].m_obj;
size_t v_x_1655_ = stack[1].m_num;
size_t v_x_1656_ = stack[2].m_num;
lean_object* v_x_1657_ = stack[3].m_obj;
lean_object* v_x_1658_ = stack[4].m_obj;
lean_object* v_res_1727_;
v_res_1727_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_1654_, v_x_1655_, v_x_1656_, v_x_1657_, v_x_1658_);
stack->m_obj
 = v_res_1727_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(size_t v_depth_1728_, lean_object* v_keys_1729_, lean_object* v_vals_1730_, lean_object* v_i_1731_, lean_object* v_entries_1732_){
_start:
{
lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = lean_array_get_size(v_keys_1729_);
v___x_1734_ = lean_nat_dec_lt(v_i_1731_, v___x_1733_);
if (v___x_1734_ == 0)
{
lean_dec(v_i_1731_);
return v_entries_1732_;
}
else
{
lean_object* v_k_1735_; lean_object* v_v_1736_; uint64_t v___y_1738_; lean_object* v___x_1749_; 
v_k_1735_ = lean_array_fget_borrowed(v_keys_1729_, v_i_1731_);
v_v_1736_ = lean_array_fget_borrowed(v_vals_1730_, v_i_1731_);
v___x_1749_ = l_Lean_Meta_Grind_Origin_key(v_k_1735_);
if (lean_obj_tag(v___x_1749_) == 0)
{
uint64_t v___x_1750_; 
v___x_1750_ = 1723ULL;
v___y_1738_ = v___x_1750_;
goto v___jp_1737_;
}
else
{
uint64_t v_hash_1751_; 
v_hash_1751_ = lean_ctor_get_uint64(v___x_1749_, sizeof(void*)*2);
lean_dec(v___x_1749_);
v___y_1738_ = v_hash_1751_;
goto v___jp_1737_;
}
v___jp_1737_:
{
size_t v_h_1739_; size_t v___x_1740_; lean_object* v___x_1741_; size_t v___x_1742_; size_t v___x_1743_; size_t v___x_1744_; size_t v_h_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_h_1739_ = lean_uint64_to_usize(v___y_1738_);
v___x_1740_ = ((size_t)5ULL);
v___x_1741_ = lean_unsigned_to_nat(1u);
v___x_1742_ = ((size_t)1ULL);
v___x_1743_ = lean_usize_sub(v_depth_1728_, v___x_1742_);
v___x_1744_ = lean_usize_mul(v___x_1740_, v___x_1743_);
v_h_1745_ = lean_usize_shift_right(v_h_1739_, v___x_1744_);
v___x_1746_ = lean_nat_add(v_i_1731_, v___x_1741_);
lean_dec(v_i_1731_);
lean_inc(v_v_1736_);
lean_inc(v_k_1735_);
v___x_1747_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_entries_1732_, v_h_1745_, v_depth_1728_, v_k_1735_, v_v_1736_);
v_i_1731_ = v___x_1746_;
v_entries_1732_ = v___x_1747_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1728_ = stack[0].m_num;
lean_object* v_keys_1729_ = stack[1].m_obj;
lean_object* v_vals_1730_ = stack[2].m_obj;
lean_object* v_i_1731_ = stack[3].m_obj;
lean_object* v_entries_1732_ = stack[4].m_obj;
lean_object* v_res_1752_;
v_res_1752_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_depth_1728_, v_keys_1729_, v_vals_1730_, v_i_1731_, v_entries_1732_);
stack->m_obj
 = v_res_1752_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_depth_1753_, lean_object* v_keys_1754_, lean_object* v_vals_1755_, lean_object* v_i_1756_, lean_object* v_entries_1757_){
_start:
{
size_t v_depth_boxed_1758_; lean_object* v_res_1759_; 
v_depth_boxed_1758_ = lean_unbox_usize(v_depth_1753_);
lean_dec(v_depth_1753_);
v_res_1759_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_depth_boxed_1758_, v_keys_1754_, v_vals_1755_, v_i_1756_, v_entries_1757_);
lean_dec_ref(v_vals_1755_);
lean_dec_ref(v_keys_1754_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_x_1760_, lean_object* v_x_1761_, lean_object* v_x_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_){
_start:
{
size_t v_x_1291__boxed_1765_; size_t v_x_1292__boxed_1766_; lean_object* v_res_1767_; 
v_x_1291__boxed_1765_ = lean_unbox_usize(v_x_1761_);
lean_dec(v_x_1761_);
v_x_1292__boxed_1766_ = lean_unbox_usize(v_x_1762_);
lean_dec(v_x_1762_);
v_res_1767_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_1760_, v_x_1291__boxed_1765_, v_x_1292__boxed_1766_, v_x_1763_, v_x_1764_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(lean_object* v_x_1768_, lean_object* v_x_1769_, lean_object* v_x_1770_){
_start:
{
uint64_t v___y_1772_; lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_Meta_Grind_Origin_key(v_x_1769_);
if (lean_obj_tag(v___x_1776_) == 0)
{
uint64_t v___x_1777_; 
v___x_1777_ = 1723ULL;
v___y_1772_ = v___x_1777_;
goto v___jp_1771_;
}
else
{
uint64_t v_hash_1778_; 
v_hash_1778_ = lean_ctor_get_uint64(v___x_1776_, sizeof(void*)*2);
lean_dec(v___x_1776_);
v___y_1772_ = v_hash_1778_;
goto v___jp_1771_;
}
v___jp_1771_:
{
size_t v___x_1773_; size_t v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = lean_uint64_to_usize(v___y_1772_);
v___x_1774_ = ((size_t)1ULL);
v___x_1775_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_1768_, v___x_1773_, v___x_1774_, v_x_1769_, v_x_1770_);
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(lean_object* v_keys_1779_, lean_object* v_vals_1780_, lean_object* v_i_1781_, lean_object* v_k_1782_){
_start:
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = lean_array_get_size(v_keys_1779_);
v___x_1784_ = lean_nat_dec_lt(v_i_1781_, v___x_1783_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; 
lean_dec(v_i_1781_);
v___x_1785_ = lean_box(0);
return v___x_1785_;
}
else
{
lean_object* v_k_x27_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v_k_x27_1786_ = lean_array_fget_borrowed(v_keys_1779_, v_i_1781_);
v___x_1787_ = l_Lean_Meta_Grind_Origin_key(v_k_1782_);
v___x_1788_ = l_Lean_Meta_Grind_Origin_key(v_k_x27_1786_);
v___x_1789_ = lean_name_eq(v___x_1787_, v___x_1788_);
lean_dec(v___x_1788_);
lean_dec(v___x_1787_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = lean_unsigned_to_nat(1u);
v___x_1791_ = lean_nat_add(v_i_1781_, v___x_1790_);
lean_dec(v_i_1781_);
v_i_1781_ = v___x_1791_;
goto _start;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = lean_array_fget_borrowed(v_vals_1780_, v_i_1781_);
lean_dec(v_i_1781_);
lean_inc(v___x_1793_);
v___x_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
return v___x_1794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg___boxed(lean_object* v_keys_1795_, lean_object* v_vals_1796_, lean_object* v_i_1797_, lean_object* v_k_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_keys_1795_, v_vals_1796_, v_i_1797_, v_k_1798_);
lean_dec_ref(v_k_1798_);
lean_dec_ref(v_vals_1796_);
lean_dec_ref(v_keys_1795_);
return v_res_1799_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(lean_object* v_x_1800_, size_t v_x_1801_, lean_object* v_x_1802_){
_start:
{
if (lean_obj_tag(v_x_1800_) == 0)
{
lean_object* v_es_1803_; lean_object* v___x_1804_; size_t v___x_1805_; size_t v___x_1806_; lean_object* v_j_1807_; lean_object* v___x_1808_; 
v_es_1803_ = lean_ctor_get(v_x_1800_, 0);
v___x_1804_ = lean_box(2);
v___x_1805_ = ((size_t)31ULL);
v___x_1806_ = lean_usize_land(v_x_1801_, v___x_1805_);
v_j_1807_ = lean_usize_to_nat(v___x_1806_);
v___x_1808_ = lean_array_get_borrowed(v___x_1804_, v_es_1803_, v_j_1807_);
lean_dec(v_j_1807_);
switch(lean_obj_tag(v___x_1808_))
{
case 0:
{
lean_object* v_key_1809_; lean_object* v_val_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; uint8_t v___x_1813_; 
v_key_1809_ = lean_ctor_get(v___x_1808_, 0);
v_val_1810_ = lean_ctor_get(v___x_1808_, 1);
v___x_1811_ = l_Lean_Meta_Grind_Origin_key(v_x_1802_);
v___x_1812_ = l_Lean_Meta_Grind_Origin_key(v_key_1809_);
v___x_1813_ = lean_name_eq(v___x_1811_, v___x_1812_);
lean_dec(v___x_1812_);
lean_dec(v___x_1811_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_box(0);
return v___x_1814_;
}
else
{
lean_object* v___x_1815_; 
lean_inc(v_val_1810_);
v___x_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1815_, 0, v_val_1810_);
return v___x_1815_;
}
}
case 1:
{
lean_object* v_node_1816_; size_t v___x_1817_; size_t v___x_1818_; 
v_node_1816_ = lean_ctor_get(v___x_1808_, 0);
v___x_1817_ = ((size_t)5ULL);
v___x_1818_ = lean_usize_shift_right(v_x_1801_, v___x_1817_);
v_x_1800_ = v_node_1816_;
v_x_1801_ = v___x_1818_;
goto _start;
}
default: 
{
lean_object* v___x_1820_; 
v___x_1820_ = lean_box(0);
return v___x_1820_;
}
}
}
else
{
lean_object* v_ks_1821_; lean_object* v_vs_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v_ks_1821_ = lean_ctor_get(v_x_1800_, 0);
v_vs_1822_ = lean_ctor_get(v_x_1800_, 1);
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_ks_1821_, v_vs_1822_, v___x_1823_, v_x_1802_);
return v___x_1824_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1800_ = stack[0].m_obj;
size_t v_x_1801_ = stack[1].m_num;
lean_object* v_x_1802_ = stack[2].m_obj;
lean_object* v_res_1825_;
v_res_1825_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_1800_, v_x_1801_, v_x_1802_);
stack->m_obj
 = v_res_1825_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_x_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_){
_start:
{
size_t v_x_1600__boxed_1829_; lean_object* v_res_1830_; 
v_x_1600__boxed_1829_ = lean_unbox_usize(v_x_1827_);
lean_dec(v_x_1827_);
v_res_1830_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_1826_, v_x_1600__boxed_1829_, v_x_1828_);
lean_dec_ref(v_x_1828_);
lean_dec_ref(v_x_1826_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(lean_object* v_x_1831_, lean_object* v_x_1832_){
_start:
{
uint64_t v___y_1834_; lean_object* v___x_1837_; 
v___x_1837_ = l_Lean_Meta_Grind_Origin_key(v_x_1832_);
if (lean_obj_tag(v___x_1837_) == 0)
{
uint64_t v___x_1838_; 
v___x_1838_ = 1723ULL;
v___y_1834_ = v___x_1838_;
goto v___jp_1833_;
}
else
{
uint64_t v_hash_1839_; 
v_hash_1839_ = lean_ctor_get_uint64(v___x_1837_, sizeof(void*)*2);
lean_dec(v___x_1837_);
v___y_1834_ = v_hash_1839_;
goto v___jp_1833_;
}
v___jp_1833_:
{
size_t v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = lean_uint64_to_usize(v___y_1834_);
v___x_1836_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_1831_, v___x_1835_, v_x_1832_);
return v___x_1836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg___boxed(lean_object* v_x_1840_, lean_object* v_x_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_x_1840_, v_x_1841_);
lean_dec_ref(v_x_1841_);
lean_dec_ref(v_x_1840_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(lean_object* v_keys_1843_, lean_object* v_vals_1844_, lean_object* v_i_1845_, lean_object* v_k_1846_){
_start:
{
lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1847_ = lean_array_get_size(v_keys_1843_);
v___x_1848_ = lean_nat_dec_lt(v_i_1845_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; 
lean_dec(v_i_1845_);
v___x_1849_ = lean_box(0);
return v___x_1849_;
}
else
{
lean_object* v_k_x27_1850_; uint8_t v___x_1851_; 
v_k_x27_1850_ = lean_array_fget_borrowed(v_keys_1843_, v_i_1845_);
v___x_1851_ = lean_name_eq(v_k_1846_, v_k_x27_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = lean_nat_add(v_i_1845_, v___x_1852_);
lean_dec(v_i_1845_);
v_i_1845_ = v___x_1853_;
goto _start;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_array_fget_borrowed(v_vals_1844_, v_i_1845_);
lean_dec(v_i_1845_);
lean_inc(v___x_1855_);
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg___boxed(lean_object* v_keys_1857_, lean_object* v_vals_1858_, lean_object* v_i_1859_, lean_object* v_k_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_keys_1857_, v_vals_1858_, v_i_1859_, v_k_1860_);
lean_dec(v_k_1860_);
lean_dec_ref(v_vals_1858_);
lean_dec_ref(v_keys_1857_);
return v_res_1861_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(lean_object* v_x_1862_, size_t v_x_1863_, lean_object* v_x_1864_){
_start:
{
if (lean_obj_tag(v_x_1862_) == 0)
{
lean_object* v_es_1865_; lean_object* v___x_1866_; size_t v___x_1867_; size_t v___x_1868_; lean_object* v_j_1869_; lean_object* v___x_1870_; 
v_es_1865_ = lean_ctor_get(v_x_1862_, 0);
v___x_1866_ = lean_box(2);
v___x_1867_ = ((size_t)31ULL);
v___x_1868_ = lean_usize_land(v_x_1863_, v___x_1867_);
v_j_1869_ = lean_usize_to_nat(v___x_1868_);
v___x_1870_ = lean_array_get_borrowed(v___x_1866_, v_es_1865_, v_j_1869_);
lean_dec(v_j_1869_);
switch(lean_obj_tag(v___x_1870_))
{
case 0:
{
lean_object* v_key_1871_; lean_object* v_val_1872_; uint8_t v___x_1873_; 
v_key_1871_ = lean_ctor_get(v___x_1870_, 0);
v_val_1872_ = lean_ctor_get(v___x_1870_, 1);
v___x_1873_ = lean_name_eq(v_x_1864_, v_key_1871_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_box(0);
return v___x_1874_;
}
else
{
lean_object* v___x_1875_; 
lean_inc(v_val_1872_);
v___x_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1875_, 0, v_val_1872_);
return v___x_1875_;
}
}
case 1:
{
lean_object* v_node_1876_; size_t v___x_1877_; size_t v___x_1878_; 
v_node_1876_ = lean_ctor_get(v___x_1870_, 0);
v___x_1877_ = ((size_t)5ULL);
v___x_1878_ = lean_usize_shift_right(v_x_1863_, v___x_1877_);
v_x_1862_ = v_node_1876_;
v_x_1863_ = v___x_1878_;
goto _start;
}
default: 
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_box(0);
return v___x_1880_;
}
}
}
else
{
lean_object* v_ks_1881_; lean_object* v_vs_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v_ks_1881_ = lean_ctor_get(v_x_1862_, 0);
v_vs_1882_ = lean_ctor_get(v_x_1862_, 1);
v___x_1883_ = lean_unsigned_to_nat(0u);
v___x_1884_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_ks_1881_, v_vs_1882_, v___x_1883_, v_x_1864_);
return v___x_1884_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1862_ = stack[0].m_obj;
size_t v_x_1863_ = stack[1].m_num;
lean_object* v_x_1864_ = stack[2].m_obj;
lean_object* v_res_1885_;
v_res_1885_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_1862_, v_x_1863_, v_x_1864_);
stack->m_obj
 = v_res_1885_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg___boxed(lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_){
_start:
{
size_t v_x_1733__boxed_1889_; lean_object* v_res_1890_; 
v_x_1733__boxed_1889_ = lean_unbox_usize(v_x_1887_);
lean_dec(v_x_1887_);
v_res_1890_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_1886_, v_x_1733__boxed_1889_, v_x_1888_);
lean_dec(v_x_1888_);
lean_dec_ref(v_x_1886_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(lean_object* v_x_1891_, lean_object* v_x_1892_){
_start:
{
uint64_t v___y_1894_; 
if (lean_obj_tag(v_x_1892_) == 0)
{
uint64_t v___x_1897_; 
v___x_1897_ = 1723ULL;
v___y_1894_ = v___x_1897_;
goto v___jp_1893_;
}
else
{
uint64_t v_hash_1898_; 
v_hash_1898_ = lean_ctor_get_uint64(v_x_1892_, sizeof(void*)*2);
v___y_1894_ = v_hash_1898_;
goto v___jp_1893_;
}
v___jp_1893_:
{
size_t v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_uint64_to_usize(v___y_1894_);
v___x_1896_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_1891_, v___x_1895_, v_x_1892_);
return v___x_1896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg___boxed(lean_object* v_x_1899_, lean_object* v_x_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_x_1899_, v_x_1900_);
lean_dec(v_x_1900_);
lean_dec_ref(v_x_1899_);
return v_res_1901_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Lean_Meta_Grind_instInhabitedTheorems_default___redArg();
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0(lean_object* v_msg_1910_){
_start:
{
lean_object* v___f_1911_; lean_object* v___f_1912_; lean_object* v___f_1913_; lean_object* v___f_1914_; lean_object* v___f_1915_; lean_object* v___f_1916_; lean_object* v___f_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___f_1911_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0));
v___f_1912_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1));
v___f_1913_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2));
v___f_1914_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3));
v___f_1915_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4));
v___f_1916_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5));
v___f_1917_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6));
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___f_1911_);
lean_ctor_set(v___x_1918_, 1, v___f_1912_);
v___x_1919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v___f_1913_);
lean_ctor_set(v___x_1919_, 2, v___f_1914_);
lean_ctor_set(v___x_1919_, 3, v___f_1915_);
lean_ctor_set(v___x_1919_, 4, v___f_1916_);
v___x_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
lean_ctor_set(v___x_1920_, 1, v___f_1917_);
v___x_1921_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7, &l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once, _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7);
v___x_1922_ = l_instInhabitedOfMonad___redArg(v___x_1920_, v___x_1921_);
v___x_1923_ = lean_panic_fn_borrowed(v___x_1922_, v_msg_1910_);
lean_dec(v___x_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(lean_object* v_xs_1924_, lean_object* v_v_1925_, lean_object* v_i_1926_){
_start:
{
lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = lean_array_get_size(v_xs_1924_);
v___x_1928_ = lean_nat_dec_lt(v_i_1926_, v___x_1927_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; 
lean_dec(v_i_1926_);
v___x_1929_ = lean_box(0);
return v___x_1929_;
}
else
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; 
v___x_1930_ = lean_array_fget_borrowed(v_xs_1924_, v_i_1926_);
v___x_1931_ = l_Lean_Meta_Grind_Origin_key(v___x_1930_);
v___x_1932_ = l_Lean_Meta_Grind_Origin_key(v_v_1925_);
v___x_1933_ = lean_name_eq(v___x_1931_, v___x_1932_);
lean_dec(v___x_1932_);
lean_dec(v___x_1931_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = lean_unsigned_to_nat(1u);
v___x_1935_ = lean_nat_add(v_i_1926_, v___x_1934_);
lean_dec(v_i_1926_);
v_i_1926_ = v___x_1935_;
goto _start;
}
else
{
lean_object* v___x_1937_; 
v___x_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1937_, 0, v_i_1926_);
return v___x_1937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13___boxed(lean_object* v_xs_1938_, lean_object* v_v_1939_, lean_object* v_i_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(v_xs_1938_, v_v_1939_, v_i_1940_);
lean_dec_ref(v_v_1939_);
lean_dec_ref(v_xs_1938_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(lean_object* v_xs_1942_, lean_object* v_v_1943_){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9_spec__13(v_xs_1942_, v_v_1943_, v___x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9___boxed(lean_object* v_xs_1946_, lean_object* v_v_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(v_xs_1946_, v_v_1947_);
lean_dec_ref(v_v_1947_);
lean_dec_ref(v_xs_1946_);
return v_res_1948_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(lean_object* v_x_1949_, size_t v_x_1950_, lean_object* v_x_1951_){
_start:
{
if (lean_obj_tag(v_x_1949_) == 0)
{
lean_object* v_es_1952_; lean_object* v___x_1953_; size_t v___x_1954_; size_t v___x_1955_; lean_object* v_j_1956_; lean_object* v_entry_1957_; 
v_es_1952_ = lean_ctor_get(v_x_1949_, 0);
v___x_1953_ = lean_box(2);
v___x_1954_ = ((size_t)31ULL);
v___x_1955_ = lean_usize_land(v_x_1950_, v___x_1954_);
v_j_1956_ = lean_usize_to_nat(v___x_1955_);
v_entry_1957_ = lean_array_get(v___x_1953_, v_es_1952_, v_j_1956_);
switch(lean_obj_tag(v_entry_1957_))
{
case 0:
{
lean_object* v_key_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
v_key_1958_ = lean_ctor_get(v_entry_1957_, 0);
lean_inc(v_key_1958_);
lean_dec_ref_known(v_entry_1957_, 2);
v___x_1959_ = l_Lean_Meta_Grind_Origin_key(v_x_1951_);
v___x_1960_ = l_Lean_Meta_Grind_Origin_key(v_key_1958_);
lean_dec(v_key_1958_);
v___x_1961_ = lean_name_eq(v___x_1959_, v___x_1960_);
lean_dec(v___x_1960_);
lean_dec(v___x_1959_);
if (v___x_1961_ == 0)
{
lean_dec(v_j_1956_);
return v_x_1949_;
}
else
{
lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1969_; 
lean_inc_ref(v_es_1952_);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_x_1949_);
if (v_isSharedCheck_1969_ == 0)
{
lean_object* v_unused_1970_; 
v_unused_1970_ = lean_ctor_get(v_x_1949_, 0);
lean_dec(v_unused_1970_);
v___x_1963_ = v_x_1949_;
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
else
{
lean_dec(v_x_1949_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1969_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1965_ = lean_array_set(v_es_1952_, v_j_1956_, v___x_1953_);
lean_dec(v_j_1956_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1965_);
v___x_1967_ = v___x_1963_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
case 1:
{
lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2005_; 
lean_inc_ref(v_es_1952_);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_x_1949_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; 
v_unused_2006_ = lean_ctor_get(v_x_1949_, 0);
lean_dec(v_unused_2006_);
v___x_1972_ = v_x_1949_;
v_isShared_1973_ = v_isSharedCheck_2005_;
goto v_resetjp_1971_;
}
else
{
lean_dec(v_x_1949_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2005_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_node_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_2004_; 
v_node_1974_ = lean_ctor_get(v_entry_1957_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_entry_1957_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1976_ = v_entry_1957_;
v_isShared_1977_ = v_isSharedCheck_2004_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_node_1974_);
lean_dec(v_entry_1957_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_2004_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
size_t v___x_1978_; lean_object* v_entries_1979_; size_t v___x_1980_; lean_object* v_newNode_1981_; lean_object* v___x_1982_; 
v___x_1978_ = ((size_t)5ULL);
v_entries_1979_ = lean_array_set(v_es_1952_, v_j_1956_, v___x_1953_);
v___x_1980_ = lean_usize_shift_right(v_x_1950_, v___x_1978_);
v_newNode_1981_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_node_1974_, v___x_1980_, v_x_1951_);
lean_inc_ref(v_newNode_1981_);
v___x_1982_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1981_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v___x_1984_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v_newNode_1981_);
v___x_1984_ = v___x_1976_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_newNode_1981_);
v___x_1984_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1985_ = lean_array_set(v_entries_1979_, v_j_1956_, v___x_1984_);
lean_dec(v_j_1956_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1985_);
v___x_1987_ = v___x_1972_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
else
{
lean_object* v_val_1990_; lean_object* v_fst_1991_; lean_object* v_snd_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v_newNode_1981_);
lean_del_object(v___x_1976_);
v_val_1990_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_val_1990_);
lean_dec_ref_known(v___x_1982_, 1);
v_fst_1991_ = lean_ctor_get(v_val_1990_, 0);
v_snd_1992_ = lean_ctor_get(v_val_1990_, 1);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_val_1990_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1994_ = v_val_1990_;
v_isShared_1995_ = v_isSharedCheck_2003_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_snd_1992_);
lean_inc(v_fst_1991_);
lean_dec(v_val_1990_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2003_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_fst_1991_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_snd_1992_);
v___x_1997_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1998_ = lean_array_set(v_entries_1979_, v_j_1956_, v___x_1997_);
lean_dec(v_j_1956_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1998_);
v___x_2000_ = v___x_1972_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
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
}
}
}
default: 
{
lean_dec(v_j_1956_);
return v_x_1949_;
}
}
}
else
{
lean_object* v_ks_2007_; lean_object* v_vs_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2022_; 
v_ks_2007_ = lean_ctor_get(v_x_1949_, 0);
v_vs_2008_ = lean_ctor_get(v_x_1949_, 1);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_x_1949_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2010_ = v_x_1949_;
v_isShared_2011_ = v_isSharedCheck_2022_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_vs_2008_);
lean_inc(v_ks_2007_);
lean_dec(v_x_1949_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2022_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_spec__9(v_ks_2007_, v_x_1951_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v___x_2014_; 
if (v_isShared_2011_ == 0)
{
v___x_2014_ = v___x_2010_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_ks_2007_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_vs_2008_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
else
{
lean_object* v_val_2016_; lean_object* v_keys_x27_2017_; lean_object* v_vals_x27_2018_; lean_object* v___x_2020_; 
v_val_2016_ = lean_ctor_get(v___x_2012_, 0);
lean_inc_n(v_val_2016_, 2);
lean_dec_ref_known(v___x_2012_, 1);
v_keys_x27_2017_ = l_Array_eraseIdx___redArg(v_ks_2007_, v_val_2016_);
v_vals_x27_2018_ = l_Array_eraseIdx___redArg(v_vs_2008_, v_val_2016_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v_vals_x27_2018_);
lean_ctor_set(v___x_2010_, 0, v_keys_x27_2017_);
v___x_2020_ = v___x_2010_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_keys_x27_2017_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_vals_x27_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1949_ = stack[0].m_obj;
size_t v_x_1950_ = stack[1].m_num;
lean_object* v_x_1951_ = stack[2].m_obj;
lean_object* v_res_2023_;
v_res_2023_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_1949_, v_x_1950_, v_x_1951_);
stack->m_obj
 = v_res_2023_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_x_2024_, lean_object* v_x_2025_, lean_object* v_x_2026_){
_start:
{
size_t v_x_1940__boxed_2027_; lean_object* v_res_2028_; 
v_x_1940__boxed_2027_ = lean_unbox_usize(v_x_2025_);
lean_dec(v_x_2025_);
v_res_2028_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2024_, v_x_1940__boxed_2027_, v_x_2026_);
lean_dec_ref(v_x_2026_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(lean_object* v_x_2029_, lean_object* v_x_2030_){
_start:
{
uint64_t v___y_2032_; lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_Meta_Grind_Origin_key(v_x_2030_);
if (lean_obj_tag(v___x_2035_) == 0)
{
uint64_t v___x_2036_; 
v___x_2036_ = 1723ULL;
v___y_2032_ = v___x_2036_;
goto v___jp_2031_;
}
else
{
uint64_t v_hash_2037_; 
v_hash_2037_ = lean_ctor_get_uint64(v___x_2035_, sizeof(void*)*2);
lean_dec(v___x_2035_);
v___y_2032_ = v_hash_2037_;
goto v___jp_2031_;
}
v___jp_2031_:
{
size_t v_h_2033_; lean_object* v___x_2034_; 
v_h_2033_ = lean_uint64_to_usize(v___y_2032_);
v___x_2034_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2029_, v_h_2033_, v_x_2030_);
return v___x_2034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg___boxed(lean_object* v_x_2038_, lean_object* v_x_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_x_2038_, v_x_2039_);
lean_dec_ref(v_x_2039_);
return v_res_2040_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2044_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2));
v___x_2045_ = lean_unsigned_to_nat(6u);
v___x_2046_ = lean_unsigned_to_nat(82u);
v___x_2047_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__1));
v___x_2048_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__0));
v___x_2049_ = l_mkPanicMessageWithDecl(v___x_2048_, v___x_2047_, v___x_2046_, v___x_2045_, v___x_2044_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0(lean_object* v_s_2050_, lean_object* v_thm_2051_){
_start:
{
lean_object* v_symbols_2055_; 
v_symbols_2055_ = lean_ctor_get(v_thm_2051_, 4);
lean_inc(v_symbols_2055_);
if (lean_obj_tag(v_symbols_2055_) == 1)
{
lean_object* v_head_2056_; 
v_head_2056_ = lean_ctor_get(v_symbols_2055_, 0);
lean_inc(v_head_2056_);
if (lean_obj_tag(v_head_2056_) == 2)
{
lean_object* v_levelParams_2057_; lean_object* v_proof_2058_; lean_object* v_numParams_2059_; lean_object* v_patterns_2060_; lean_object* v_origin_2061_; lean_object* v_kind_2062_; uint8_t v_minIndexable_2063_; lean_object* v_cnstrs_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2115_; 
v_levelParams_2057_ = lean_ctor_get(v_thm_2051_, 0);
v_proof_2058_ = lean_ctor_get(v_thm_2051_, 1);
v_numParams_2059_ = lean_ctor_get(v_thm_2051_, 2);
v_patterns_2060_ = lean_ctor_get(v_thm_2051_, 3);
v_origin_2061_ = lean_ctor_get(v_thm_2051_, 5);
v_kind_2062_ = lean_ctor_get(v_thm_2051_, 6);
v_minIndexable_2063_ = lean_ctor_get_uint8(v_thm_2051_, sizeof(void*)*8);
v_cnstrs_2064_ = lean_ctor_get(v_thm_2051_, 7);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_thm_2051_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; 
v_unused_2116_ = lean_ctor_get(v_thm_2051_, 4);
lean_dec(v_unused_2116_);
v___x_2066_ = v_thm_2051_;
v_isShared_2067_ = v_isSharedCheck_2115_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_cnstrs_2064_);
lean_inc(v_kind_2062_);
lean_inc(v_origin_2061_);
lean_inc(v_patterns_2060_);
lean_inc(v_numParams_2059_);
lean_inc(v_proof_2058_);
lean_inc(v_levelParams_2057_);
lean_dec(v_thm_2051_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2115_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v_tail_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2113_; 
v_tail_2068_ = lean_ctor_get(v_symbols_2055_, 1);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_symbols_2055_);
if (v_isSharedCheck_2113_ == 0)
{
lean_object* v_unused_2114_; 
v_unused_2114_ = lean_ctor_get(v_symbols_2055_, 0);
lean_dec(v_unused_2114_);
v___x_2070_ = v_symbols_2055_;
v_isShared_2071_ = v_isSharedCheck_2113_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_tail_2068_);
lean_dec(v_symbols_2055_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2113_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v_constName_2072_; lean_object* v_smap_2073_; lean_object* v_origins_2074_; lean_object* v_erased_2075_; lean_object* v_omap_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2112_; 
v_constName_2072_ = lean_ctor_get(v_head_2056_, 0);
lean_inc(v_constName_2072_);
lean_dec_ref_known(v_head_2056_, 1);
v_smap_2073_ = lean_ctor_get(v_s_2050_, 0);
v_origins_2074_ = lean_ctor_get(v_s_2050_, 1);
v_erased_2075_ = lean_ctor_get(v_s_2050_, 2);
v_omap_2076_ = lean_ctor_get(v_s_2050_, 3);
v_isSharedCheck_2112_ = !lean_is_exclusive(v_s_2050_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2078_ = v_s_2050_;
v_isShared_2079_ = v_isSharedCheck_2112_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_omap_2076_);
lean_inc(v_erased_2075_);
lean_inc(v_origins_2074_);
lean_inc(v_smap_2073_);
lean_dec(v_s_2050_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2112_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v_thm_2081_; 
lean_inc_ref(v_origin_2061_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 4, v_tail_2068_);
v_thm_2081_ = v___x_2066_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_levelParams_2057_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_proof_2058_);
lean_ctor_set(v_reuseFailAlloc_2111_, 2, v_numParams_2059_);
lean_ctor_set(v_reuseFailAlloc_2111_, 3, v_patterns_2060_);
lean_ctor_set(v_reuseFailAlloc_2111_, 4, v_tail_2068_);
lean_ctor_set(v_reuseFailAlloc_2111_, 5, v_origin_2061_);
lean_ctor_set(v_reuseFailAlloc_2111_, 6, v_kind_2062_);
lean_ctor_set(v_reuseFailAlloc_2111_, 7, v_cnstrs_2064_);
lean_ctor_set_uint8(v_reuseFailAlloc_2111_, sizeof(void*)*8, v_minIndexable_2063_);
v_thm_2081_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
lean_object* v___x_2082_; lean_object* v_origins_2083_; lean_object* v_erased_2084_; lean_object* v___y_2086_; lean_object* v___x_2104_; 
v___x_2082_ = lean_box(0);
lean_inc_ref(v_origin_2061_);
v_origins_2083_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_origins_2074_, v_origin_2061_, v___x_2082_);
v_erased_2084_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_erased_2075_, v_origin_2061_);
v___x_2104_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_smap_2073_, v_constName_2072_);
if (lean_obj_tag(v___x_2104_) == 1)
{
lean_object* v_val_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v_val_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_val_2105_);
lean_dec_ref_known(v___x_2104_, 1);
lean_inc_ref(v_thm_2081_);
v___x_2106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2106_, 0, v_thm_2081_);
lean_ctor_set(v___x_2106_, 1, v_val_2105_);
v___x_2107_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2073_, v_constName_2072_, v___x_2106_);
v___y_2086_ = v___x_2107_;
goto v___jp_2085_;
}
else
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_dec(v___x_2104_);
v___x_2108_ = lean_box(0);
lean_inc_ref(v_thm_2081_);
v___x_2109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2109_, 0, v_thm_2081_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2073_, v_constName_2072_, v___x_2109_);
v___y_2086_ = v___x_2110_;
goto v___jp_2085_;
}
v___jp_2085_:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_omap_2076_, v_origin_2061_);
if (lean_obj_tag(v___x_2087_) == 1)
{
lean_object* v_val_2088_; lean_object* v___x_2090_; 
v_val_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_val_2088_);
lean_dec_ref_known(v___x_2087_, 1);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v_val_2088_);
lean_ctor_set(v___x_2070_, 0, v_thm_2081_);
v___x_2090_ = v___x_2070_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_thm_2081_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_val_2088_);
v___x_2090_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2091_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2076_, v_origin_2061_, v___x_2090_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 3, v___x_2091_);
lean_ctor_set(v___x_2078_, 2, v_erased_2084_);
lean_ctor_set(v___x_2078_, 1, v_origins_2083_);
lean_ctor_set(v___x_2078_, 0, v___y_2086_);
v___x_2093_ = v___x_2078_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___y_2086_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_origins_2083_);
lean_ctor_set(v_reuseFailAlloc_2094_, 2, v_erased_2084_);
lean_ctor_set(v_reuseFailAlloc_2094_, 3, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
else
{
lean_object* v___x_2096_; lean_object* v___x_2098_; 
lean_dec(v___x_2087_);
v___x_2096_ = lean_box(0);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v___x_2096_);
lean_ctor_set(v___x_2070_, 0, v_thm_2081_);
v___x_2098_ = v___x_2070_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_thm_2081_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2076_, v_origin_2061_, v___x_2098_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 3, v___x_2099_);
lean_ctor_set(v___x_2078_, 2, v_erased_2084_);
lean_ctor_set(v___x_2078_, 1, v_origins_2083_);
lean_ctor_set(v___x_2078_, 0, v___y_2086_);
v___x_2101_ = v___x_2078_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___y_2086_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_origins_2083_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_erased_2084_);
lean_ctor_set(v_reuseFailAlloc_2102_, 3, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
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
lean_dec_ref_known(v_symbols_2055_, 2);
lean_dec(v_head_2056_);
lean_dec_ref(v_thm_2051_);
lean_dec_ref(v_s_2050_);
goto v___jp_2052_;
}
}
else
{
lean_dec(v_symbols_2055_);
lean_dec_ref(v_thm_2051_);
lean_dec_ref(v_s_2050_);
goto v___jp_2052_;
}
v___jp_2052_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3, &l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3);
v___x_2054_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0(v___x_2053_);
return v___x_2054_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1_spec__6(lean_object* v_msg_2117_){
_start:
{
lean_object* v___f_2118_; lean_object* v___f_2119_; lean_object* v___f_2120_; lean_object* v___f_2121_; lean_object* v___f_2122_; lean_object* v___f_2123_; lean_object* v___f_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___f_2118_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__0));
v___f_2119_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__1));
v___f_2120_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__2));
v___f_2121_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__3));
v___f_2122_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__4));
v___f_2123_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__5));
v___f_2124_ = ((lean_object*)(l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__6));
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___f_2118_);
lean_ctor_set(v___x_2125_, 1, v___f_2119_);
v___x_2126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
lean_ctor_set(v___x_2126_, 1, v___f_2120_);
lean_ctor_set(v___x_2126_, 2, v___f_2121_);
lean_ctor_set(v___x_2126_, 3, v___f_2122_);
lean_ctor_set(v___x_2126_, 4, v___f_2123_);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v___f_2124_);
v___x_2128_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7, &l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7_once, _init_l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__0___closed__7);
v___x_2129_ = l_instInhabitedOfMonad___redArg(v___x_2127_, v___x_2128_);
v___x_2130_ = lean_panic_fn_borrowed(v___x_2129_, v_msg_2117_);
lean_dec(v___x_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1(lean_object* v_s_2131_, lean_object* v_thm_2132_){
_start:
{
lean_object* v_symbols_2136_; 
v_symbols_2136_ = lean_ctor_get(v_thm_2132_, 2);
lean_inc(v_symbols_2136_);
if (lean_obj_tag(v_symbols_2136_) == 1)
{
lean_object* v_head_2137_; 
v_head_2137_ = lean_ctor_get(v_symbols_2136_, 0);
lean_inc(v_head_2137_);
if (lean_obj_tag(v_head_2137_) == 2)
{
lean_object* v_levelParams_2138_; lean_object* v_proof_2139_; lean_object* v_origin_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2191_; 
v_levelParams_2138_ = lean_ctor_get(v_thm_2132_, 0);
v_proof_2139_ = lean_ctor_get(v_thm_2132_, 1);
v_origin_2140_ = lean_ctor_get(v_thm_2132_, 3);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_thm_2132_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; 
v_unused_2192_ = lean_ctor_get(v_thm_2132_, 2);
lean_dec(v_unused_2192_);
v___x_2142_ = v_thm_2132_;
v_isShared_2143_ = v_isSharedCheck_2191_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_origin_2140_);
lean_inc(v_proof_2139_);
lean_inc(v_levelParams_2138_);
lean_dec(v_thm_2132_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2191_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v_tail_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2189_; 
v_tail_2144_ = lean_ctor_get(v_symbols_2136_, 1);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_symbols_2136_);
if (v_isSharedCheck_2189_ == 0)
{
lean_object* v_unused_2190_; 
v_unused_2190_ = lean_ctor_get(v_symbols_2136_, 0);
lean_dec(v_unused_2190_);
v___x_2146_ = v_symbols_2136_;
v_isShared_2147_ = v_isSharedCheck_2189_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_tail_2144_);
lean_dec(v_symbols_2136_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2189_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v_constName_2148_; lean_object* v_smap_2149_; lean_object* v_origins_2150_; lean_object* v_erased_2151_; lean_object* v_omap_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2188_; 
v_constName_2148_ = lean_ctor_get(v_head_2137_, 0);
lean_inc(v_constName_2148_);
lean_dec_ref_known(v_head_2137_, 1);
v_smap_2149_ = lean_ctor_get(v_s_2131_, 0);
v_origins_2150_ = lean_ctor_get(v_s_2131_, 1);
v_erased_2151_ = lean_ctor_get(v_s_2131_, 2);
v_omap_2152_ = lean_ctor_get(v_s_2131_, 3);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_s_2131_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2154_ = v_s_2131_;
v_isShared_2155_ = v_isSharedCheck_2188_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_omap_2152_);
lean_inc(v_erased_2151_);
lean_inc(v_origins_2150_);
lean_inc(v_smap_2149_);
lean_dec(v_s_2131_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2188_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v_thm_2157_; 
lean_inc_ref(v_origin_2140_);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 2, v_tail_2144_);
v_thm_2157_ = v___x_2142_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_levelParams_2138_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_proof_2139_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_tail_2144_);
lean_ctor_set(v_reuseFailAlloc_2187_, 3, v_origin_2140_);
v_thm_2157_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v___x_2158_; lean_object* v_origins_2159_; lean_object* v_erased_2160_; lean_object* v___y_2162_; lean_object* v___x_2180_; 
v___x_2158_ = lean_box(0);
lean_inc_ref(v_origin_2140_);
v_origins_2159_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_origins_2150_, v_origin_2140_, v___x_2158_);
v_erased_2160_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_erased_2151_, v_origin_2140_);
v___x_2180_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_smap_2149_, v_constName_2148_);
if (lean_obj_tag(v___x_2180_) == 1)
{
lean_object* v_val_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_val_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_val_2181_);
lean_dec_ref_known(v___x_2180_, 1);
lean_inc_ref(v_thm_2157_);
v___x_2182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2182_, 0, v_thm_2157_);
lean_ctor_set(v___x_2182_, 1, v_val_2181_);
v___x_2183_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2149_, v_constName_2148_, v___x_2182_);
v___y_2162_ = v___x_2183_;
goto v___jp_2161_;
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
lean_dec(v___x_2180_);
v___x_2184_ = lean_box(0);
lean_inc_ref(v_thm_2157_);
v___x_2185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2185_, 0, v_thm_2157_);
lean_ctor_set(v___x_2185_, 1, v___x_2184_);
v___x_2186_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_smap_2149_, v_constName_2148_, v___x_2185_);
v___y_2162_ = v___x_2186_;
goto v___jp_2161_;
}
v___jp_2161_:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_omap_2152_, v_origin_2140_);
if (lean_obj_tag(v___x_2163_) == 1)
{
lean_object* v_val_2164_; lean_object* v___x_2166_; 
v_val_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_val_2164_);
lean_dec_ref_known(v___x_2163_, 1);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 1, v_val_2164_);
lean_ctor_set(v___x_2146_, 0, v_thm_2157_);
v___x_2166_ = v___x_2146_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_thm_2157_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_val_2164_);
v___x_2166_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v___x_2167_; lean_object* v___x_2169_; 
v___x_2167_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2152_, v_origin_2140_, v___x_2166_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 3, v___x_2167_);
lean_ctor_set(v___x_2154_, 2, v_erased_2160_);
lean_ctor_set(v___x_2154_, 1, v_origins_2159_);
lean_ctor_set(v___x_2154_, 0, v___y_2162_);
v___x_2169_ = v___x_2154_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___y_2162_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_origins_2159_);
lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_erased_2160_);
lean_ctor_set(v_reuseFailAlloc_2170_, 3, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
lean_dec(v___x_2163_);
v___x_2172_ = lean_box(0);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 1, v___x_2172_);
lean_ctor_set(v___x_2146_, 0, v_thm_2157_);
v___x_2174_ = v___x_2146_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_thm_2157_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; lean_object* v___x_2177_; 
v___x_2175_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_omap_2152_, v_origin_2140_, v___x_2174_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 3, v___x_2175_);
lean_ctor_set(v___x_2154_, 2, v_erased_2160_);
lean_ctor_set(v___x_2154_, 1, v_origins_2159_);
lean_ctor_set(v___x_2154_, 0, v___y_2162_);
v___x_2177_ = v___x_2154_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___y_2162_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_origins_2159_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v_erased_2160_);
lean_ctor_set(v_reuseFailAlloc_2178_, 3, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
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
lean_dec(v_head_2137_);
lean_dec_ref_known(v_symbols_2136_, 2);
lean_dec_ref(v_thm_2132_);
lean_dec_ref(v_s_2131_);
goto v___jp_2133_;
}
}
else
{
lean_dec(v_symbols_2136_);
lean_dec_ref(v_thm_2132_);
lean_dec_ref(v_s_2131_);
goto v___jp_2133_;
}
v___jp_2133_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = lean_obj_once(&l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3, &l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3_once, _init_l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__3);
v___x_2135_ = l_panic___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1_spec__6(v___x_2134_);
return v___x_2135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ExtensionState_addEntry(lean_object* v_s_2193_, lean_object* v_e_2194_){
_start:
{
switch(lean_obj_tag(v_e_2194_))
{
case 0:
{
lean_object* v_declName_2195_; lean_object* v_casesTypes_2196_; lean_object* v_extThms_2197_; lean_object* v_funCC_2198_; lean_object* v_ematch_2199_; lean_object* v_inj_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2209_; 
v_declName_2195_ = lean_ctor_get(v_e_2194_, 0);
lean_inc(v_declName_2195_);
lean_dec_ref_known(v_e_2194_, 1);
v_casesTypes_2196_ = lean_ctor_get(v_s_2193_, 0);
v_extThms_2197_ = lean_ctor_get(v_s_2193_, 1);
v_funCC_2198_ = lean_ctor_get(v_s_2193_, 2);
v_ematch_2199_ = lean_ctor_get(v_s_2193_, 3);
v_inj_2200_ = lean_ctor_get(v_s_2193_, 4);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_s_2193_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2202_ = v_s_2193_;
v_isShared_2203_ = v_isSharedCheck_2209_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_inj_2200_);
lean_inc(v_ematch_2199_);
lean_inc(v_funCC_2198_);
lean_inc(v_extThms_2197_);
lean_inc(v_casesTypes_2196_);
lean_dec(v_s_2193_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2209_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2204_ = lean_box(0);
v___x_2205_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_extThms_2197_, v_declName_2195_, v___x_2204_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 1, v___x_2205_);
v___x_2207_ = v___x_2202_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_casesTypes_2196_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_funCC_2198_);
lean_ctor_set(v_reuseFailAlloc_2208_, 3, v_ematch_2199_);
lean_ctor_set(v_reuseFailAlloc_2208_, 4, v_inj_2200_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
case 1:
{
lean_object* v_declName_2210_; lean_object* v_casesTypes_2211_; lean_object* v_extThms_2212_; lean_object* v_funCC_2213_; lean_object* v_ematch_2214_; lean_object* v_inj_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2223_; 
v_declName_2210_ = lean_ctor_get(v_e_2194_, 0);
lean_inc(v_declName_2210_);
lean_dec_ref_known(v_e_2194_, 1);
v_casesTypes_2211_ = lean_ctor_get(v_s_2193_, 0);
v_extThms_2212_ = lean_ctor_get(v_s_2193_, 1);
v_funCC_2213_ = lean_ctor_get(v_s_2193_, 2);
v_ematch_2214_ = lean_ctor_get(v_s_2193_, 3);
v_inj_2215_ = lean_ctor_get(v_s_2193_, 4);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_s_2193_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2217_ = v_s_2193_;
v_isShared_2218_ = v_isSharedCheck_2223_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_inj_2215_);
lean_inc(v_ematch_2214_);
lean_inc(v_funCC_2213_);
lean_inc(v_extThms_2212_);
lean_inc(v_casesTypes_2211_);
lean_dec(v_s_2193_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2223_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2219_ = l_Lean_NameSet_insert(v_funCC_2213_, v_declName_2210_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 2, v___x_2219_);
v___x_2221_ = v___x_2217_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_casesTypes_2211_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_extThms_2212_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2222_, 3, v_ematch_2214_);
lean_ctor_set(v_reuseFailAlloc_2222_, 4, v_inj_2215_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
case 2:
{
lean_object* v_declName_2224_; uint8_t v_eager_2225_; lean_object* v_casesTypes_2226_; lean_object* v_extThms_2227_; lean_object* v_funCC_2228_; lean_object* v_ematch_2229_; lean_object* v_inj_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2239_; 
v_declName_2224_ = lean_ctor_get(v_e_2194_, 0);
lean_inc(v_declName_2224_);
v_eager_2225_ = lean_ctor_get_uint8(v_e_2194_, sizeof(void*)*1);
lean_dec_ref_known(v_e_2194_, 1);
v_casesTypes_2226_ = lean_ctor_get(v_s_2193_, 0);
v_extThms_2227_ = lean_ctor_get(v_s_2193_, 1);
v_funCC_2228_ = lean_ctor_get(v_s_2193_, 2);
v_ematch_2229_ = lean_ctor_get(v_s_2193_, 3);
v_inj_2230_ = lean_ctor_get(v_s_2193_, 4);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_s_2193_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2232_ = v_s_2193_;
v_isShared_2233_ = v_isSharedCheck_2239_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_inj_2230_);
lean_inc(v_ematch_2229_);
lean_inc(v_funCC_2228_);
lean_inc(v_extThms_2227_);
lean_inc(v_casesTypes_2226_);
lean_dec(v_s_2193_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2239_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2237_; 
v___x_2234_ = lean_box(v_eager_2225_);
v___x_2235_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_CasesTypes_insert_spec__0___redArg(v_casesTypes_2226_, v_declName_2224_, v___x_2234_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2235_);
v___x_2237_ = v___x_2232_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2235_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_extThms_2227_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_funCC_2228_);
lean_ctor_set(v_reuseFailAlloc_2238_, 3, v_ematch_2229_);
lean_ctor_set(v_reuseFailAlloc_2238_, 4, v_inj_2230_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
case 3:
{
lean_object* v_thm_2240_; lean_object* v_casesTypes_2241_; lean_object* v_extThms_2242_; lean_object* v_funCC_2243_; lean_object* v_ematch_2244_; lean_object* v_inj_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2253_; 
v_thm_2240_ = lean_ctor_get(v_e_2194_, 0);
lean_inc_ref(v_thm_2240_);
lean_dec_ref_known(v_e_2194_, 1);
v_casesTypes_2241_ = lean_ctor_get(v_s_2193_, 0);
v_extThms_2242_ = lean_ctor_get(v_s_2193_, 1);
v_funCC_2243_ = lean_ctor_get(v_s_2193_, 2);
v_ematch_2244_ = lean_ctor_get(v_s_2193_, 3);
v_inj_2245_ = lean_ctor_get(v_s_2193_, 4);
v_isSharedCheck_2253_ = !lean_is_exclusive(v_s_2193_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2247_ = v_s_2193_;
v_isShared_2248_ = v_isSharedCheck_2253_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_inj_2245_);
lean_inc(v_ematch_2244_);
lean_inc(v_funCC_2243_);
lean_inc(v_extThms_2242_);
lean_inc(v_casesTypes_2241_);
lean_dec(v_s_2193_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2253_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2249_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0(v_ematch_2244_, v_thm_2240_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 3, v___x_2249_);
v___x_2251_ = v___x_2247_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_casesTypes_2241_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_extThms_2242_);
lean_ctor_set(v_reuseFailAlloc_2252_, 2, v_funCC_2243_);
lean_ctor_set(v_reuseFailAlloc_2252_, 3, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2252_, 4, v_inj_2245_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
default: 
{
lean_object* v_thm_2254_; lean_object* v_casesTypes_2255_; lean_object* v_extThms_2256_; lean_object* v_funCC_2257_; lean_object* v_ematch_2258_; lean_object* v_inj_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2267_; 
v_thm_2254_ = lean_ctor_get(v_e_2194_, 0);
lean_inc_ref(v_thm_2254_);
lean_dec_ref_known(v_e_2194_, 1);
v_casesTypes_2255_ = lean_ctor_get(v_s_2193_, 0);
v_extThms_2256_ = lean_ctor_get(v_s_2193_, 1);
v_funCC_2257_ = lean_ctor_get(v_s_2193_, 2);
v_ematch_2258_ = lean_ctor_get(v_s_2193_, 3);
v_inj_2259_ = lean_ctor_get(v_s_2193_, 4);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_s_2193_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2261_ = v_s_2193_;
v_isShared_2262_ = v_isSharedCheck_2267_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_inj_2259_);
lean_inc(v_ematch_2258_);
lean_inc(v_funCC_2257_);
lean_inc(v_extThms_2256_);
lean_inc(v_casesTypes_2255_);
lean_dec(v_s_2193_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2267_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2263_; lean_object* v___x_2265_; 
v___x_2263_ = l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__1(v_inj_2259_, v_thm_2254_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 4, v___x_2263_);
v___x_2265_ = v___x_2261_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_casesTypes_2255_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_extThms_2256_);
lean_ctor_set(v_reuseFailAlloc_2266_, 2, v_funCC_2257_);
lean_ctor_set(v_reuseFailAlloc_2266_, 3, v_ematch_2258_);
lean_ctor_set(v_reuseFailAlloc_2266_, 4, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1(lean_object* v_00_u03b2_2268_, lean_object* v_x_2269_, lean_object* v_x_2270_, lean_object* v_x_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1___redArg(v_x_2269_, v_x_2270_, v_x_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2(lean_object* v_00_u03b2_2273_, lean_object* v_x_2274_, lean_object* v_x_2275_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___redArg(v_x_2274_, v_x_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2277_, lean_object* v_x_2278_, lean_object* v_x_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2(v_00_u03b2_2277_, v_x_2278_, v_x_2279_);
lean_dec_ref(v_x_2279_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3(lean_object* v_00_u03b2_2281_, lean_object* v_x_2282_, lean_object* v_x_2283_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___redArg(v_x_2282_, v_x_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2285_, lean_object* v_x_2286_, lean_object* v_x_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3(v_00_u03b2_2285_, v_x_2286_, v_x_2287_);
lean_dec_ref(v_x_2287_);
lean_dec_ref(v_x_2286_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4(lean_object* v_00_u03b2_2289_, lean_object* v_x_2290_, lean_object* v_x_2291_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___redArg(v_x_2290_, v_x_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4___boxed(lean_object* v_00_u03b2_2293_, lean_object* v_x_2294_, lean_object* v_x_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4(v_00_u03b2_2293_, v_x_2294_, v_x_2295_);
lean_dec(v_x_2295_);
lean_dec_ref(v_x_2294_);
return v_res_2296_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2297_, lean_object* v_x_2298_, size_t v_x_2299_, size_t v_x_2300_, lean_object* v_x_2301_, lean_object* v_x_2302_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___redArg(v_x_2298_, v_x_2299_, v_x_2300_, v_x_2301_, v_x_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2298_ = stack[1].m_obj;
size_t v_x_2299_ = stack[2].m_num;
size_t v_x_2300_ = stack[3].m_num;
lean_object* v_x_2301_ = stack[4].m_obj;
lean_object* v_x_2302_ = stack[5].m_obj;
lean_object* v_res_2304_;
v_res_2304_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(lean_box(0), v_x_2298_, v_x_2299_, v_x_2300_, v_x_2301_, v_x_2302_);
stack->m_obj
 = v_res_2304_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2305_, lean_object* v_x_2306_, lean_object* v_x_2307_, lean_object* v_x_2308_, lean_object* v_x_2309_, lean_object* v_x_2310_){
_start:
{
size_t v_x_2786__boxed_2311_; size_t v_x_2787__boxed_2312_; lean_object* v_res_2313_; 
v_x_2786__boxed_2311_ = lean_unbox_usize(v_x_2307_);
lean_dec(v_x_2307_);
v_x_2787__boxed_2312_ = lean_unbox_usize(v_x_2308_);
lean_dec(v_x_2308_);
v_res_2313_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2(v_00_u03b2_2305_, v_x_2306_, v_x_2786__boxed_2311_, v_x_2787__boxed_2312_, v_x_2309_, v_x_2310_);
return v_res_2313_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_2314_, lean_object* v_x_2315_, size_t v_x_2316_, lean_object* v_x_2317_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___redArg(v_x_2315_, v_x_2316_, v_x_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2315_ = stack[1].m_obj;
size_t v_x_2316_ = stack[2].m_num;
lean_object* v_x_2317_ = stack[3].m_obj;
lean_object* v_res_2319_;
v_res_2319_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(lean_box(0), v_x_2315_, v_x_2316_, v_x_2317_);
stack->m_obj
 = v_res_2319_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2320_, lean_object* v_x_2321_, lean_object* v_x_2322_, lean_object* v_x_2323_){
_start:
{
size_t v_x_2814__boxed_2324_; lean_object* v_res_2325_; 
v_x_2814__boxed_2324_ = lean_unbox_usize(v_x_2322_);
lean_dec(v_x_2322_);
v_res_2325_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__2_spec__4(v_00_u03b2_2320_, v_x_2321_, v_x_2814__boxed_2324_, v_x_2323_);
lean_dec_ref(v_x_2323_);
return v_res_2325_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(lean_object* v_00_u03b2_2326_, lean_object* v_x_2327_, size_t v_x_2328_, lean_object* v_x_2329_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___redArg(v_x_2327_, v_x_2328_, v_x_2329_);
return v___x_2330_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2327_ = stack[1].m_obj;
size_t v_x_2328_ = stack[2].m_num;
lean_object* v_x_2329_ = stack[3].m_obj;
lean_object* v_res_2331_;
v_res_2331_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(lean_box(0), v_x_2327_, v_x_2328_, v_x_2329_);
stack->m_obj
 = v_res_2331_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2332_, lean_object* v_x_2333_, lean_object* v_x_2334_, lean_object* v_x_2335_){
_start:
{
size_t v_x_2832__boxed_2336_; lean_object* v_res_2337_; 
v_x_2832__boxed_2336_ = lean_unbox_usize(v_x_2334_);
lean_dec(v_x_2334_);
v_res_2337_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6(v_00_u03b2_2332_, v_x_2333_, v_x_2832__boxed_2336_, v_x_2335_);
lean_dec_ref(v_x_2335_);
lean_dec_ref(v_x_2333_);
return v_res_2337_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(lean_object* v_00_u03b2_2338_, lean_object* v_x_2339_, size_t v_x_2340_, lean_object* v_x_2341_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___redArg(v_x_2339_, v_x_2340_, v_x_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2339_ = stack[1].m_obj;
size_t v_x_2340_ = stack[2].m_num;
lean_object* v_x_2341_ = stack[3].m_obj;
lean_object* v_res_2343_;
v_res_2343_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(lean_box(0), v_x_2339_, v_x_2340_, v_x_2341_);
stack->m_obj
 = v_res_2343_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8___boxed(lean_object* v_00_u03b2_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_, lean_object* v_x_2347_){
_start:
{
size_t v_x_2850__boxed_2348_; lean_object* v_res_2349_; 
v_x_2850__boxed_2348_ = lean_unbox_usize(v_x_2346_);
lean_dec(v_x_2346_);
v_res_2349_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8(v_00_u03b2_2344_, v_x_2345_, v_x_2850__boxed_2348_, v_x_2347_);
lean_dec(v_x_2347_);
lean_dec_ref(v_x_2345_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2350_, lean_object* v_n_2351_, lean_object* v_k_2352_, lean_object* v_v_2353_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5___redArg(v_n_2351_, v_k_2352_, v_v_2353_);
return v___x_2354_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2355_, size_t v_depth_2356_, lean_object* v_keys_2357_, lean_object* v_vals_2358_, lean_object* v_heq_2359_, lean_object* v_i_2360_, lean_object* v_entries_2361_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___redArg(v_depth_2356_, v_keys_2357_, v_vals_2358_, v_i_2360_, v_entries_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2356_ = stack[1].m_num;
lean_object* v_keys_2357_ = stack[2].m_obj;
lean_object* v_vals_2358_ = stack[3].m_obj;
lean_object* v_i_2360_ = stack[5].m_obj;
lean_object* v_entries_2361_ = stack[6].m_obj;
lean_object* v_res_2363_;
v_res_2363_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(lean_box(0), v_depth_2356_, v_keys_2357_, v_vals_2358_, lean_box(0), v_i_2360_, v_entries_2361_);
stack->m_obj
 = v_res_2363_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2364_, lean_object* v_depth_2365_, lean_object* v_keys_2366_, lean_object* v_vals_2367_, lean_object* v_heq_2368_, lean_object* v_i_2369_, lean_object* v_entries_2370_){
_start:
{
size_t v_depth_boxed_2371_; lean_object* v_res_2372_; 
v_depth_boxed_2371_ = lean_unbox_usize(v_depth_2365_);
lean_dec(v_depth_2365_);
v_res_2372_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__6(v_00_u03b2_2364_, v_depth_boxed_2371_, v_keys_2366_, v_vals_2367_, v_heq_2368_, v_i_2369_, v_entries_2370_);
lean_dec_ref(v_vals_2367_);
lean_dec_ref(v_keys_2366_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12(lean_object* v_00_u03b2_2373_, lean_object* v_keys_2374_, lean_object* v_vals_2375_, lean_object* v_heq_2376_, lean_object* v_i_2377_, lean_object* v_k_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___redArg(v_keys_2374_, v_vals_2375_, v_i_2377_, v_k_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12___boxed(lean_object* v_00_u03b2_2380_, lean_object* v_keys_2381_, lean_object* v_vals_2382_, lean_object* v_heq_2383_, lean_object* v_i_2384_, lean_object* v_k_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__3_spec__6_spec__12(v_00_u03b2_2380_, v_keys_2381_, v_vals_2382_, v_heq_2383_, v_i_2384_, v_k_2385_);
lean_dec_ref(v_k_2385_);
lean_dec_ref(v_vals_2382_);
lean_dec_ref(v_keys_2381_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15(lean_object* v_00_u03b2_2387_, lean_object* v_keys_2388_, lean_object* v_vals_2389_, lean_object* v_heq_2390_, lean_object* v_i_2391_, lean_object* v_k_2392_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___redArg(v_keys_2388_, v_vals_2389_, v_i_2391_, v_k_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15___boxed(lean_object* v_00_u03b2_2394_, lean_object* v_keys_2395_, lean_object* v_vals_2396_, lean_object* v_heq_2397_, lean_object* v_i_2398_, lean_object* v_k_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__4_spec__8_spec__15(v_00_u03b2_2394_, v_keys_2395_, v_vals_2396_, v_heq_2397_, v_i_2398_, v_k_2399_);
lean_dec(v_k_2399_);
lean_dec_ref(v_vals_2396_);
lean_dec_ref(v_keys_2395_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_2401_, lean_object* v_x_2402_, lean_object* v_x_2403_, lean_object* v_x_2404_, lean_object* v_x_2405_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0_spec__1_spec__2_spec__5_spec__9___redArg(v_x_2402_, v_x_2403_, v_x_2404_, v_x_2405_);
return v___x_2406_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__12(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__10));
v___x_2434_ = l_Lean_mkAtom(v___x_2433_);
return v___x_2434_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2435_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__12, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__12_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__12);
v___x_2436_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2437_ = lean_array_push(v___x_2436_, v___x_2435_);
return v___x_2437_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__17));
v___x_2447_ = l_Lean_mkAtom(v___x_2446_);
return v___x_2447_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2448_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__18, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__18_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__18);
v___x_2449_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2450_ = lean_array_push(v___x_2449_, v___x_2448_);
return v___x_2450_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__20(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2451_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__19, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__19_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__19);
v___x_2452_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__16));
v___x_2453_ = lean_box(2);
v___x_2454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2453_);
lean_ctor_set(v___x_2454_, 1, v___x_2452_);
lean_ctor_set(v___x_2454_, 2, v___x_2451_);
return v___x_2454_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__21(void){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__20, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__20_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__20);
v___x_2456_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__13, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__13_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__13);
v___x_2457_ = lean_array_push(v___x_2456_, v___x_2455_);
return v___x_2457_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__22(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2458_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__21, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__21_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__21);
v___x_2459_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__11));
v___x_2460_ = lean_box(2);
v___x_2461_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
lean_ctor_set(v___x_2461_, 1, v___x_2459_);
lean_ctor_set(v___x_2461_, 2, v___x_2458_);
return v___x_2461_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2462_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__22, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__22_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__22);
v___x_2463_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2464_ = lean_array_push(v___x_2463_, v___x_2462_);
return v___x_2464_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2465_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__23, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__23_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__23);
v___x_2466_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__9));
v___x_2467_ = lean_box(2);
v___x_2468_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
lean_ctor_set(v___x_2468_, 1, v___x_2466_);
lean_ctor_set(v___x_2468_, 2, v___x_2465_);
return v___x_2468_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__25(void){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2469_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__24, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__24_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__24);
v___x_2470_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2471_ = lean_array_push(v___x_2470_, v___x_2469_);
return v___x_2471_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__26(void){
_start:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2472_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__25, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__25_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__25);
v___x_2473_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__7));
v___x_2474_ = lean_box(2);
v___x_2475_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
lean_ctor_set(v___x_2475_, 1, v___x_2473_);
lean_ctor_set(v___x_2475_, 2, v___x_2472_);
return v___x_2475_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__27(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__26, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__26_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__26);
v___x_2477_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__5));
v___x_2478_ = lean_array_push(v___x_2477_, v___x_2476_);
return v___x_2478_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__28(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2479_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__27, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__27_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__27);
v___x_2480_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___auto__1___closed__4));
v___x_2481_ = lean_box(2);
v___x_2482_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
lean_ctor_set(v___x_2482_, 1, v___x_2480_);
lean_ctor_set(v___x_2482_, 2, v___x_2479_);
return v___x_2482_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___auto__1(void){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___auto__1___closed__28, &l_Lean_Meta_Grind_mkExtension___auto__1___closed__28_once, _init_l_Lean_Meta_Grind_mkExtension___auto__1___closed__28);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(lean_object* v_msg_2484_){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = lean_box(0);
v___x_2486_ = lean_panic_fn_borrowed(v___x_2485_, v_msg_2484_);
return v___x_2486_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2489_ = ((lean_object*)(l_Lean_Meta_Grind_Theorems_insert___at___00Lean_Meta_Grind_ExtensionState_addEntry_spec__0___closed__2));
v___x_2490_ = lean_unsigned_to_nat(17u);
v___x_2491_ = lean_unsigned_to_nat(203u);
v___x_2492_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___lam__0___closed__1));
v___x_2493_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___lam__0___closed__0));
v___x_2494_ = l_mkPanicMessageWithDecl(v___x_2493_, v___x_2492_, v___x_2491_, v___x_2490_, v___x_2489_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__0(lean_object* v_x_2495_, lean_object* v_e_2496_){
_start:
{
lean_object* v___y_2498_; 
switch(lean_obj_tag(v_e_2496_))
{
case 3:
{
lean_object* v_thm_2505_; lean_object* v_origin_2506_; 
v_thm_2505_ = lean_ctor_get(v_e_2496_, 0);
v_origin_2506_ = lean_ctor_get(v_thm_2505_, 5);
if (lean_obj_tag(v_origin_2506_) == 0)
{
lean_object* v_declName_2507_; 
v_declName_2507_ = lean_ctor_get(v_origin_2506_, 0);
lean_inc(v_declName_2507_);
v___y_2498_ = v_declName_2507_;
goto v___jp_2497_;
}
else
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___lam__0___closed__2, &l_Lean_Meta_Grind_mkExtension___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2);
v___x_2509_ = l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(v___x_2508_);
v___y_2498_ = v___x_2509_;
goto v___jp_2497_;
}
}
case 4:
{
lean_object* v_thm_2510_; lean_object* v_origin_2511_; 
v_thm_2510_ = lean_ctor_get(v_e_2496_, 0);
v_origin_2511_ = lean_ctor_get(v_thm_2510_, 3);
if (lean_obj_tag(v_origin_2511_) == 0)
{
lean_object* v_declName_2512_; 
v_declName_2512_ = lean_ctor_get(v_origin_2511_, 0);
lean_inc(v_declName_2512_);
v___y_2498_ = v_declName_2512_;
goto v___jp_2497_;
}
else
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = lean_obj_once(&l_Lean_Meta_Grind_mkExtension___lam__0___closed__2, &l_Lean_Meta_Grind_mkExtension___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_mkExtension___lam__0___closed__2);
v___x_2514_ = l_panic___at___00Lean_Meta_Grind_mkExtension_spec__0(v___x_2513_);
v___y_2498_ = v___x_2514_;
goto v___jp_2497_;
}
}
default: 
{
lean_object* v_declName_2515_; 
v_declName_2515_ = lean_ctor_get(v_e_2496_, 0);
lean_inc(v_declName_2515_);
v___y_2498_ = v_declName_2515_;
goto v___jp_2497_;
}
}
v___jp_2497_:
{
uint8_t v___x_2499_; 
v___x_2499_ = l_Lean_isPrivateName(v___y_2498_);
lean_dec(v___y_2498_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2500_, 0, v_e_2496_);
lean_inc_ref_n(v___x_2500_, 2);
v___x_2501_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
lean_ctor_set(v___x_2501_, 2, v___x_2500_);
return v___x_2501_;
}
else
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = lean_box(0);
v___x_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2503_, 0, v_e_2496_);
v___x_2504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2502_);
lean_ctor_set(v___x_2504_, 1, v___x_2502_);
lean_ctor_set(v___x_2504_, 2, v___x_2503_);
return v___x_2504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__0___boxed(lean_object* v_x_2516_, lean_object* v_e_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Lean_Meta_Grind_mkExtension___lam__0(v_x_2516_, v_e_2517_);
lean_dec_ref(v_x_2516_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__1(lean_object* v___y_2519_){
_start:
{
lean_inc_ref(v___y_2519_);
return v___y_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___lam__1___boxed(lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_Meta_Grind_mkExtension___lam__1(v___y_2520_);
lean_dec_ref(v___y_2520_);
return v_res_2521_;
}
}
lean_object* l_Lean_Meta_Grind_mkExtension(lean_object* v_name_2525_){
_start:
{
lean_object* v___f_2527_; lean_object* v___f_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___f_2527_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__0));
v___f_2528_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__1));
v___x_2529_ = ((lean_object*)(l_Lean_Meta_Grind_mkExtension___closed__2));
v___x_2530_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1, &l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1_once, _init_l_Lean_Meta_Grind_instInhabitedExtensionState_default___closed__1);
v___x_2531_ = 0;
v___x_2532_ = lean_box(0);
v___x_2533_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_2533_, 0, v_name_2525_);
lean_ctor_set(v___x_2533_, 1, v___x_2529_);
lean_ctor_set(v___x_2533_, 2, v___x_2530_);
lean_ctor_set(v___x_2533_, 3, v___f_2528_);
lean_ctor_set(v___x_2533_, 4, v___f_2527_);
lean_ctor_set(v___x_2533_, 5, v___x_2532_);
lean_ctor_set_uint8(v___x_2533_, sizeof(void*)*6, v___x_2531_);
lean_ctor_set_uint8(v___x_2533_, sizeof(void*)*6 + 1, v___x_2531_);
v___x_2534_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2533_);
return v___x_2534_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_mkExtension_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2525_ = stack[0].m_obj;
lean_object* v_res_2535_;
v_res_2535_ = l_Lean_Meta_Grind_mkExtension(v_name_2525_);
stack->m_obj
 = v_res_2535_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkExtension___boxed(lean_object* v_name_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_Meta_Grind_mkExtension(v_name_2536_);
return v_res_2538_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = lean_obj_once(&l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0, &l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0_once, _init_l_Lean_Meta_Grind_instInhabitedCasesTypes_default___closed__0);
v___x_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
return v___x_2540_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2541_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2542_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0);
v___x_2543_ = lean_unsigned_to_nat(0u);
v___x_2544_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
lean_ctor_set(v___x_2544_, 2, v___x_2543_);
lean_ctor_set(v___x_2544_, 3, v___x_2543_);
lean_ctor_set(v___x_2544_, 4, v___x_2542_);
lean_ctor_set(v___x_2544_, 5, v___x_2542_);
lean_ctor_set(v___x_2544_, 6, v___x_2542_);
lean_ctor_set(v___x_2544_, 7, v___x_2542_);
lean_ctor_set(v___x_2544_, 8, v___x_2542_);
lean_ctor_set(v___x_2544_, 9, v___x_2542_);
lean_ctor_set(v___x_2544_, 10, v___x_2542_);
lean_ctor_set(v___x_2544_, 11, v___x_2541_);
return v___x_2544_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_unsigned_to_nat(32u);
v___x_2546_ = lean_mk_empty_array_with_capacity(v___x_2545_);
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
return v___x_2547_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2548_ = ((size_t)5ULL);
v___x_2549_ = lean_unsigned_to_nat(0u);
v___x_2550_ = lean_unsigned_to_nat(32u);
v___x_2551_ = lean_mk_empty_array_with_capacity(v___x_2550_);
v___x_2552_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__2);
v___x_2553_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2553_, 0, v___x_2552_);
lean_ctor_set(v___x_2553_, 1, v___x_2551_);
lean_ctor_set(v___x_2553_, 2, v___x_2549_);
lean_ctor_set(v___x_2553_, 3, v___x_2549_);
lean_ctor_set_usize(v___x_2553_, 4, v___x_2548_);
return v___x_2553_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2554_ = lean_box(1);
v___x_2555_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__3);
v___x_2556_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__0);
v___x_2557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
lean_ctor_set(v___x_2557_, 1, v___x_2555_);
lean_ctor_set(v___x_2557_, 2, v___x_2554_);
return v___x_2557_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(lean_object* v_msgData_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v___x_2562_; lean_object* v_toCold_2563_; lean_object* v_env_2564_; lean_object* v_options_2565_; uint8_t v___x_2566_; lean_object* v_env_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2562_ = lean_st_ref_get(v___y_2560_);
v_toCold_2563_ = lean_ctor_get(v___y_2559_, 0);
v_env_2564_ = lean_ctor_get(v___x_2562_, 0);
lean_inc_ref(v_env_2564_);
lean_dec(v___x_2562_);
v_options_2565_ = lean_ctor_get(v_toCold_2563_, 2);
v___x_2566_ = 0;
v_env_2567_ = l_Lean_Environment_setRecordingDeps(v_env_2564_, v___x_2566_);
v___x_2568_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__1);
v___x_2569_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___closed__4);
lean_inc_ref(v_options_2565_);
v___x_2570_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2570_, 0, v_env_2567_);
lean_ctor_set(v___x_2570_, 1, v___x_2568_);
lean_ctor_set(v___x_2570_, 2, v___x_2569_);
lean_ctor_set(v___x_2570_, 3, v_options_2565_);
v___x_2571_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
lean_ctor_set(v___x_2571_, 1, v_msgData_2558_);
v___x_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2558_ = stack[0].m_obj;
lean_object* v___y_2559_ = stack[1].m_obj;
lean_object* v___y_2560_ = stack[2].m_obj;
lean_object* v_res_2573_;
v_res_2573_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(v_msgData_2558_, v___y_2559_, v___y_2560_);
stack->m_obj
 = v_res_2573_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0___boxed(lean_object* v_msgData_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(v_msgData_2574_, v___y_2575_, v___y_2576_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
return v_res_2578_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(lean_object* v_msg_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_ref_2583_; lean_object* v___x_2584_; lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2593_; 
v_ref_2583_ = lean_ctor_get(v___y_2580_, 2);
v___x_2584_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_spec__0(v_msg_2579_, v___y_2580_, v___y_2581_);
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2593_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2593_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2589_; lean_object* v___x_2591_; 
lean_inc(v_ref_2583_);
v___x_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2589_, 0, v_ref_2583_);
lean_ctor_set(v___x_2589_, 1, v_a_2585_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set_tag(v___x_2587_, 1);
lean_ctor_set(v___x_2587_, 0, v___x_2589_);
v___x_2591_ = v___x_2587_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2579_ = stack[0].m_obj;
lean_object* v___y_2580_ = stack[1].m_obj;
lean_object* v___y_2581_ = stack[2].m_obj;
lean_object* v_res_2594_;
v_res_2594_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v_msg_2579_, v___y_2580_, v___y_2581_);
stack->m_obj
 = v_res_2594_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg___boxed(lean_object* v_msg_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v_msg_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
return v_res_2599_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1(void){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2601_ = ((lean_object*)(l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__0));
v___x_2602_ = l_Lean_stringToMessageData(v___x_2601_);
return v___x_2602_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = ((lean_object*)(l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__2));
v___x_2605_ = l_Lean_stringToMessageData(v___x_2604_);
return v___x_2605_;
}
}
lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object* v_declName_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v___x_2610_; uint8_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2610_ = lean_obj_once(&l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1, &l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__1);
v___x_2611_ = 0;
v___x_2612_ = l_Lean_MessageData_ofConstName(v_declName_2606_, v___x_2611_);
v___x_2613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2610_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = lean_obj_once(&l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3, &l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3_once, _init_l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___closed__3);
v___x_2615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2613_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v___x_2615_, v_a_2607_, v_a_2608_);
return v___x_2616_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2606_ = stack[0].m_obj;
lean_object* v_a_2607_ = stack[1].m_obj;
lean_object* v_a_2608_ = stack[2].m_obj;
lean_object* v_res_2617_;
v_res_2617_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2606_, v_a_2607_, v_a_2608_);
stack->m_obj
 = v_res_2617_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg___boxed(lean_object* v_declName_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2618_, v_a_2619_, v_a_2620_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
return v_res_2622_;
}
}
lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(lean_object* v_00_u03b1_2623_, lean_object* v_declName_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_2624_, v_a_2625_, v_a_2626_);
return v___x_2628_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2624_ = stack[1].m_obj;
lean_object* v_a_2625_ = stack[2].m_obj;
lean_object* v_a_2626_ = stack[3].m_obj;
lean_object* v_res_2629_;
v_res_2629_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(lean_box(0), v_declName_2624_, v_a_2625_, v_a_2626_);
stack->m_obj
 = v_res_2629_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___boxed(lean_object* v_00_u03b1_2630_, lean_object* v_declName_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute(v_00_u03b1_2630_, v_declName_2631_, v_a_2632_, v_a_2633_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
return v_res_2635_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(lean_object* v_00_u03b1_2636_, lean_object* v_msg_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___redArg(v_msg_2637_, v___y_2638_, v___y_2639_);
return v___x_2641_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2637_ = stack[1].m_obj;
lean_object* v___y_2638_ = stack[2].m_obj;
lean_object* v___y_2639_ = stack[3].m_obj;
lean_object* v_res_2642_;
v_res_2642_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(lean_box(0), v_msg_2637_, v___y_2638_, v___y_2639_);
stack->m_obj
 = v_res_2642_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0___boxed(lean_object* v_00_u03b1_2643_, lean_object* v_msg_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Lean_throwError___at___00Lean_Meta_Grind_throwNotMarkedWithGrindAttribute_spec__0(v_00_u03b1_2643_, v_msg_2644_, v___y_2645_, v___y_2646_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
return v_res_2648_;
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
