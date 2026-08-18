// Lean compiler output
// Module: Lean.Elab.Tactic.Do.LetElim
// Imports: public import Lean.Meta.Tactic.Simp import Init.Omega
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
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_KVMap_setNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_mergeBy(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setType(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setValue(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Simp_isCharLit(lean_object*);
uint8_t l_Lean_Meta_Simp_isOfNatNatLit(lean_object*);
uint8_t l_Lean_Meta_Simp_isOfScientificLit(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instBEqUses_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_instBEqUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_instBEqUses = (const lean_object*)&l_Lean_Elab_Tactic_Do_instBEqUses___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instOrdUses_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_instOrdUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_instOrdUses = (const lean_object*)&l_Lean_Elab_Tactic_Do_instOrdUses___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instInhabitedUses_default;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instInhabitedUses;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_add(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_fromNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_fromNat___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Uses_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_instAddUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_instAddUses = (const lean_object*)&l_Lean_Elab_Tactic_Do_instAddUses___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2_spec__4___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2_spec__4___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_FVarUses_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_instAddFVarUses = (const lean_object*)&l_Lean_Elab_Tactic_Do_instAddFVarUses___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticGet_elem_tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(141, 31, 109, 153, 11, 229, 201, 51)}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "get_elem_tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instAddBVarUses(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_addMData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_addMData___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_addMData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "uses"};
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 67, 224, 192, 49, 118, 23, 147)}};
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4;
static const lean_closure_object l_Lean_Elab_Tactic_Do_countUsesDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "BVar index out of bounds: "};
static const lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUses___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUses___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " >= "};
static const lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUses___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_Tactic_Do_countUses___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Elab_Tactic_Do_countUses___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Do_countUses___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_countUses___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_countUses___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_countUses___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_doNotDup(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_doNotDup___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2;
static lean_once_cell_t l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_elimLetsCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___closed__1;
static const lean_closure_object l_Lean_Elab_Tactic_Do_elimLetsCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elimLetsCore___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_Elab_Tactic_Do_Uses_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(lean_object* v_zero_23_){
_start:
{
lean_inc(v_zero_23_);
return v_zero_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg___boxed(lean_object* v_zero_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim___redArg(v_zero_24_);
lean_dec(v_zero_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_zero_29_){
_start:
{
lean_inc(v_zero_29_);
return v_zero_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_zero_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_zero_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_Elab_Tactic_Do_Uses_zero_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_zero_33_);
lean_dec(v_zero_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(lean_object* v_one_36_){
_start:
{
lean_inc(v_one_36_);
return v_one_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg___boxed(lean_object* v_one_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Elab_Tactic_Do_Uses_one_elim___redArg(v_one_37_);
lean_dec(v_one_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_one_42_){
_start:
{
lean_inc(v_one_42_);
return v_one_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_one_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_one_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_Elab_Tactic_Do_Uses_one_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_one_46_);
lean_dec(v_one_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(lean_object* v_many_49_){
_start:
{
lean_inc(v_many_49_);
return v_many_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg___boxed(lean_object* v_many_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Elab_Tactic_Do_Uses_many_elim___redArg(v_many_50_);
lean_dec(v_many_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_many_55_){
_start:
{
lean_inc(v_many_55_);
return v_many_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_many_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_many_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_Elab_Tactic_Do_Uses_many_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_many_59_);
lean_dec(v_many_59_);
return v_res_61_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instBEqUses_beq(uint8_t v_x_62_, uint8_t v_y_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_64_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_62_);
v___x_65_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_y_63_);
v___x_66_ = lean_nat_dec_eq(v___x_64_, v___x_65_);
lean_dec(v___x_65_);
lean_dec(v___x_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instBEqUses_beq___boxed(lean_object* v_x_67_, lean_object* v_y_68_){
_start:
{
uint8_t v_x_17__boxed_69_; uint8_t v_y_18__boxed_70_; uint8_t v_res_71_; lean_object* v_r_72_; 
v_x_17__boxed_69_ = lean_unbox(v_x_67_);
v_y_18__boxed_70_ = lean_unbox(v_y_68_);
v_res_71_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_x_17__boxed_69_, v_y_18__boxed_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_instOrdUses_ord(uint8_t v_x_75_, uint8_t v_y_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_77_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_x_75_);
v___x_78_ = l_Lean_Elab_Tactic_Do_Uses_ctorIdx(v_y_76_);
v___x_79_ = lean_nat_dec_lt(v___x_77_, v___x_78_);
if (v___x_79_ == 0)
{
uint8_t v___x_80_; 
v___x_80_ = lean_nat_dec_eq(v___x_77_, v___x_78_);
lean_dec(v___x_78_);
lean_dec(v___x_77_);
if (v___x_80_ == 0)
{
uint8_t v___x_81_; 
v___x_81_ = 2;
return v___x_81_;
}
else
{
uint8_t v___x_82_; 
v___x_82_ = 1;
return v___x_82_;
}
}
else
{
uint8_t v___x_83_; 
lean_dec(v___x_78_);
lean_dec(v___x_77_);
v___x_83_ = 0;
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instOrdUses_ord___boxed(lean_object* v_x_84_, lean_object* v_y_85_){
_start:
{
uint8_t v_x_30__boxed_86_; uint8_t v_y_31__boxed_87_; uint8_t v_res_88_; lean_object* v_r_89_; 
v_x_30__boxed_86_ = lean_unbox(v_x_84_);
v_y_31__boxed_87_ = lean_unbox(v_y_85_);
v_res_88_ = l_Lean_Elab_Tactic_Do_instOrdUses_ord(v_x_30__boxed_86_, v_y_31__boxed_87_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_instInhabitedUses_default(void){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_instInhabitedUses(void){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = 0;
return v___x_93_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_add(uint8_t v_x_94_, uint8_t v_x_95_){
_start:
{
if (v_x_94_ == 0)
{
return v_x_95_;
}
else
{
if (v_x_95_ == 0)
{
return v_x_94_;
}
else
{
uint8_t v___x_96_; 
v___x_96_ = 2;
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_add___boxed(lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
uint8_t v_x_30__boxed_99_; uint8_t v_x_31__boxed_100_; uint8_t v_res_101_; lean_object* v_r_102_; 
v_x_30__boxed_99_ = lean_unbox(v_x_97_);
v_x_31__boxed_100_ = lean_unbox(v_x_98_);
v_res_101_ = l_Lean_Elab_Tactic_Do_Uses_add(v_x_30__boxed_99_, v_x_31__boxed_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat(uint8_t v_x_103_){
_start:
{
switch(v_x_103_)
{
case 0:
{
lean_object* v___x_104_; 
v___x_104_ = lean_unsigned_to_nat(0u);
return v___x_104_;
}
case 1:
{
lean_object* v___x_105_; 
v___x_105_ = lean_unsigned_to_nat(1u);
return v___x_105_;
}
default: 
{
lean_object* v___x_106_; 
v___x_106_ = lean_unsigned_to_nat(2u);
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_toNat___boxed(lean_object* v_x_107_){
_start:
{
uint8_t v_x_34__boxed_108_; lean_object* v_res_109_; 
v_x_34__boxed_108_ = lean_unbox(v_x_107_);
v_res_109_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v_x_34__boxed_108_);
return v_res_109_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Uses_fromNat(lean_object* v_x_110_){
_start:
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_nat_dec_eq(v_x_110_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(1u);
v___x_114_ = lean_nat_dec_eq(v_x_110_, v___x_113_);
if (v___x_114_ == 0)
{
uint8_t v___x_115_; 
v___x_115_ = 2;
return v___x_115_;
}
else
{
uint8_t v___x_116_; 
v___x_116_ = 1;
return v___x_116_;
}
}
else
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Uses_fromNat___boxed(lean_object* v_x_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v_x_118_);
lean_dec(v_x_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(lean_object* v_m_123_, lean_object* v_query_124_, lean_object* v_x_125_, lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
lean_object* v_zero_128_; uint8_t v_isZero_129_; 
v_zero_128_ = lean_unsigned_to_nat(0u);
v_isZero_129_ = lean_nat_dec_eq(v_x_126_, v_zero_128_);
if (v_isZero_129_ == 1)
{
lean_dec(v_x_127_);
lean_dec(v_x_126_);
if (lean_obj_tag(v_x_125_) == 0)
{
lean_object* v___x_130_; 
v___x_130_ = lean_box(2);
return v___x_130_;
}
else
{
lean_object* v_val_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
v_val_131_ = lean_ctor_get(v_x_125_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v_x_125_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_val_131_);
lean_dec(v_x_125_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_val_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
else
{
lean_object* v_keyArray_139_; lean_object* v_valueArray_140_; lean_object* v___x_141_; uint8_t v_isSome_142_; 
v_keyArray_139_ = lean_ctor_get(v_m_123_, 1);
v_valueArray_140_ = lean_ctor_get(v_m_123_, 2);
v___x_141_ = lean_array_fget_borrowed(v_keyArray_139_, v_x_127_);
v_isSome_142_ = lean_noption_is_some(v___x_141_);
if (v_isSome_142_ == 0)
{
lean_dec(v_x_126_);
if (lean_obj_tag(v_x_125_) == 0)
{
lean_object* v___x_143_; 
v___x_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_143_, 0, v_x_127_);
return v___x_143_;
}
else
{
lean_object* v_val_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
lean_dec(v_x_127_);
v_val_144_ = lean_ctor_get(v_x_125_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v_x_125_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_val_144_);
lean_dec(v_x_125_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_val_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
else
{
lean_object* v_one_152_; lean_object* v_n_153_; lean_object* v___y_155_; 
v_one_152_ = lean_unsigned_to_nat(1u);
v_n_153_ = lean_nat_sub(v_x_126_, v_one_152_);
lean_dec(v_x_126_);
if (v_isSome_142_ == 0)
{
goto v___jp_161_;
}
else
{
lean_object* v___x_163_; uint8_t v_isSome_164_; 
v___x_163_ = lean_array_fget_borrowed(v_valueArray_140_, v_x_127_);
v_isSome_164_ = lean_noption_is_some(v___x_163_);
if (v_isSome_164_ == 0)
{
goto v___jp_161_;
}
else
{
lean_object* v_val_165_; uint8_t v___x_166_; 
lean_inc(v___x_141_);
v_val_165_ = lean_noption_get(v___x_141_);
v___x_166_ = l_Lean_instBEqFVarId_beq(v_val_165_, v_query_124_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
lean_dec(v_val_165_);
v___x_167_ = lean_array_get_size(v_keyArray_139_);
v___x_168_ = lean_nat_add(v_x_127_, v_one_152_);
lean_dec(v_x_127_);
v___x_169_ = lean_nat_dec_lt(v___x_168_, v___x_167_);
if (v___x_169_ == 0)
{
lean_dec(v___x_168_);
v_x_126_ = v_n_153_;
v_x_127_ = v_zero_128_;
goto _start;
}
else
{
v_x_126_ = v_n_153_;
v_x_127_ = v___x_168_;
goto _start;
}
}
else
{
lean_object* v_val_172_; lean_object* v___x_173_; 
lean_dec(v_n_153_);
lean_dec(v_x_125_);
lean_inc(v___x_163_);
v_val_172_ = lean_noption_get(v___x_163_);
v___x_173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_173_, 0, v_x_127_);
lean_ctor_set(v___x_173_, 1, v_val_165_);
lean_ctor_set(v___x_173_, 2, v_val_172_);
return v___x_173_;
}
}
}
v___jp_154_:
{
lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_156_ = lean_array_get_size(v_keyArray_139_);
v___x_157_ = lean_nat_add(v_x_127_, v_one_152_);
lean_dec(v_x_127_);
v___x_158_ = lean_nat_dec_lt(v___x_157_, v___x_156_);
if (v___x_158_ == 0)
{
lean_dec(v___x_157_);
v_x_125_ = v___y_155_;
v_x_126_ = v_n_153_;
v_x_127_ = v_zero_128_;
goto _start;
}
else
{
v_x_125_ = v___y_155_;
v_x_126_ = v_n_153_;
v_x_127_ = v___x_157_;
goto _start;
}
}
v___jp_161_:
{
if (lean_obj_tag(v_x_125_) == 0)
{
lean_object* v___x_162_; 
lean_inc(v_x_127_);
v___x_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_162_, 0, v_x_127_);
v___y_155_ = v___x_162_;
goto v___jp_154_;
}
else
{
v___y_155_ = v_x_125_;
goto v___jp_154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg___boxed(lean_object* v_m_174_, lean_object* v_query_175_, lean_object* v_x_176_, lean_object* v_x_177_, lean_object* v_x_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_m_174_, v_query_175_, v_x_176_, v_x_177_, v_x_178_);
lean_dec(v_query_175_);
lean_dec_ref(v_m_174_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___redArg(lean_object* v_m_180_, lean_object* v_query_181_){
_start:
{
lean_object* v_keyArray_182_; lean_object* v___x_183_; uint64_t v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v_fold_187_; uint64_t v___x_188_; uint64_t v___x_189_; uint64_t v___x_190_; size_t v___x_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; size_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_keyArray_182_ = lean_ctor_get(v_m_180_, 1);
v___x_183_ = lean_array_get_size(v_keyArray_182_);
v___x_184_ = l_Lean_instHashableFVarId_hash(v_query_181_);
v___x_185_ = 32ULL;
v___x_186_ = lean_uint64_shift_right(v___x_184_, v___x_185_);
v_fold_187_ = lean_uint64_xor(v___x_184_, v___x_186_);
v___x_188_ = 16ULL;
v___x_189_ = lean_uint64_shift_right(v_fold_187_, v___x_188_);
v___x_190_ = lean_uint64_xor(v_fold_187_, v___x_189_);
v___x_191_ = lean_uint64_to_usize(v___x_190_);
v___x_192_ = lean_usize_of_nat(v___x_183_);
v___x_193_ = ((size_t)1ULL);
v___x_194_ = lean_usize_sub(v___x_192_, v___x_193_);
v___x_195_ = lean_usize_land(v___x_191_, v___x_194_);
v___x_196_ = lean_usize_to_nat(v___x_195_);
v___x_197_ = lean_box(0);
v___x_198_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_m_180_, v_query_181_, v___x_197_, v___x_183_, v___x_196_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___redArg___boxed(lean_object* v_m_199_, lean_object* v_query_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___redArg(v_m_199_, v_query_200_);
lean_dec(v_query_200_);
lean_dec_ref(v_m_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2_spec__3___redArg(lean_object* v_b_202_, lean_object* v_acc_203_, lean_object* v_i_204_){
_start:
{
lean_object* v___y_206_; lean_object* v_keyArray_214_; lean_object* v_valueArray_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_keyArray_214_ = lean_ctor_get(v_b_202_, 1);
v_valueArray_215_ = lean_ctor_get(v_b_202_, 2);
v___x_216_ = lean_array_get_size(v_keyArray_214_);
v___x_217_ = lean_nat_dec_lt(v_i_204_, v___x_216_);
if (v___x_217_ == 0)
{
lean_dec(v_i_204_);
return v_acc_203_;
}
else
{
lean_object* v___x_218_; uint8_t v_isSome_219_; 
v___x_218_ = lean_array_fget_borrowed(v_keyArray_214_, v_i_204_);
v_isSome_219_ = lean_noption_is_some(v___x_218_);
if (v_isSome_219_ == 0)
{
goto v___jp_210_;
}
else
{
lean_object* v___x_220_; uint8_t v_isSome_221_; 
v___x_220_ = lean_array_fget_borrowed(v_valueArray_215_, v_i_204_);
v_isSome_221_ = lean_noption_is_some(v___x_220_);
if (v_isSome_221_ == 0)
{
goto v___jp_210_;
}
else
{
lean_object* v_val_222_; lean_object* v_val_223_; lean_object* v_i_225_; lean_object* v___x_230_; 
lean_inc(v___x_218_);
v_val_222_ = lean_noption_get(v___x_218_);
lean_inc(v___x_220_);
v_val_223_ = lean_noption_get(v___x_220_);
v___x_230_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___redArg(v_acc_203_, v_val_222_);
switch(lean_obj_tag(v___x_230_))
{
case 0:
{
lean_object* v_index_231_; lean_object* v_size_232_; lean_object* v___x_233_; 
v_index_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_index_231_);
lean_dec_ref_known(v___x_230_, 3);
v_size_232_ = lean_ctor_get(v_acc_203_, 0);
lean_inc(v_size_232_);
v___x_233_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_203_, v_size_232_, v_index_231_, v_val_222_, v_val_223_);
lean_dec(v_index_231_);
v___y_206_ = v___x_233_;
goto v___jp_205_;
}
case 1:
{
lean_object* v_index_234_; 
v_index_234_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_index_234_);
lean_dec_ref_known(v___x_230_, 1);
v_i_225_ = v_index_234_;
goto v___jp_224_;
}
default: 
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_203_, v___x_235_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_index_237_; 
v_index_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_index_237_);
lean_dec_ref_known(v___x_236_, 1);
v_i_225_ = v_index_237_;
goto v___jp_224_;
}
else
{
lean_dec(v_val_223_);
lean_dec(v_val_222_);
v___y_206_ = v_acc_203_;
goto v___jp_205_;
}
}
}
v___jp_224_:
{
lean_object* v_size_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_size_226_ = lean_ctor_get(v_acc_203_, 0);
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_nat_add(v_size_226_, v___x_227_);
v___x_229_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_203_, v___x_228_, v_i_225_, v_val_222_, v_val_223_);
lean_dec(v_i_225_);
v___y_206_ = v___x_229_;
goto v___jp_205_;
}
}
}
}
v___jp_205_:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_nat_add(v_i_204_, v___x_207_);
lean_dec(v_i_204_);
v_acc_203_ = v___y_206_;
v_i_204_ = v___x_208_;
goto _start;
}
v___jp_210_:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_add(v_i_204_, v___x_211_);
lean_dec(v_i_204_);
v_i_204_ = v___x_212_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_238_, lean_object* v_acc_239_, lean_object* v_i_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2_spec__3___redArg(v_b_238_, v_acc_239_, v_i_240_);
lean_dec_ref(v_b_238_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2___redArg(lean_object* v_init_242_, lean_object* v_b_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2_spec__3___redArg(v_b_243_, v_init_242_, v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2___redArg___boxed(lean_object* v_init_246_, lean_object* v_b_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2___redArg(v_init_246_, v_b_247_);
lean_dec_ref(v_b_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1___redArg(lean_object* v_m_249_){
_start:
{
lean_object* v_keyArray_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v_cellCount_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_target_257_; lean_object* v___x_258_; 
v_keyArray_250_ = lean_ctor_get(v_m_249_, 1);
v___x_251_ = lean_array_get_size(v_keyArray_250_);
v___x_252_ = lean_unsigned_to_nat(2u);
v_cellCount_253_ = lean_nat_mul(v___x_251_, v___x_252_);
v___x_254_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_253_);
v___x_255_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_253_);
v___x_256_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_253_);
v_target_257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_257_, 0, v___x_254_);
lean_ctor_set(v_target_257_, 1, v___x_255_);
lean_ctor_set(v_target_257_, 2, v___x_256_);
v___x_258_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2___redArg(v_target_257_, v_m_249_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1___redArg___boxed(lean_object* v_m_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1___redArg(v_m_259_);
lean_dec_ref(v_m_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2_spec__4___lam__0(uint8_t v_val_261_, lean_object* v_x_262_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_box(v_val_261_);
v___x_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
else
{
lean_object* v_val_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_275_; 
v_val_265_ = lean_ctor_get(v_x_262_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v_x_262_);
if (v_isSharedCheck_275_ == 0)
{
v___x_267_ = v_x_262_;
v_isShared_268_ = v_isSharedCheck_275_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_val_265_);
lean_dec(v_x_262_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_275_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
uint8_t v___x_269_; uint8_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_269_ = lean_unbox(v_val_265_);
lean_dec(v_val_265_);
v___x_270_ = l_Lean_Elab_Tactic_Do_Uses_add(v_val_261_, v___x_269_);
v___x_271_ = lean_box(v___x_270_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_271_);
v___x_273_ = v___x_267_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2_spec__4___lam__0___boxed(lean_object* v_val_276_, lean_object* v_x_277_){
_start:
{
uint8_t v_val_1497__boxed_278_; lean_object* v_res_279_; 
v_val_1497__boxed_278_ = lean_unbox(v_val_276_);
v_res_279_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2_spec__4___lam__0(v_val_1497__boxed_278_, v_x_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2_spec__4(lean_object* v_b_280_, lean_object* v_acc_281_, lean_object* v_i_282_){
_start:
{
lean_object* v___y_288_; lean_object* v_keyArray_292_; lean_object* v_valueArray_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v_keyArray_292_ = lean_ctor_get(v_b_280_, 1);
v_valueArray_293_ = lean_ctor_get(v_b_280_, 2);
v___x_294_ = lean_array_get_size(v_keyArray_292_);
v___x_295_ = lean_nat_dec_lt(v_i_282_, v___x_294_);
if (v___x_295_ == 0)
{
lean_dec(v_i_282_);
return v_acc_281_;
}
else
{
lean_object* v___x_296_; uint8_t v_isSome_297_; 
v___x_296_ = lean_array_fget_borrowed(v_keyArray_292_, v_i_282_);
v_isSome_297_ = lean_noption_is_some(v___x_296_);
if (v_isSome_297_ == 0)
{
goto v___jp_283_;
}
else
{
lean_object* v___x_298_; uint8_t v_isSome_299_; 
v___x_298_ = lean_array_fget_borrowed(v_valueArray_293_, v_i_282_);
v_isSome_299_ = lean_noption_is_some(v___x_298_);
if (v_isSome_299_ == 0)
{
goto v___jp_283_;
}
else
{
lean_object* v_val_300_; lean_object* v_val_301_; lean_object* v___x_302_; 
lean_inc(v___x_296_);
v_val_300_ = lean_noption_get(v___x_296_);
lean_inc(v___x_298_);
v_val_301_ = lean_noption_get(v___x_298_);
v___x_302_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___redArg(v_acc_281_, v_val_300_);
switch(lean_obj_tag(v___x_302_))
{
case 0:
{
lean_object* v_index_303_; lean_object* v_value_304_; lean_object* v___x_305_; uint8_t v___x_306_; lean_object* v___x_307_; lean_object* v_val_308_; lean_object* v_size_309_; lean_object* v___x_310_; 
v_index_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_index_303_);
v_value_304_ = lean_ctor_get(v___x_302_, 2);
lean_inc(v_value_304_);
lean_dec_ref_known(v___x_302_, 3);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v_value_304_);
v___x_306_ = lean_unbox(v_val_301_);
lean_dec(v_val_301_);
v___x_307_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2_spec__4___lam__0(v___x_306_, v___x_305_);
v_val_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_val_308_);
lean_dec(v___x_307_);
v_size_309_ = lean_ctor_get(v_acc_281_, 0);
lean_inc(v_size_309_);
v___x_310_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_281_, v_size_309_, v_index_303_, v_val_300_, v_val_308_);
lean_dec(v_index_303_);
v___y_288_ = v___x_310_;
goto v___jp_287_;
}
case 1:
{
lean_object* v_index_311_; lean_object* v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v_val_315_; lean_object* v___y_317_; lean_object* v_i_318_; lean_object* v_size_333_; lean_object* v_keyArray_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v_index_311_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_index_311_);
lean_dec_ref_known(v___x_302_, 1);
v___x_312_ = lean_box(0);
v___x_313_ = lean_unbox(v_val_301_);
lean_dec(v_val_301_);
v___x_314_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2_spec__4___lam__0(v___x_313_, v___x_312_);
v_val_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_val_315_);
lean_dec(v___x_314_);
v_size_333_ = lean_ctor_get(v_acc_281_, 0);
v_keyArray_334_ = lean_ctor_get(v_acc_281_, 1);
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_nat_add(v_size_333_, v___x_335_);
v___x_337_ = lean_array_get_size(v_keyArray_334_);
v___x_338_ = lean_nat_dec_lt(v___x_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_dec(v___x_336_);
lean_dec(v_index_311_);
goto v___jp_323_;
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_339_ = lean_unsigned_to_nat(4u);
v___x_340_ = lean_nat_mul(v___x_336_, v___x_339_);
v___x_341_ = lean_unsigned_to_nat(3u);
v___x_342_ = lean_nat_mul(v___x_337_, v___x_341_);
v___x_343_ = lean_nat_dec_le(v___x_340_, v___x_342_);
lean_dec(v___x_342_);
lean_dec(v___x_340_);
if (v___x_343_ == 0)
{
lean_dec(v___x_336_);
lean_dec(v_index_311_);
goto v___jp_323_;
}
else
{
lean_object* v___x_344_; 
v___x_344_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_281_, v___x_336_, v_index_311_, v_val_300_, v_val_315_);
lean_dec(v_index_311_);
v___y_288_ = v___x_344_;
goto v___jp_287_;
}
}
v___jp_316_:
{
lean_object* v_size_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v_size_319_ = lean_ctor_get(v___y_317_, 0);
v___x_320_ = lean_unsigned_to_nat(1u);
v___x_321_ = lean_nat_add(v_size_319_, v___x_320_);
v___x_322_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_317_, v___x_321_, v_i_318_, v_val_300_, v_val_315_);
lean_dec(v_i_318_);
v___y_288_ = v___x_322_;
goto v___jp_287_;
}
v___jp_323_:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1___redArg(v_acc_281_);
lean_dec_ref(v_acc_281_);
v___x_325_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___redArg(v___x_324_, v_val_300_);
switch(lean_obj_tag(v___x_325_))
{
case 0:
{
lean_object* v_index_326_; lean_object* v_size_327_; lean_object* v___x_328_; 
v_index_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_index_326_);
lean_dec_ref_known(v___x_325_, 3);
v_size_327_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_size_327_);
v___x_328_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_324_, v_size_327_, v_index_326_, v_val_300_, v_val_315_);
lean_dec(v_index_326_);
v___y_288_ = v___x_328_;
goto v___jp_287_;
}
case 1:
{
lean_object* v_index_329_; 
v_index_329_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_index_329_);
lean_dec_ref_known(v___x_325_, 1);
v___y_317_ = v___x_324_;
v_i_318_ = v_index_329_;
goto v___jp_316_;
}
default: 
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_324_, v___x_330_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_index_332_; 
v_index_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_index_332_);
lean_dec_ref_known(v___x_331_, 1);
v___y_317_ = v___x_324_;
v_i_318_ = v_index_332_;
goto v___jp_316_;
}
else
{
lean_dec(v_val_315_);
lean_dec(v_val_300_);
v___y_288_ = v___x_324_;
goto v___jp_287_;
}
}
}
}
}
default: 
{
lean_object* v___x_345_; uint8_t v___x_346_; lean_object* v___x_347_; lean_object* v_val_348_; lean_object* v___y_350_; lean_object* v_i_351_; lean_object* v___y_357_; lean_object* v_size_366_; lean_object* v_keyArray_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_345_ = lean_box(0);
v___x_346_ = lean_unbox(v_val_301_);
lean_dec(v_val_301_);
v___x_347_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2_spec__4___lam__0(v___x_346_, v___x_345_);
v_val_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_val_348_);
lean_dec(v___x_347_);
v_size_366_ = lean_ctor_get(v_acc_281_, 0);
v_keyArray_367_ = lean_ctor_get(v_acc_281_, 1);
v___x_368_ = lean_unsigned_to_nat(1u);
v___x_369_ = lean_nat_add(v_size_366_, v___x_368_);
v___x_370_ = lean_array_get_size(v_keyArray_367_);
v___x_371_ = lean_nat_dec_lt(v___x_369_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; 
lean_dec(v___x_369_);
v___x_372_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1___redArg(v_acc_281_);
lean_dec_ref(v_acc_281_);
v___y_357_ = v___x_372_;
goto v___jp_356_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_373_ = lean_unsigned_to_nat(4u);
v___x_374_ = lean_nat_mul(v___x_369_, v___x_373_);
lean_dec(v___x_369_);
v___x_375_ = lean_unsigned_to_nat(3u);
v___x_376_ = lean_nat_mul(v___x_370_, v___x_375_);
v___x_377_ = lean_nat_dec_le(v___x_374_, v___x_376_);
lean_dec(v___x_376_);
lean_dec(v___x_374_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
v___x_378_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1___redArg(v_acc_281_);
lean_dec_ref(v_acc_281_);
v___y_357_ = v___x_378_;
goto v___jp_356_;
}
else
{
v___y_357_ = v_acc_281_;
goto v___jp_356_;
}
}
v___jp_349_:
{
lean_object* v_size_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_size_352_ = lean_ctor_get(v___y_350_, 0);
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = lean_nat_add(v_size_352_, v___x_353_);
v___x_355_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_350_, v___x_354_, v_i_351_, v_val_300_, v_val_348_);
lean_dec(v_i_351_);
v___y_288_ = v___x_355_;
goto v___jp_287_;
}
v___jp_356_:
{
lean_object* v___x_358_; 
v___x_358_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___redArg(v___y_357_, v_val_300_);
switch(lean_obj_tag(v___x_358_))
{
case 0:
{
lean_object* v_index_359_; lean_object* v_size_360_; lean_object* v___x_361_; 
v_index_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_index_359_);
lean_dec_ref_known(v___x_358_, 3);
v_size_360_ = lean_ctor_get(v___y_357_, 0);
lean_inc(v_size_360_);
v___x_361_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_357_, v_size_360_, v_index_359_, v_val_300_, v_val_348_);
lean_dec(v_index_359_);
v___y_288_ = v___x_361_;
goto v___jp_287_;
}
case 1:
{
lean_object* v_index_362_; 
v_index_362_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_index_362_);
lean_dec_ref_known(v___x_358_, 1);
v___y_350_ = v___y_357_;
v_i_351_ = v_index_362_;
goto v___jp_349_;
}
default: 
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_357_, v___x_363_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_index_365_; 
v_index_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_index_365_);
lean_dec_ref_known(v___x_364_, 1);
v___y_350_ = v___y_357_;
v_i_351_ = v_index_365_;
goto v___jp_349_;
}
else
{
lean_dec(v_val_348_);
lean_dec(v_val_300_);
v___y_288_ = v___y_357_;
goto v___jp_287_;
}
}
}
}
}
}
}
}
}
v___jp_283_:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = lean_nat_add(v_i_282_, v___x_284_);
lean_dec(v_i_282_);
v_i_282_ = v___x_285_;
goto _start;
}
v___jp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_nat_add(v_i_282_, v___x_289_);
lean_dec(v_i_282_);
v_acc_281_ = v___y_288_;
v_i_282_ = v___x_290_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2_spec__4___boxed(lean_object* v_b_379_, lean_object* v_acc_380_, lean_object* v_i_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2_spec__4(v_b_379_, v_acc_380_, v_i_381_);
lean_dec_ref(v_b_379_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(lean_object* v_init_383_, lean_object* v_b_384_){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2_spec__4(v_b_384_, v_init_383_, v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2___boxed(lean_object* v_init_387_, lean_object* v_b_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_init_387_, v_b_388_);
lean_dec_ref(v_b_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add(lean_object* v_a_390_, lean_object* v_b_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_b_391_, v_a_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_FVarUses_add___boxed(lean_object* v_a_393_, lean_object* v_b_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Elab_Tactic_Do_FVarUses_add(v_a_393_, v_b_394_);
lean_dec_ref(v_a_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(lean_object* v_00_u03b2_396_, lean_object* v_m_397_, lean_object* v_query_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___redArg(v_m_397_, v_query_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___boxed(lean_object* v_00_u03b2_400_, lean_object* v_m_401_, lean_object* v_query_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0(v_00_u03b2_400_, v_m_401_, v_query_402_);
lean_dec(v_query_402_);
lean_dec_ref(v_m_401_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(lean_object* v_00_u03b2_404_, lean_object* v_m_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1___redArg(v_m_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1___boxed(lean_object* v_00_u03b2_407_, lean_object* v_m_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1(v_00_u03b2_407_, v_m_408_);
lean_dec_ref(v_m_408_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(lean_object* v_00_u03b2_410_, lean_object* v_m_411_, lean_object* v_query_412_, lean_object* v_x_413_, lean_object* v_x_414_, lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___redArg(v_m_411_, v_query_412_, v_x_413_, v_x_414_, v_x_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0___boxed(lean_object* v_00_u03b2_418_, lean_object* v_m_419_, lean_object* v_query_420_, lean_object* v_x_421_, lean_object* v_x_422_, lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0_spec__0(v_00_u03b2_418_, v_m_419_, v_query_420_, v_x_421_, v_x_422_, v_x_423_, v_x_424_);
lean_dec(v_query_420_);
lean_dec_ref(v_m_419_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2(lean_object* v_00_u03b2_426_, lean_object* v_init_427_, lean_object* v_b_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2___redArg(v_init_427_, v_b_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2___boxed(lean_object* v_00_u03b2_430_, lean_object* v_init_431_, lean_object* v_b_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2(v_00_u03b2_430_, v_init_431_, v_b_432_);
lean_dec_ref(v_b_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_434_, lean_object* v_b_435_, lean_object* v_acc_436_, lean_object* v_i_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2_spec__3___redArg(v_b_435_, v_acc_436_, v_i_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_439_, lean_object* v_b_440_, lean_object* v_acc_441_, lean_object* v_i_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1_spec__2_spec__3(v_00_u03b2_439_, v_b_440_, v_acc_441_, v_i_442_);
lean_dec_ref(v_b_440_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(lean_object* v_x_446_){
_start:
{
if (lean_obj_tag(v_x_446_) == 0)
{
lean_object* v___x_447_; 
v___x_447_ = lean_unsigned_to_nat(0u);
return v___x_447_;
}
else
{
lean_object* v___x_448_; 
v___x_448_ = lean_unsigned_to_nat(1u);
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg___boxed(lean_object* v_x_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(v_x_449_);
lean_dec(v_x_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(lean_object* v_n_451_, lean_object* v_x_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___redArg(v_x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx___boxed(lean_object* v_n_454_, lean_object* v_x_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorIdx(v_n_454_, v_x_455_);
lean_dec(v_x_455_);
lean_dec(v_n_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(lean_object* v_t_457_, lean_object* v_k_458_){
_start:
{
if (lean_obj_tag(v_t_457_) == 0)
{
return v_k_458_;
}
else
{
lean_object* v_uses_459_; lean_object* v___x_460_; 
v_uses_459_ = lean_ctor_get(v_t_457_, 0);
lean_inc_ref(v_uses_459_);
lean_dec_ref_known(v_t_457_, 1);
v___x_460_ = lean_apply_1(v_k_458_, v_uses_459_);
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(lean_object* v_n_461_, lean_object* v_motive_462_, lean_object* v_ctorIdx_463_, lean_object* v_t_464_, lean_object* v_h_465_, lean_object* v_k_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_464_, v_k_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___boxed(lean_object* v_n_468_, lean_object* v_motive_469_, lean_object* v_ctorIdx_470_, lean_object* v_t_471_, lean_object* v_h_472_, lean_object* v_k_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim(v_n_468_, v_motive_469_, v_ctorIdx_470_, v_t_471_, v_h_472_, v_k_473_);
lean_dec(v_ctorIdx_470_);
lean_dec(v_n_468_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___redArg(lean_object* v_t_475_, lean_object* v_none_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_475_, v_none_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim(lean_object* v_n_478_, lean_object* v_motive_479_, lean_object* v_t_480_, lean_object* v_h_481_, lean_object* v_none_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_480_, v_none_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_none_elim___boxed(lean_object* v_n_484_, lean_object* v_motive_485_, lean_object* v_t_486_, lean_object* v_h_487_, lean_object* v_none_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Elab_Tactic_Do_BVarUses_none_elim(v_n_484_, v_motive_485_, v_t_486_, v_h_487_, v_none_488_);
lean_dec(v_n_484_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___redArg(lean_object* v_t_490_, lean_object* v_some_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_490_, v_some_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim(lean_object* v_n_493_, lean_object* v_motive_494_, lean_object* v_t_495_, lean_object* v_h_496_, lean_object* v_some_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Elab_Tactic_Do_BVarUses_ctorElim___redArg(v_t_495_, v_some_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_some_elim___boxed(lean_object* v_n_499_, lean_object* v_motive_500_, lean_object* v_t_501_, lean_object* v_h_502_, lean_object* v_some_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Elab_Tactic_Do_BVarUses_some_elim(v_n_499_, v_motive_500_, v_t_501_, v_h_502_, v_some_503_);
lean_dec(v_n_499_);
return v_res_504_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__12));
v___x_530_ = l_Lean_mkAtom(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__13);
v___x_532_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_533_ = lean_array_push(v___x_532_, v___x_531_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_534_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__14);
v___x_535_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__11));
v___x_536_ = lean_box(2);
v___x_537_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_535_);
lean_ctor_set(v___x_537_, 2, v___x_534_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__15);
v___x_539_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_540_ = lean_array_push(v___x_539_, v___x_538_);
return v___x_540_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_541_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__16);
v___x_542_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__9));
v___x_543_ = lean_box(2);
v___x_544_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v___x_542_);
lean_ctor_set(v___x_544_, 2, v___x_541_);
return v___x_544_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_545_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__17);
v___x_546_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_547_ = lean_array_push(v___x_546_, v___x_545_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_548_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__18);
v___x_549_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__7));
v___x_550_ = lean_box(2);
v___x_551_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v___x_549_);
lean_ctor_set(v___x_551_, 2, v___x_548_);
return v___x_551_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_552_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__19);
v___x_553_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__5));
v___x_554_ = lean_array_push(v___x_553_, v___x_552_);
return v___x_554_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_555_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__20);
v___x_556_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__4));
v___x_557_ = lean_box(2);
v___x_558_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v___x_556_);
lean_ctor_set(v___x_558_, 2, v___x_555_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1(void){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21, &l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21_once, _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1___closed__21);
return v___x_559_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(lean_object* v_numBVars_560_, lean_object* v_n_561_, lean_object* v_i_562_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_563_ = lean_unsigned_to_nat(1u);
v___x_564_ = lean_nat_sub(v_numBVars_560_, v___x_563_);
v___x_565_ = lean_nat_sub(v___x_564_, v_n_561_);
lean_dec(v___x_564_);
v___x_566_ = lean_nat_dec_eq(v_i_562_, v___x_565_);
lean_dec(v___x_565_);
if (v___x_566_ == 0)
{
uint8_t v___x_567_; 
v___x_567_ = 0;
return v___x_567_;
}
else
{
uint8_t v___x_568_; 
v___x_568_ = 1;
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed(lean_object* v_numBVars_569_, lean_object* v_n_570_, lean_object* v_i_571_){
_start:
{
uint8_t v_res_572_; lean_object* v_r_573_; 
v_res_572_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0(v_numBVars_569_, v_n_570_, v_i_571_);
lean_dec(v_i_571_);
lean_dec(v_n_570_);
lean_dec(v_numBVars_569_);
v_r_573_ = lean_box(v_res_572_);
return v_r_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(lean_object* v_numBVars_574_, lean_object* v_n_575_){
_start:
{
lean_object* v___f_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
lean_inc(v_numBVars_574_);
v___f_576_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_BVarUses_single___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_576_, 0, v_numBVars_574_);
lean_closure_set(v___f_576_, 1, v_n_575_);
v___x_577_ = l_Array_ofFn___redArg(v_numBVars_574_, v___f_576_);
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_single(lean_object* v_numBVars_579_, lean_object* v_n_580_, lean_object* v_x_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Elab_Tactic_Do_BVarUses_single___redArg(v_numBVars_579_, v_n_580_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop(lean_object* v_numBVars_587_, lean_object* v_x_588_){
_start:
{
if (lean_obj_tag(v_x_588_) == 0)
{
lean_object* v___x_589_; 
v___x_589_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_pop___closed__0));
return v___x_589_;
}
else
{
lean_object* v_uses_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_603_; 
v_uses_590_ = lean_ctor_get(v_x_588_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_603_ == 0)
{
v___x_592_ = v_x_588_;
v_isShared_593_ = v_isSharedCheck_603_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_uses_590_);
lean_dec(v_x_588_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_603_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_594_ = lean_unsigned_to_nat(1u);
v___x_595_ = lean_nat_add(v_numBVars_587_, v___x_594_);
v___x_596_ = lean_nat_sub(v___x_595_, v___x_594_);
lean_dec(v___x_595_);
v___x_597_ = lean_array_fget(v_uses_590_, v___x_596_);
lean_dec(v___x_596_);
v___x_598_ = lean_array_pop(v_uses_590_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_598_);
v___x_600_ = v___x_592_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_602_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_597_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
return v___x_601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_pop___boxed(lean_object* v_numBVars_604_, lean_object* v_x_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_Elab_Tactic_Do_BVarUses_pop(v_numBVars_604_, v_x_605_);
lean_dec(v_numBVars_604_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(lean_object* v_as_607_, lean_object* v_bs_608_, lean_object* v_i_609_, lean_object* v_cs_610_){
_start:
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = lean_array_get_size(v_as_607_);
v___x_612_ = lean_nat_dec_lt(v_i_609_, v___x_611_);
if (v___x_612_ == 0)
{
lean_dec(v_i_609_);
return v_cs_610_;
}
else
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = lean_array_get_size(v_bs_608_);
v___x_614_ = lean_nat_dec_lt(v_i_609_, v___x_613_);
if (v___x_614_ == 0)
{
lean_dec(v_i_609_);
return v_cs_610_;
}
else
{
lean_object* v_a_615_; lean_object* v_b_616_; uint8_t v___x_617_; uint8_t v___x_618_; uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_a_615_ = lean_array_fget_borrowed(v_as_607_, v_i_609_);
v_b_616_ = lean_array_fget_borrowed(v_bs_608_, v_i_609_);
v___x_617_ = lean_unbox(v_a_615_);
v___x_618_ = lean_unbox(v_b_616_);
v___x_619_ = l_Lean_Elab_Tactic_Do_Uses_add(v___x_617_, v___x_618_);
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_nat_add(v_i_609_, v___x_620_);
lean_dec(v_i_609_);
v___x_622_ = lean_box(v___x_619_);
v___x_623_ = lean_array_push(v_cs_610_, v___x_622_);
v_i_609_ = v___x_621_;
v_cs_610_ = v___x_623_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0___boxed(lean_object* v_as_625_, lean_object* v_bs_626_, lean_object* v_i_627_, lean_object* v_cs_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(v_as_625_, v_bs_626_, v_i_627_, v_cs_628_);
lean_dec_ref(v_bs_626_);
lean_dec_ref(v_as_625_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(lean_object* v_a_632_, lean_object* v_b_633_){
_start:
{
if (lean_obj_tag(v_a_632_) == 0)
{
return v_b_633_;
}
else
{
if (lean_obj_tag(v_b_633_) == 0)
{
lean_object* v_uses_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
v_uses_634_ = lean_ctor_get(v_a_632_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v_a_632_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v_a_632_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_uses_634_);
lean_dec(v_a_632_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_uses_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
else
{
lean_object* v_uses_642_; lean_object* v_uses_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_653_; 
v_uses_642_ = lean_ctor_get(v_a_632_, 0);
lean_inc_ref(v_uses_642_);
lean_dec_ref_known(v_a_632_, 1);
v_uses_643_ = lean_ctor_get(v_b_633_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v_b_633_);
if (v_isSharedCheck_653_ == 0)
{
v___x_645_ = v_b_633_;
v_isShared_646_ = v_isSharedCheck_653_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_uses_643_);
lean_dec(v_b_633_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_653_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_BVarUses_add___redArg___closed__0));
v___x_649_ = l_Array_zipWithMAux___at___00Lean_Elab_Tactic_Do_BVarUses_add_spec__0(v_uses_642_, v_uses_643_, v___x_647_, v___x_648_);
lean_dec_ref(v_uses_643_);
lean_dec_ref(v_uses_642_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_649_);
v___x_651_ = v___x_645_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add(lean_object* v_numBVars_654_, lean_object* v_a_655_, lean_object* v_b_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Elab_Tactic_Do_BVarUses_add___redArg(v_a_655_, v_b_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_BVarUses_add___boxed(lean_object* v_numBVars_658_, lean_object* v_a_659_, lean_object* v_b_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_Elab_Tactic_Do_BVarUses_add(v_numBVars_658_, v_a_659_, v_b_660_);
lean_dec(v_numBVars_658_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instAddBVarUses(lean_object* v_numBVars_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_BVarUses_add___boxed), 3, 1);
lean_closure_set(v___x_663_, 0, v_numBVars_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2___redArg(lean_object* v_f_664_, lean_object* v_x_665_){
_start:
{
lean_object* v_fst_666_; lean_object* v_snd_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_675_; 
v_fst_666_ = lean_ctor_get(v_x_665_, 0);
v_snd_667_ = lean_ctor_get(v_x_665_, 1);
v_isSharedCheck_675_ = !lean_is_exclusive(v_x_665_);
if (v_isSharedCheck_675_ == 0)
{
v___x_669_ = v_x_665_;
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_snd_667_);
lean_inc(v_fst_666_);
lean_dec(v_x_665_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_671_ = lean_apply_1(v_f_664_, v_fst_666_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_671_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_snd_667_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_over1Of2(lean_object* v_00_u03b1_u2081_676_, lean_object* v_00_u03b1_u2082_677_, lean_object* v_00_u03b2_678_, lean_object* v_f_679_, lean_object* v_x_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v_f_679_, v_x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0(lean_object* v_x_682_, lean_object* v_new_683_, lean_object* v_x_684_){
_start:
{
lean_inc_ref(v_new_683_);
return v_new_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData___lam__0___boxed(lean_object* v_x_685_, lean_object* v_new_686_, lean_object* v_x_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Elab_Tactic_Do_addMData___lam__0(v_x_685_, v_new_686_, v_x_687_);
lean_dec_ref(v_x_687_);
lean_dec_ref(v_new_686_);
lean_dec(v_x_685_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_addMData(lean_object* v_d_690_, lean_object* v_e_691_){
_start:
{
if (lean_obj_tag(v_e_691_) == 10)
{
lean_object* v_data_692_; lean_object* v_expr_693_; lean_object* v___f_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v_data_692_ = lean_ctor_get(v_e_691_, 0);
lean_inc(v_data_692_);
v_expr_693_ = lean_ctor_get(v_e_691_, 1);
lean_inc_ref(v_expr_693_);
lean_dec_ref_known(v_e_691_, 2);
v___f_694_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_addMData___closed__0));
v___x_695_ = l_Lean_KVMap_mergeBy(v___f_694_, v_d_690_, v_data_692_);
lean_dec(v_data_692_);
v___x_696_ = l_Lean_Expr_mdata___override(v___x_695_, v_expr_693_);
return v___x_696_;
}
else
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_Expr_mdata___override(v_d_690_, v_e_691_);
return v___x_697_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(lean_object* v_e_698_){
_start:
{
uint8_t v___y_700_; 
switch(lean_obj_tag(v_e_698_))
{
case 1:
{
uint8_t v___x_702_; 
v___x_702_ = 0;
return v___x_702_;
}
case 5:
{
uint8_t v___x_703_; 
v___x_703_ = l_Lean_Meta_Simp_isOfNatNatLit(v_e_698_);
if (v___x_703_ == 0)
{
uint8_t v___x_704_; 
v___x_704_ = l_Lean_Meta_Simp_isOfScientificLit(v_e_698_);
v___y_700_ = v___x_704_;
goto v___jp_699_;
}
else
{
v___y_700_ = v___x_703_;
goto v___jp_699_;
}
}
case 6:
{
uint8_t v___x_705_; 
v___x_705_ = 0;
return v___x_705_;
}
case 7:
{
uint8_t v___x_706_; 
v___x_706_ = 0;
return v___x_706_;
}
case 8:
{
uint8_t v___x_707_; 
v___x_707_ = 0;
return v___x_707_;
}
case 10:
{
lean_object* v_expr_708_; 
v_expr_708_ = lean_ctor_get(v_e_698_, 1);
v_e_698_ = v_expr_708_;
goto _start;
}
case 11:
{
lean_object* v_struct_710_; 
v_struct_710_ = lean_ctor_get(v_e_698_, 2);
v_e_698_ = v_struct_710_;
goto _start;
}
default: 
{
uint8_t v___x_712_; 
v___x_712_ = 1;
return v___x_712_;
}
}
v___jp_699_:
{
if (v___y_700_ == 0)
{
uint8_t v___x_701_; 
v___x_701_ = l_Lean_Meta_Simp_isCharLit(v_e_698_);
return v___x_701_;
}
else
{
return v___y_700_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup___boxed(lean_object* v_e_713_){
_start:
{
uint8_t v_res_714_; lean_object* v_r_715_; 
v_res_714_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_e_713_);
lean_dec_ref(v_e_713_);
v_r_715_ = lean_box(v_res_714_);
return v_r_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___lam__0(lean_object* v_val_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_717_, 0, v_val_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(lean_object* v_msgData_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; lean_object* v_env_725_; lean_object* v___x_726_; lean_object* v_mctx_727_; lean_object* v_lctx_728_; lean_object* v_options_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_724_ = lean_st_ref_get(v___y_722_);
v_env_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc_ref(v_env_725_);
lean_dec(v___x_724_);
v___x_726_ = lean_st_ref_get(v___y_720_);
v_mctx_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc_ref(v_mctx_727_);
lean_dec(v___x_726_);
v_lctx_728_ = lean_ctor_get(v___y_719_, 2);
v_options_729_ = lean_ctor_get(v___y_721_, 2);
lean_inc_ref(v_options_729_);
lean_inc_ref(v_lctx_728_);
v___x_730_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_730_, 0, v_env_725_);
lean_ctor_set(v___x_730_, 1, v_mctx_727_);
lean_ctor_set(v___x_730_, 2, v_lctx_728_);
lean_ctor_set(v___x_730_, 3, v_options_729_);
v___x_731_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v_msgData_718_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5___boxed(lean_object* v_msgData_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msgData_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(lean_object* v_msg_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_ref_746_; lean_object* v___x_747_; lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_756_; 
v_ref_746_ = lean_ctor_get(v___y_743_, 5);
v___x_747_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3_spec__5(v_msg_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
v_a_748_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_756_ == 0)
{
v___x_750_ = v___x_747_;
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_754_; 
lean_inc(v_ref_746_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_ref_746_);
lean_ctor_set(v___x_752_, 1, v_a_748_);
if (v_isShared_751_ == 0)
{
lean_ctor_set_tag(v___x_750_, 1);
lean_ctor_set(v___x_750_, 0, v___x_752_);
v___x_754_ = v___x_750_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg___boxed(lean_object* v_msg_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__0(lean_object* v_data_764_, lean_object* v_expr_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Expr_mdata___override(v_data_764_, v_expr_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___lam__1(lean_object* v_typeName_767_, lean_object* v_idx_768_, lean_object* v_struct_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_Expr_proj___override(v_typeName_767_, v_idx_768_, v_struct_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(lean_object* v___y_771_){
_start:
{
lean_object* v___x_773_; lean_object* v_ngen_774_; lean_object* v_namePrefix_775_; lean_object* v_idx_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_805_; 
v___x_773_ = lean_st_ref_get(v___y_771_);
v_ngen_774_ = lean_ctor_get(v___x_773_, 2);
lean_inc_ref(v_ngen_774_);
lean_dec(v___x_773_);
v_namePrefix_775_ = lean_ctor_get(v_ngen_774_, 0);
v_idx_776_ = lean_ctor_get(v_ngen_774_, 1);
v_isSharedCheck_805_ = !lean_is_exclusive(v_ngen_774_);
if (v_isSharedCheck_805_ == 0)
{
v___x_778_ = v_ngen_774_;
v_isShared_779_ = v_isSharedCheck_805_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_idx_776_);
lean_inc(v_namePrefix_775_);
lean_dec(v_ngen_774_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_805_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v_env_781_; lean_object* v_nextMacroScope_782_; lean_object* v_auxDeclNGen_783_; lean_object* v_traceState_784_; lean_object* v_cache_785_; lean_object* v_messages_786_; lean_object* v_infoState_787_; lean_object* v_snapshotTasks_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_803_; 
v___x_780_ = lean_st_ref_take(v___y_771_);
v_env_781_ = lean_ctor_get(v___x_780_, 0);
v_nextMacroScope_782_ = lean_ctor_get(v___x_780_, 1);
v_auxDeclNGen_783_ = lean_ctor_get(v___x_780_, 3);
v_traceState_784_ = lean_ctor_get(v___x_780_, 4);
v_cache_785_ = lean_ctor_get(v___x_780_, 5);
v_messages_786_ = lean_ctor_get(v___x_780_, 6);
v_infoState_787_ = lean_ctor_get(v___x_780_, 7);
v_snapshotTasks_788_ = lean_ctor_get(v___x_780_, 8);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; 
v_unused_804_ = lean_ctor_get(v___x_780_, 2);
lean_dec(v_unused_804_);
v___x_790_ = v___x_780_;
v_isShared_791_ = v_isSharedCheck_803_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_snapshotTasks_788_);
lean_inc(v_infoState_787_);
lean_inc(v_messages_786_);
lean_inc(v_cache_785_);
lean_inc(v_traceState_784_);
lean_inc(v_auxDeclNGen_783_);
lean_inc(v_nextMacroScope_782_);
lean_inc(v_env_781_);
lean_dec(v___x_780_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_803_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v_r_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
lean_inc(v_idx_776_);
lean_inc(v_namePrefix_775_);
v_r_792_ = l_Lean_Name_num___override(v_namePrefix_775_, v_idx_776_);
v___x_793_ = lean_unsigned_to_nat(1u);
v___x_794_ = lean_nat_add(v_idx_776_, v___x_793_);
lean_dec(v_idx_776_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v___x_794_);
v___x_796_ = v___x_778_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_namePrefix_775_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v___x_794_);
v___x_796_ = v_reuseFailAlloc_802_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_798_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 2, v___x_796_);
v___x_798_ = v___x_790_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_env_781_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_nextMacroScope_782_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_801_, 3, v_auxDeclNGen_783_);
lean_ctor_set(v_reuseFailAlloc_801_, 4, v_traceState_784_);
lean_ctor_set(v_reuseFailAlloc_801_, 5, v_cache_785_);
lean_ctor_set(v_reuseFailAlloc_801_, 6, v_messages_786_);
lean_ctor_set(v_reuseFailAlloc_801_, 7, v_infoState_787_);
lean_ctor_set(v_reuseFailAlloc_801_, 8, v_snapshotTasks_788_);
v___x_798_ = v_reuseFailAlloc_801_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_st_ref_put(v___y_771_, v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v_r_792_);
return v___x_800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg___boxed(lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v___y_806_);
lean_dec(v___y_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4(lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
v___x_814_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v___y_812_);
v_a_815_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4___boxed(lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4(v___y_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(lean_object* v_m_829_, lean_object* v_query_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___redArg(v_m_829_, v_query_830_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_index_832_; lean_object* v_key_833_; lean_object* v_value_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
v_index_832_ = lean_ctor_get(v___x_831_, 0);
v_key_833_ = lean_ctor_get(v___x_831_, 1);
v_value_834_ = lean_ctor_get(v___x_831_, 2);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_831_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_value_834_);
lean_inc(v_key_833_);
lean_inc(v_index_832_);
lean_dec(v___x_831_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_index_832_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_key_833_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_value_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
else
{
lean_object* v___x_842_; 
lean_dec(v___x_831_);
v___x_842_ = lean_box(1);
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg___boxed(lean_object* v_m_843_, lean_object* v_query_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_m_843_, v_query_844_);
lean_dec(v_query_844_);
lean_dec_ref(v_m_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(lean_object* v_m_846_, lean_object* v_a_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_m_846_, v_a_847_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_index_849_; lean_object* v_size_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_index_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_index_849_);
lean_dec_ref_known(v___x_848_, 3);
v_size_850_ = lean_ctor_get(v_m_846_, 0);
v___x_851_ = lean_unsigned_to_nat(1u);
v___x_852_ = lean_nat_sub(v_size_850_, v___x_851_);
v___x_853_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_846_, v___x_852_, v_index_849_);
lean_dec(v_index_849_);
return v___x_853_;
}
else
{
return v_m_846_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg___boxed(lean_object* v_m_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_854_, v_a_855_);
lean_dec(v_a_855_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(lean_object* v_m_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_m_857_, v_a_858_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_value_860_; lean_object* v___x_861_; 
v_value_860_ = lean_ctor_get(v___x_859_, 2);
lean_inc(v_value_860_);
lean_dec_ref_known(v___x_859_, 3);
v___x_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_861_, 0, v_value_860_);
return v___x_861_;
}
else
{
lean_object* v___x_862_; 
v___x_862_ = lean_box(0);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg___boxed(lean_object* v_m_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_m_863_, v_a_864_);
lean_dec(v_a_864_);
lean_dec_ref(v_m_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(lean_object* v_m_866_, lean_object* v_a_867_, lean_object* v_fallback_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_m_866_, v_a_867_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_inc(v_fallback_868_);
return v_fallback_868_;
}
else
{
lean_object* v_val_870_; 
v_val_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_val_870_);
lean_dec_ref_known(v___x_869_, 1);
return v_val_870_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg___boxed(lean_object* v_m_871_, lean_object* v_a_872_, lean_object* v_fallback_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_871_, v_a_872_, v_fallback_873_);
lean_dec(v_fallback_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_m_871_);
return v_res_874_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2(void){
_start:
{
lean_object* v_cellCount_878_; lean_object* v___x_879_; 
v_cellCount_878_ = lean_unsigned_to_nat(16u);
v___x_879_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_878_);
return v___x_879_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3(void){
_start:
{
lean_object* v_cellCount_880_; lean_object* v___x_881_; 
v_cellCount_880_ = lean_unsigned_to_nat(16u);
v___x_881_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_880_);
return v___x_881_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_882_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__3);
v___x_883_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2);
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___x_883_);
lean_ctor_set(v___x_885_, 2, v___x_882_);
return v___x_885_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__1(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__0));
v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
return v___x_889_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__3(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__2));
v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
return v___x_892_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__4(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_894_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__1___redArg(v___x_893_);
return v___x_894_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__5(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__4, &l_Lean_Elab_Tactic_Do_countUses___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__4);
v___x_897_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_896_, v___x_895_);
return v___x_897_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__6(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2);
v___x_899_ = lean_array_get_size(v___x_898_);
return v___x_899_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_countUses___closed__7(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_900_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__6, &l_Lean_Elab_Tactic_Do_countUses___closed__6_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__6);
v___x_901_ = lean_unsigned_to_nat(1u);
v___x_902_ = lean_nat_dec_lt(v___x_901_, v___x_900_);
return v___x_902_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__8(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = lean_unsigned_to_nat(3u);
v___x_904_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__6, &l_Lean_Elab_Tactic_Do_countUses___closed__6_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__6);
v___x_905_ = lean_nat_mul(v___x_904_, v___x_903_);
return v___x_905_;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_Do_countUses___closed__9(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_906_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__8, &l_Lean_Elab_Tactic_Do_countUses___closed__8_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__8);
v___x_907_ = lean_unsigned_to_nat(4u);
v___x_908_ = lean_nat_dec_le(v___x_907_, v___x_906_);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_countUses___closed__11(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUses___closed__10));
v___x_911_ = l_Lean_stringToMessageData(v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses(lean_object* v_e_912_, lean_object* v_subst_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v___y_920_; lean_object* v___y_924_; 
switch(lean_obj_tag(v_e_912_))
{
case 0:
{
lean_object* v_deBruijnIndex_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v_deBruijnIndex_927_ = lean_ctor_get(v_e_912_, 0);
v___x_928_ = lean_array_get_size(v_subst_913_);
v___x_929_ = lean_nat_dec_lt(v_deBruijnIndex_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
lean_inc(v_deBruijnIndex_927_);
lean_dec_ref_known(v_e_912_, 1);
lean_dec_ref(v_subst_913_);
v___x_930_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__1, &l_Lean_Elab_Tactic_Do_countUses___closed__1_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__1);
v___x_931_ = l_Nat_reprFast(v_deBruijnIndex_927_);
v___x_932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
v___x_933_ = l_Lean_MessageData_ofFormat(v___x_932_);
v___x_934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_930_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__3, &l_Lean_Elab_Tactic_Do_countUses___closed__3_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__3);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = l_Nat_reprFast(v___x_928_);
v___x_938_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
v___x_939_ = l_Lean_MessageData_ofFormat(v___x_938_);
v___x_940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_936_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_940_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
return v___x_941_;
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; lean_object* v___y_948_; lean_object* v_i_949_; lean_object* v___y_955_; lean_object* v_i_956_; lean_object* v___y_962_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_984_; 
v___x_942_ = lean_unsigned_to_nat(1u);
v___x_943_ = lean_nat_sub(v___x_928_, v___x_942_);
v___x_944_ = lean_nat_sub(v___x_943_, v_deBruijnIndex_927_);
lean_dec(v___x_943_);
v___x_945_ = lean_array_fget(v_subst_913_, v___x_944_);
lean_dec(v___x_944_);
lean_dec_ref(v_subst_913_);
v___x_946_ = 1;
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_984_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___redArg(v___x_973_, v___x_945_);
switch(lean_obj_tag(v___x_984_))
{
case 0:
{
lean_object* v_index_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_index_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_index_985_);
lean_dec_ref_known(v___x_984_, 3);
v___x_986_ = lean_box(v___x_946_);
v___x_987_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_973_, v___x_972_, v_index_985_, v___x_945_, v___x_986_);
lean_dec(v_index_985_);
v___y_920_ = v___x_987_;
goto v___jp_919_;
}
case 1:
{
lean_object* v_index_988_; uint8_t v___x_989_; 
v_index_988_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_index_988_);
lean_dec_ref_known(v___x_984_, 1);
v___x_989_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_countUses___closed__7, &l_Lean_Elab_Tactic_Do_countUses___closed__7_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__7);
if (v___x_989_ == 0)
{
lean_dec(v_index_988_);
goto v___jp_974_;
}
else
{
uint8_t v___x_990_; 
v___x_990_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_countUses___closed__9, &l_Lean_Elab_Tactic_Do_countUses___closed__9_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__9);
if (v___x_990_ == 0)
{
lean_dec(v_index_988_);
goto v___jp_974_;
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_box(v___x_946_);
v___x_992_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_973_, v___x_942_, v_index_988_, v___x_945_, v___x_991_);
lean_dec(v_index_988_);
v___y_920_ = v___x_992_;
goto v___jp_919_;
}
}
}
default: 
{
uint8_t v___x_993_; 
v___x_993_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_countUses___closed__7, &l_Lean_Elab_Tactic_Do_countUses___closed__7_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__7);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
v___x_994_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__4, &l_Lean_Elab_Tactic_Do_countUses___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__4);
v___y_962_ = v___x_994_;
goto v___jp_961_;
}
else
{
uint8_t v___x_995_; 
v___x_995_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_countUses___closed__9, &l_Lean_Elab_Tactic_Do_countUses___closed__9_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__9);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; 
v___x_996_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__4, &l_Lean_Elab_Tactic_Do_countUses___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__4);
v___y_962_ = v___x_996_;
goto v___jp_961_;
}
else
{
v___y_962_ = v___x_973_;
goto v___jp_961_;
}
}
}
}
v___jp_947_:
{
lean_object* v_size_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v_size_950_ = lean_ctor_get(v___y_948_, 0);
v___x_951_ = lean_nat_add(v_size_950_, v___x_942_);
v___x_952_ = lean_box(v___x_946_);
v___x_953_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_948_, v___x_951_, v_i_949_, v___x_945_, v___x_952_);
lean_dec(v_i_949_);
v___y_920_ = v___x_953_;
goto v___jp_919_;
}
v___jp_954_:
{
lean_object* v_size_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_size_957_ = lean_ctor_get(v___y_955_, 0);
v___x_958_ = lean_nat_add(v_size_957_, v___x_942_);
v___x_959_ = lean_box(v___x_946_);
v___x_960_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_955_, v___x_958_, v_i_956_, v___x_945_, v___x_959_);
lean_dec(v_i_956_);
v___y_920_ = v___x_960_;
goto v___jp_919_;
}
v___jp_961_:
{
lean_object* v___x_963_; 
v___x_963_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___redArg(v___y_962_, v___x_945_);
switch(lean_obj_tag(v___x_963_))
{
case 0:
{
lean_object* v_index_964_; lean_object* v_size_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_index_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_index_964_);
lean_dec_ref_known(v___x_963_, 3);
v_size_965_ = lean_ctor_get(v___y_962_, 0);
lean_inc(v_size_965_);
v___x_966_ = lean_box(v___x_946_);
v___x_967_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_962_, v_size_965_, v_index_964_, v___x_945_, v___x_966_);
lean_dec(v_index_964_);
v___y_920_ = v___x_967_;
goto v___jp_919_;
}
case 1:
{
lean_object* v_index_968_; 
v_index_968_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_index_968_);
lean_dec_ref_known(v___x_963_, 1);
v___y_955_ = v___y_962_;
v_i_956_ = v_index_968_;
goto v___jp_954_;
}
default: 
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = lean_unsigned_to_nat(0u);
v___x_970_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_962_, v___x_969_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_index_971_; 
v_index_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_index_971_);
lean_dec_ref_known(v___x_970_, 1);
v___y_955_ = v___y_962_;
v_i_956_ = v_index_971_;
goto v___jp_954_;
}
else
{
lean_dec(v___x_945_);
v___y_920_ = v___y_962_;
goto v___jp_919_;
}
}
}
}
v___jp_974_:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__4, &l_Lean_Elab_Tactic_Do_countUses___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__4);
v___x_976_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___redArg(v___x_975_, v___x_945_);
switch(lean_obj_tag(v___x_976_))
{
case 0:
{
lean_object* v_index_977_; lean_object* v_size_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_index_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_index_977_);
lean_dec_ref_known(v___x_976_, 3);
v_size_978_ = lean_ctor_get(v___x_975_, 0);
v___x_979_ = lean_box(v___x_946_);
lean_inc(v_size_978_);
v___x_980_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_975_, v_size_978_, v_index_977_, v___x_945_, v___x_979_);
lean_dec(v_index_977_);
v___y_920_ = v___x_980_;
goto v___jp_919_;
}
case 1:
{
lean_object* v_index_981_; 
v_index_981_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_index_981_);
lean_dec_ref_known(v___x_976_, 1);
v___y_948_ = v___x_975_;
v_i_949_ = v_index_981_;
goto v___jp_947_;
}
default: 
{
lean_object* v___x_982_; 
v___x_982_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__5, &l_Lean_Elab_Tactic_Do_countUses___closed__5_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__5);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_index_983_; 
v_index_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_index_983_);
v___y_948_ = v___x_975_;
v_i_949_ = v_index_983_;
goto v___jp_947_;
}
else
{
lean_dec(v___x_945_);
v___y_920_ = v___x_975_;
goto v___jp_919_;
}
}
}
}
}
}
case 1:
{
lean_object* v_fvarId_997_; uint8_t v___x_998_; lean_object* v___y_1000_; lean_object* v_i_1001_; lean_object* v___y_1008_; lean_object* v_i_1009_; lean_object* v___y_1016_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1038_; 
lean_dec_ref(v_subst_913_);
v_fvarId_997_ = lean_ctor_get(v_e_912_, 0);
v___x_998_ = 1;
v___x_1026_ = lean_unsigned_to_nat(0u);
v___x_1027_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_1038_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___redArg(v___x_1027_, v_fvarId_997_);
switch(lean_obj_tag(v___x_1038_))
{
case 0:
{
lean_object* v_index_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v_index_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_index_1039_);
lean_dec_ref_known(v___x_1038_, 3);
v___x_1040_ = lean_box(v___x_998_);
lean_inc(v_fvarId_997_);
v___x_1041_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1027_, v___x_1026_, v_index_1039_, v_fvarId_997_, v___x_1040_);
lean_dec(v_index_1039_);
v___y_924_ = v___x_1041_;
goto v___jp_923_;
}
case 1:
{
lean_object* v_index_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_index_1042_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_index_1042_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1043_ = lean_unsigned_to_nat(1u);
v___x_1044_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_countUses___closed__7, &l_Lean_Elab_Tactic_Do_countUses___closed__7_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__7);
if (v___x_1044_ == 0)
{
lean_dec(v_index_1042_);
goto v___jp_1028_;
}
else
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_countUses___closed__9, &l_Lean_Elab_Tactic_Do_countUses___closed__9_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__9);
if (v___x_1045_ == 0)
{
lean_dec(v_index_1042_);
goto v___jp_1028_;
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_box(v___x_998_);
lean_inc(v_fvarId_997_);
v___x_1047_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1027_, v___x_1043_, v_index_1042_, v_fvarId_997_, v___x_1046_);
lean_dec(v_index_1042_);
v___y_924_ = v___x_1047_;
goto v___jp_923_;
}
}
}
default: 
{
uint8_t v___x_1048_; 
v___x_1048_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_countUses___closed__7, &l_Lean_Elab_Tactic_Do_countUses___closed__7_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__7);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__4, &l_Lean_Elab_Tactic_Do_countUses___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__4);
v___y_1016_ = v___x_1049_;
goto v___jp_1015_;
}
else
{
uint8_t v___x_1050_; 
v___x_1050_ = lean_uint8_once(&l_Lean_Elab_Tactic_Do_countUses___closed__9, &l_Lean_Elab_Tactic_Do_countUses___closed__9_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__9);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__4, &l_Lean_Elab_Tactic_Do_countUses___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__4);
v___y_1016_ = v___x_1051_;
goto v___jp_1015_;
}
else
{
v___y_1016_ = v___x_1027_;
goto v___jp_1015_;
}
}
}
}
v___jp_999_:
{
lean_object* v_size_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_size_1002_ = lean_ctor_get(v___y_1000_, 0);
v___x_1003_ = lean_unsigned_to_nat(1u);
v___x_1004_ = lean_nat_add(v_size_1002_, v___x_1003_);
v___x_1005_ = lean_box(v___x_998_);
lean_inc(v_fvarId_997_);
v___x_1006_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1000_, v___x_1004_, v_i_1001_, v_fvarId_997_, v___x_1005_);
lean_dec(v_i_1001_);
v___y_924_ = v___x_1006_;
goto v___jp_923_;
}
v___jp_1007_:
{
lean_object* v_size_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_size_1010_ = lean_ctor_get(v___y_1008_, 0);
v___x_1011_ = lean_unsigned_to_nat(1u);
v___x_1012_ = lean_nat_add(v_size_1010_, v___x_1011_);
v___x_1013_ = lean_box(v___x_998_);
lean_inc(v_fvarId_997_);
v___x_1014_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1008_, v___x_1012_, v_i_1009_, v_fvarId_997_, v___x_1013_);
lean_dec(v_i_1009_);
v___y_924_ = v___x_1014_;
goto v___jp_923_;
}
v___jp_1015_:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___redArg(v___y_1016_, v_fvarId_997_);
switch(lean_obj_tag(v___x_1017_))
{
case 0:
{
lean_object* v_index_1018_; lean_object* v_size_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v_index_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_index_1018_);
lean_dec_ref_known(v___x_1017_, 3);
v_size_1019_ = lean_ctor_get(v___y_1016_, 0);
lean_inc(v_size_1019_);
v___x_1020_ = lean_box(v___x_998_);
lean_inc(v_fvarId_997_);
v___x_1021_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1016_, v_size_1019_, v_index_1018_, v_fvarId_997_, v___x_1020_);
lean_dec(v_index_1018_);
v___y_924_ = v___x_1021_;
goto v___jp_923_;
}
case 1:
{
lean_object* v_index_1022_; 
v_index_1022_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_index_1022_);
lean_dec_ref_known(v___x_1017_, 1);
v___y_1008_ = v___y_1016_;
v_i_1009_ = v_index_1022_;
goto v___jp_1007_;
}
default: 
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1016_, v___x_1023_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_index_1025_; 
v_index_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_index_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v___y_1008_ = v___y_1016_;
v_i_1009_ = v_index_1025_;
goto v___jp_1007_;
}
else
{
v___y_924_ = v___y_1016_;
goto v___jp_923_;
}
}
}
}
v___jp_1028_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__4, &l_Lean_Elab_Tactic_Do_countUses___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__4);
v___x_1030_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__0___redArg(v___x_1029_, v_fvarId_997_);
switch(lean_obj_tag(v___x_1030_))
{
case 0:
{
lean_object* v_index_1031_; lean_object* v_size_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_index_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_index_1031_);
lean_dec_ref_known(v___x_1030_, 3);
v_size_1032_ = lean_ctor_get(v___x_1029_, 0);
v___x_1033_ = lean_box(v___x_998_);
lean_inc(v_fvarId_997_);
lean_inc(v_size_1032_);
v___x_1034_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1029_, v_size_1032_, v_index_1031_, v_fvarId_997_, v___x_1033_);
lean_dec(v_index_1031_);
v___y_924_ = v___x_1034_;
goto v___jp_923_;
}
case 1:
{
lean_object* v_index_1035_; 
v_index_1035_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_index_1035_);
lean_dec_ref_known(v___x_1030_, 1);
v___y_1000_ = v___x_1029_;
v_i_1001_ = v_index_1035_;
goto v___jp_999_;
}
default: 
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__5, &l_Lean_Elab_Tactic_Do_countUses___closed__5_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__5);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_index_1037_; 
v_index_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_index_1037_);
v___y_1000_ = v___x_1029_;
v_i_1001_ = v_index_1037_;
goto v___jp_999_;
}
else
{
v___y_924_ = v___x_1029_;
goto v___jp_923_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_1052_; lean_object* v_arg_1053_; lean_object* v___x_1054_; 
v_fn_1052_ = lean_ctor_get(v_e_912_, 0);
lean_inc_ref(v_fn_1052_);
v_arg_1053_ = lean_ctor_get(v_e_912_, 1);
lean_inc_ref(v_arg_1053_);
lean_dec_ref_known(v_e_912_, 2);
lean_inc_ref(v_subst_913_);
v___x_1054_ = l_Lean_Elab_Tactic_Do_countUses(v_fn_1052_, v_subst_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v_fst_1056_; lean_object* v_snd_1057_; lean_object* v___x_1058_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1054_, 1);
v_fst_1056_ = lean_ctor_get(v_a_1055_, 0);
lean_inc(v_fst_1056_);
v_snd_1057_ = lean_ctor_get(v_a_1055_, 1);
lean_inc(v_snd_1057_);
lean_dec(v_a_1055_);
v___x_1058_ = l_Lean_Elab_Tactic_Do_countUses(v_arg_1053_, v_subst_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1077_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1077_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1077_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v_fst_1063_; lean_object* v_snd_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1076_; 
v_fst_1063_ = lean_ctor_get(v_a_1059_, 0);
v_snd_1064_ = lean_ctor_get(v_a_1059_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_a_1059_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1066_ = v_a_1059_;
v_isShared_1067_ = v_isSharedCheck_1076_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_snd_1064_);
lean_inc(v_fst_1063_);
lean_dec(v_a_1059_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1076_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v___x_1068_ = l_Lean_Expr_app___override(v_fst_1056_, v_fst_1063_);
v___x_1069_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_snd_1064_, v_snd_1057_);
lean_dec(v_snd_1057_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v___x_1069_);
lean_ctor_set(v___x_1066_, 0, v___x_1068_);
v___x_1071_ = v___x_1066_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1073_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1071_);
v___x_1073_ = v___x_1061_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
else
{
lean_dec(v_snd_1057_);
lean_dec(v_fst_1056_);
return v___x_1058_;
}
}
else
{
lean_dec_ref(v_arg_1053_);
lean_dec_ref(v_subst_913_);
return v___x_1054_;
}
}
case 6:
{
lean_object* v_binderName_1078_; lean_object* v_binderType_1079_; lean_object* v_body_1080_; uint8_t v_binderInfo_1081_; lean_object* v___x_1082_; 
v_binderName_1078_ = lean_ctor_get(v_e_912_, 0);
lean_inc(v_binderName_1078_);
v_binderType_1079_ = lean_ctor_get(v_e_912_, 1);
lean_inc_ref(v_binderType_1079_);
v_body_1080_ = lean_ctor_get(v_e_912_, 2);
lean_inc_ref(v_body_1080_);
v_binderInfo_1081_ = lean_ctor_get_uint8(v_e_912_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_912_, 3);
v___x_1082_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4(v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1084_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v___x_1082_, 1);
lean_inc_ref(v_subst_913_);
v___x_1084_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_1079_, v_subst_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v_fst_1086_; lean_object* v_snd_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v_fst_1086_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_fst_1086_);
v_snd_1087_ = lean_ctor_get(v_a_1085_, 1);
lean_inc(v_snd_1087_);
lean_dec(v_a_1085_);
lean_inc(v_a_1083_);
v___x_1088_ = lean_array_push(v_subst_913_, v_a_1083_);
v___x_1089_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1080_, v___x_1088_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1109_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1109_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1109_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_fst_1094_; lean_object* v_snd_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1108_; 
v_fst_1094_ = lean_ctor_get(v_a_1090_, 0);
v_snd_1095_ = lean_ctor_get(v_a_1090_, 1);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_a_1090_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1097_ = v_a_1090_;
v_isShared_1098_ = v_isSharedCheck_1108_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_snd_1095_);
lean_inc(v_fst_1094_);
lean_dec(v_a_1090_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1108_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1099_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_snd_1095_, v_snd_1087_);
lean_dec(v_snd_1087_);
v___x_1100_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_1099_, v_a_1083_);
lean_dec(v_a_1083_);
v___x_1101_ = l_Lean_Expr_lam___override(v_binderName_1078_, v_fst_1086_, v_fst_1094_, v_binderInfo_1081_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 1, v___x_1100_);
lean_ctor_set(v___x_1097_, 0, v___x_1101_);
v___x_1103_ = v___x_1097_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v___x_1100_);
v___x_1103_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1105_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1103_);
v___x_1105_ = v___x_1092_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
else
{
lean_dec(v_snd_1087_);
lean_dec(v_fst_1086_);
lean_dec(v_a_1083_);
lean_dec(v_binderName_1078_);
return v___x_1089_;
}
}
else
{
lean_dec(v_a_1083_);
lean_dec_ref(v_body_1080_);
lean_dec(v_binderName_1078_);
lean_dec_ref(v_subst_913_);
return v___x_1084_;
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec_ref(v_body_1080_);
lean_dec_ref(v_binderType_1079_);
lean_dec(v_binderName_1078_);
lean_dec_ref(v_subst_913_);
v_a_1110_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1082_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1082_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
case 7:
{
lean_object* v_binderName_1118_; lean_object* v_binderType_1119_; lean_object* v_body_1120_; uint8_t v_binderInfo_1121_; lean_object* v___x_1122_; 
v_binderName_1118_ = lean_ctor_get(v_e_912_, 0);
lean_inc(v_binderName_1118_);
v_binderType_1119_ = lean_ctor_get(v_e_912_, 1);
lean_inc_ref(v_binderType_1119_);
v_body_1120_ = lean_ctor_get(v_e_912_, 2);
lean_inc_ref(v_body_1120_);
v_binderInfo_1121_ = lean_ctor_get_uint8(v_e_912_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_912_, 3);
v___x_1122_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4(v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1124_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
lean_inc_ref(v_subst_913_);
v___x_1124_ = l_Lean_Elab_Tactic_Do_countUses(v_binderType_1119_, v_subst_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v_fst_1126_; lean_object* v_snd_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1125_);
lean_dec_ref_known(v___x_1124_, 1);
v_fst_1126_ = lean_ctor_get(v_a_1125_, 0);
lean_inc(v_fst_1126_);
v_snd_1127_ = lean_ctor_get(v_a_1125_, 1);
lean_inc(v_snd_1127_);
lean_dec(v_a_1125_);
lean_inc(v_a_1123_);
v___x_1128_ = lean_array_push(v_subst_913_, v_a_1123_);
v___x_1129_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1120_, v___x_1128_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1149_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1132_ = v___x_1129_;
v_isShared_1133_ = v_isSharedCheck_1149_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1129_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1149_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v_fst_1134_; lean_object* v_snd_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1148_; 
v_fst_1134_ = lean_ctor_get(v_a_1130_, 0);
v_snd_1135_ = lean_ctor_get(v_a_1130_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_a_1130_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1137_ = v_a_1130_;
v_isShared_1138_ = v_isSharedCheck_1148_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_snd_1135_);
lean_inc(v_fst_1134_);
lean_dec(v_a_1130_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1148_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1139_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_snd_1135_, v_snd_1127_);
lean_dec(v_snd_1127_);
v___x_1140_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___x_1139_, v_a_1123_);
lean_dec(v_a_1123_);
v___x_1141_ = l_Lean_Expr_forallE___override(v_binderName_1118_, v_fst_1126_, v_fst_1134_, v_binderInfo_1121_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 1, v___x_1140_);
lean_ctor_set(v___x_1137_, 0, v___x_1141_);
v___x_1143_ = v___x_1137_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___x_1140_);
v___x_1143_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1145_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1143_);
v___x_1145_ = v___x_1132_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
else
{
lean_dec(v_snd_1127_);
lean_dec(v_fst_1126_);
lean_dec(v_a_1123_);
lean_dec(v_binderName_1118_);
return v___x_1129_;
}
}
else
{
lean_dec(v_a_1123_);
lean_dec_ref(v_body_1120_);
lean_dec(v_binderName_1118_);
lean_dec_ref(v_subst_913_);
return v___x_1124_;
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v_body_1120_);
lean_dec_ref(v_binderType_1119_);
lean_dec(v_binderName_1118_);
lean_dec_ref(v_subst_913_);
v_a_1150_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1122_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1122_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
case 8:
{
lean_object* v_declName_1158_; lean_object* v_type_1159_; lean_object* v_value_1160_; lean_object* v_body_1161_; uint8_t v_nondep_1162_; lean_object* v___x_1163_; 
v_declName_1158_ = lean_ctor_get(v_e_912_, 0);
lean_inc(v_declName_1158_);
v_type_1159_ = lean_ctor_get(v_e_912_, 1);
lean_inc_ref(v_type_1159_);
v_value_1160_ = lean_ctor_get(v_e_912_, 2);
lean_inc_ref(v_value_1160_);
v_body_1161_ = lean_ctor_get(v_e_912_, 3);
lean_inc_ref(v_body_1161_);
v_nondep_1162_ = lean_ctor_get_uint8(v_e_912_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_912_, 4);
v___x_1163_ = l_Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4(v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc_n(v_a_1164_, 2);
lean_dec_ref_known(v___x_1163_, 1);
lean_inc_ref(v_subst_913_);
v___x_1165_ = lean_array_push(v_subst_913_, v_a_1164_);
v___x_1166_ = l_Lean_Elab_Tactic_Do_countUses(v_body_1161_, v___x_1165_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1209_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1209_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1209_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_fst_1171_; lean_object* v_snd_1172_; lean_object* v___x_1174_; 
v_fst_1171_ = lean_ctor_get(v_a_1167_, 0);
lean_inc(v_fst_1171_);
v_snd_1172_ = lean_ctor_get(v_a_1167_, 1);
lean_inc(v_snd_1172_);
lean_dec(v_a_1167_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set_tag(v___x_1169_, 1);
lean_ctor_set(v___x_1169_, 0, v_value_1160_);
v___x_1174_ = v___x_1169_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_value_1160_);
v___x_1174_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_a_1164_, v_type_1159_, v___x_1174_, v_snd_1172_, v_subst_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
lean_dec(v_a_1164_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1199_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1199_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1199_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v_snd_1180_; lean_object* v_fst_1181_; 
v_snd_1180_ = lean_ctor_get(v_a_1176_, 1);
lean_inc(v_snd_1180_);
v_fst_1181_ = lean_ctor_get(v_snd_1180_, 0);
lean_inc(v_fst_1181_);
if (lean_obj_tag(v_fst_1181_) == 1)
{
lean_object* v_fst_1182_; lean_object* v_snd_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1195_; 
v_fst_1182_ = lean_ctor_get(v_a_1176_, 0);
lean_inc(v_fst_1182_);
lean_dec(v_a_1176_);
v_snd_1183_ = lean_ctor_get(v_snd_1180_, 1);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_snd_1180_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v_snd_1180_, 0);
lean_dec(v_unused_1196_);
v___x_1185_ = v_snd_1180_;
v_isShared_1186_ = v_isSharedCheck_1195_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_snd_1183_);
lean_dec(v_snd_1180_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1195_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_val_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v_val_1187_ = lean_ctor_get(v_fst_1181_, 0);
lean_inc(v_val_1187_);
lean_dec_ref_known(v_fst_1181_, 1);
v___x_1188_ = l_Lean_Expr_letE___override(v_declName_1158_, v_fst_1182_, v_val_1187_, v_fst_1171_, v_nondep_1162_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1188_);
v___x_1190_ = v___x_1185_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_snd_1183_);
v___x_1190_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1192_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1190_);
v___x_1192_ = v___x_1178_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_dec(v_fst_1181_);
lean_dec(v_snd_1180_);
lean_del_object(v___x_1178_);
lean_dec(v_a_1176_);
lean_dec(v_fst_1171_);
lean_dec(v_declName_1158_);
v___x_1197_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUses___closed__11, &l_Lean_Elab_Tactic_Do_countUses___closed__11_once, _init_l_Lean_Elab_Tactic_Do_countUses___closed__11);
v___x_1198_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v___x_1197_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
return v___x_1198_;
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec(v_fst_1171_);
lean_dec(v_declName_1158_);
v_a_1200_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1175_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1175_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1164_);
lean_dec_ref(v_value_1160_);
lean_dec_ref(v_type_1159_);
lean_dec(v_declName_1158_);
lean_dec_ref(v_subst_913_);
return v___x_1166_;
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v_body_1161_);
lean_dec_ref(v_value_1160_);
lean_dec_ref(v_type_1159_);
lean_dec(v_declName_1158_);
lean_dec_ref(v_subst_913_);
v_a_1210_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1163_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1163_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
case 10:
{
lean_object* v_data_1218_; lean_object* v_expr_1219_; lean_object* v___x_1220_; 
v_data_1218_ = lean_ctor_get(v_e_912_, 0);
lean_inc(v_data_1218_);
v_expr_1219_ = lean_ctor_get(v_e_912_, 1);
lean_inc_ref(v_expr_1219_);
lean_dec_ref_known(v_e_912_, 2);
v___x_1220_ = l_Lean_Elab_Tactic_Do_countUses(v_expr_1219_, v_subst_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1230_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1230_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1230_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___f_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___f_1225_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__0), 2, 1);
lean_closure_set(v___f_1225_, 0, v_data_1218_);
v___x_1226_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1225_, v_a_1221_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1226_);
v___x_1228_ = v___x_1223_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
else
{
lean_dec(v_data_1218_);
return v___x_1220_;
}
}
case 11:
{
lean_object* v_typeName_1231_; lean_object* v_idx_1232_; lean_object* v_struct_1233_; lean_object* v___x_1234_; 
v_typeName_1231_ = lean_ctor_get(v_e_912_, 0);
lean_inc(v_typeName_1231_);
v_idx_1232_ = lean_ctor_get(v_e_912_, 1);
lean_inc(v_idx_1232_);
v_struct_1233_ = lean_ctor_get(v_e_912_, 2);
lean_inc_ref(v_struct_1233_);
lean_dec_ref_known(v_e_912_, 3);
v___x_1234_ = l_Lean_Elab_Tactic_Do_countUses(v_struct_1233_, v_subst_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1244_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1244_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1244_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___f_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___f_1239_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_countUses___lam__1), 3, 2);
lean_closure_set(v___f_1239_, 0, v_typeName_1231_);
lean_closure_set(v___f_1239_, 1, v_idx_1232_);
v___x_1240_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1239_, v_a_1235_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1240_);
v___x_1242_ = v___x_1237_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
else
{
lean_dec(v_idx_1232_);
lean_dec(v_typeName_1231_);
return v___x_1234_;
}
}
default: 
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_dec_ref(v_subst_913_);
v___x_1245_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_e_912_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
return v___x_1247_;
}
}
v___jp_919_:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_921_, 0, v_e_912_);
lean_ctor_set(v___x_921_, 1, v___y_920_);
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
return v___x_922_;
}
v___jp_923_:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v_e_912_);
lean_ctor_set(v___x_925_, 1, v___y_924_);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
return v___x_926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl(lean_object* v_fvarId_1248_, lean_object* v_ty_1249_, lean_object* v_val_x3f_1250_, lean_object* v_bodyUses_1251_, lean_object* v_subst_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v___x_1258_; 
lean_inc_ref(v_subst_1252_);
v___x_1258_ = l_Lean_Elab_Tactic_Do_countUses(v_ty_1249_, v_subst_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1314_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1261_ = v___x_1258_;
v_isShared_1262_ = v_isSharedCheck_1314_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1258_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1314_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v_fst_1263_; lean_object* v_snd_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1313_; 
v_fst_1263_ = lean_ctor_get(v_a_1259_, 0);
v_snd_1264_ = lean_ctor_get(v_a_1259_, 1);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_a_1259_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1266_ = v_a_1259_;
v_isShared_1267_ = v_isSharedCheck_1313_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_snd_1264_);
lean_inc(v_fst_1263_);
lean_dec(v_a_1259_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1313_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
uint8_t v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v_fst_1286_; lean_object* v_snd_1287_; 
if (lean_obj_tag(v_val_x3f_1250_) == 0)
{
lean_object* v___x_1297_; 
lean_dec_ref(v_subst_1252_);
v___x_1297_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__4);
v_fst_1286_ = v_val_x3f_1250_;
v_snd_1287_ = v___x_1297_;
goto v___jp_1285_;
}
else
{
lean_object* v_val_1298_; lean_object* v___x_1299_; 
v_val_1298_ = lean_ctor_get(v_val_x3f_1250_, 0);
lean_inc(v_val_1298_);
lean_dec_ref_known(v_val_x3f_1250_, 1);
v___x_1299_ = l_Lean_Elab_Tactic_Do_countUses(v_val_1298_, v_subst_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___f_1301_; lean_object* v___x_1302_; lean_object* v_fst_1303_; lean_object* v_snd_1304_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref_known(v___x_1299_, 1);
v___f_1301_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__5));
v___x_1302_ = l_Lean_Elab_Tactic_Do_over1Of2___redArg(v___f_1301_, v_a_1300_);
v_fst_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_fst_1303_);
v_snd_1304_ = lean_ctor_get(v___x_1302_, 1);
lean_inc(v_snd_1304_);
lean_dec_ref(v___x_1302_);
v_fst_1286_ = v_fst_1303_;
v_snd_1287_ = v_snd_1304_;
goto v___jp_1285_;
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_del_object(v___x_1266_);
lean_dec(v_snd_1264_);
lean_dec(v_fst_1263_);
lean_del_object(v___x_1261_);
lean_dec_ref(v_bodyUses_1251_);
v_a_1305_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1299_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1299_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
v___jp_1268_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1272_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v___y_1271_, v_fvarId_1248_);
v___x_1273_ = lean_box(0);
v___x_1274_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_1275_ = l_Lean_Elab_Tactic_Do_Uses_toNat(v___y_1269_);
v___x_1276_ = l_Lean_KVMap_setNat(v___x_1273_, v___x_1274_, v___x_1275_);
v___x_1277_ = l_Lean_Elab_Tactic_Do_addMData(v___x_1276_, v_fst_1263_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v___x_1272_);
lean_ctor_set(v___x_1266_, 0, v___y_1270_);
v___x_1279_ = v___x_1266_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___y_1270_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___x_1272_);
v___x_1279_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1277_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v___x_1280_);
v___x_1282_ = v___x_1261_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
v___jp_1285_:
{
uint8_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; uint8_t v___x_1292_; 
v___x_1288_ = 0;
v___x_1289_ = lean_box(v___x_1288_);
v___x_1290_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_bodyUses_1251_, v_fvarId_1248_, v___x_1289_);
lean_dec(v___x_1289_);
v___x_1291_ = lean_unbox(v___x_1290_);
v___x_1292_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v___x_1291_, v___x_1288_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1293_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_snd_1264_, v_bodyUses_1251_);
lean_dec_ref(v_bodyUses_1251_);
v___x_1294_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Elab_Tactic_Do_FVarUses_add_spec__2(v_snd_1287_, v___x_1293_);
lean_dec_ref(v___x_1293_);
v___x_1295_ = lean_unbox(v___x_1290_);
lean_dec(v___x_1290_);
v___y_1269_ = v___x_1295_;
v___y_1270_ = v_fst_1286_;
v___y_1271_ = v___x_1294_;
goto v___jp_1268_;
}
else
{
uint8_t v___x_1296_; 
lean_dec_ref(v_snd_1287_);
lean_dec(v_snd_1264_);
v___x_1296_ = lean_unbox(v___x_1290_);
lean_dec(v___x_1290_);
v___y_1269_ = v___x_1296_;
v___y_1270_ = v_fst_1286_;
v___y_1271_ = v_bodyUses_1251_;
goto v___jp_1268_;
}
}
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec_ref(v_subst_1252_);
lean_dec_ref(v_bodyUses_1251_);
lean_dec(v_val_x3f_1250_);
v_a_1315_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1258_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1258_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesDecl___boxed(lean_object* v_fvarId_1323_, lean_object* v_ty_1324_, lean_object* v_val_x3f_1325_, lean_object* v_bodyUses_1326_, lean_object* v_subst_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v_fvarId_1323_, v_ty_1324_, v_val_x3f_1325_, v_bodyUses_1326_, v_subst_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_fvarId_1323_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUses___boxed(lean_object* v_e_1334_, lean_object* v_subst_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_Elab_Tactic_Do_countUses(v_e_1334_, v_subst_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
lean_dec(v_a_1339_);
lean_dec_ref(v_a_1338_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(lean_object* v_00_u03b2_1342_, lean_object* v_m_1343_, lean_object* v_a_1344_, lean_object* v_fallback_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___redArg(v_m_1343_, v_a_1344_, v_fallback_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0___boxed(lean_object* v_00_u03b2_1347_, lean_object* v_m_1348_, lean_object* v_a_1349_, lean_object* v_fallback_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0(v_00_u03b2_1347_, v_m_1348_, v_a_1349_, v_fallback_1350_);
lean_dec(v_fallback_1350_);
lean_dec(v_a_1349_);
lean_dec_ref(v_m_1348_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(lean_object* v_00_u03b2_1352_, lean_object* v_m_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___redArg(v_m_1353_, v_a_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1___boxed(lean_object* v_00_u03b2_1356_, lean_object* v_m_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1(v_00_u03b2_1356_, v_m_1357_, v_a_1358_);
lean_dec(v_a_1358_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(lean_object* v_00_u03b1_1360_, lean_object* v_msg_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___redArg(v_msg_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3___boxed(lean_object* v_00_u03b1_1368_, lean_object* v_msg_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_countUses_spec__3(v_00_u03b1_1368_, v_msg_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___redArg(v___y_1379_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7___boxed(lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Elab_Tactic_Do_countUses_spec__4_spec__7(v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(lean_object* v_00_u03b2_1388_, lean_object* v_m_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___redArg(v_m_1389_, v_a_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1392_, lean_object* v_m_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__0_spec__0(v_00_u03b2_1392_, v_m_1393_, v_a_1394_);
lean_dec(v_a_1394_);
lean_dec_ref(v_m_1393_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(lean_object* v_00_u03b2_1396_, lean_object* v_m_1397_, lean_object* v_query_1398_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___redArg(v_m_1397_, v_query_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1400_, lean_object* v_m_1401_, lean_object* v_query_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Elab_Tactic_Do_countUsesDecl_spec__1_spec__2(v_00_u03b2_1400_, v_m_1401_, v_query_1402_);
lean_dec(v_query_1402_);
lean_dec_ref(v_m_1401_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(lean_object* v_as_1406_, size_t v_i_1407_, size_t v_stop_1408_, lean_object* v_b_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_usize_dec_eq(v_i_1407_, v_stop_1408_);
if (v___x_1415_ == 0)
{
size_t v___x_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = ((size_t)1ULL);
v___x_1417_ = lean_usize_sub(v_i_1407_, v___x_1416_);
v___x_1418_ = lean_array_uget_borrowed(v_as_1406_, v___x_1417_);
if (lean_obj_tag(v___x_1418_) == 0)
{
v_i_1407_ = v___x_1417_;
goto _start;
}
else
{
lean_object* v_val_1420_; lean_object* v_fst_1421_; lean_object* v_snd_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_val_1420_ = lean_ctor_get(v___x_1418_, 0);
v_fst_1421_ = lean_ctor_get(v_b_1409_, 0);
lean_inc(v_fst_1421_);
v_snd_1422_ = lean_ctor_get(v_b_1409_, 1);
lean_inc(v_snd_1422_);
lean_dec_ref(v_b_1409_);
v___x_1423_ = l_Lean_LocalDecl_fvarId(v_val_1420_);
v___x_1424_ = l_Lean_LocalDecl_type(v_val_1420_);
v___x_1425_ = l_Lean_LocalDecl_value_x3f(v_val_1420_, v___x_1415_);
v___x_1426_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_1427_ = l_Lean_Elab_Tactic_Do_countUsesDecl(v___x_1423_, v___x_1424_, v___x_1425_, v_snd_1422_, v___x_1426_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___x_1423_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v_snd_1429_; lean_object* v_fst_1430_; lean_object* v_fst_1431_; lean_object* v_snd_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1447_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___x_1427_, 1);
v_snd_1429_ = lean_ctor_get(v_a_1428_, 1);
lean_inc(v_snd_1429_);
v_fst_1430_ = lean_ctor_get(v_a_1428_, 0);
lean_inc(v_fst_1430_);
lean_dec(v_a_1428_);
v_fst_1431_ = lean_ctor_get(v_snd_1429_, 0);
v_snd_1432_ = lean_ctor_get(v_snd_1429_, 1);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_snd_1429_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1434_ = v_snd_1429_;
v_isShared_1435_ = v_isSharedCheck_1447_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_snd_1432_);
lean_inc(v_fst_1431_);
lean_dec(v_snd_1429_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1447_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___y_1437_; 
if (lean_obj_tag(v_fst_1431_) == 0)
{
lean_object* v___x_1443_; 
lean_inc(v_val_1420_);
v___x_1443_ = l_Lean_LocalDecl_setType(v_val_1420_, v_fst_1430_);
v___y_1437_ = v___x_1443_;
goto v___jp_1436_;
}
else
{
lean_object* v_val_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v_val_1444_ = lean_ctor_get(v_fst_1431_, 0);
lean_inc(v_val_1444_);
lean_dec_ref_known(v_fst_1431_, 1);
lean_inc(v_val_1420_);
v___x_1445_ = l_Lean_LocalDecl_setType(v_val_1420_, v_fst_1430_);
v___x_1446_ = l_Lean_LocalDecl_setValue(v___x_1445_, v_val_1444_);
v___y_1437_ = v___x_1446_;
goto v___jp_1436_;
}
v___jp_1436_:
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1438_ = lean_array_push(v_fst_1421_, v___y_1437_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1438_);
v___x_1440_ = v___x_1434_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_snd_1432_);
v___x_1440_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
v_i_1407_ = v___x_1417_;
v_b_1409_ = v___x_1440_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v_fst_1421_);
v_a_1448_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1427_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1427_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
else
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v_b_1409_);
return v___x_1456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1457_, lean_object* v_i_1458_, lean_object* v_stop_1459_, lean_object* v_b_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
size_t v_i_boxed_1466_; size_t v_stop_boxed_1467_; lean_object* v_res_1468_; 
v_i_boxed_1466_ = lean_unbox_usize(v_i_1458_);
lean_dec(v_i_1458_);
v_stop_boxed_1467_ = lean_unbox_usize(v_stop_1459_);
lean_dec(v_stop_1459_);
v_res_1468_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_as_1457_, v_i_boxed_1466_, v_stop_boxed_1467_, v_b_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec_ref(v_as_1457_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(lean_object* v_x_1469_, lean_object* v_x_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
if (lean_obj_tag(v_x_1469_) == 0)
{
lean_object* v_cs_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1489_; 
v_cs_1476_ = lean_ctor_get(v_x_1469_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_x_1469_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1478_ = v_x_1469_;
v_isShared_1479_ = v_isSharedCheck_1489_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_cs_1476_);
lean_dec(v_x_1469_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1489_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v___x_1480_ = lean_array_get_size(v_cs_1476_);
v___x_1481_ = lean_unsigned_to_nat(0u);
v___x_1482_ = lean_nat_dec_lt(v___x_1481_, v___x_1480_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1484_; 
lean_dec_ref(v_cs_1476_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v_x_1470_);
v___x_1484_ = v___x_1478_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_x_1470_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
else
{
size_t v___x_1486_; size_t v___x_1487_; lean_object* v___x_1488_; 
lean_del_object(v___x_1478_);
v___x_1486_ = lean_usize_of_nat(v___x_1480_);
v___x_1487_ = ((size_t)0ULL);
v___x_1488_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_cs_1476_, v___x_1486_, v___x_1487_, v_x_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec_ref(v_cs_1476_);
return v___x_1488_;
}
}
}
else
{
lean_object* v_vs_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1503_; 
v_vs_1490_ = lean_ctor_get(v_x_1469_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_x_1469_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1492_ = v_x_1469_;
v_isShared_1493_ = v_isSharedCheck_1503_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_vs_1490_);
lean_dec(v_x_1469_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1503_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1494_ = lean_array_get_size(v_vs_1490_);
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = lean_nat_dec_lt(v___x_1495_, v___x_1494_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1498_; 
lean_dec_ref(v_vs_1490_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set_tag(v___x_1492_, 0);
lean_ctor_set(v___x_1492_, 0, v_x_1470_);
v___x_1498_ = v___x_1492_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_x_1470_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
else
{
size_t v___x_1500_; size_t v___x_1501_; lean_object* v___x_1502_; 
lean_del_object(v___x_1492_);
v___x_1500_ = lean_usize_of_nat(v___x_1494_);
v___x_1501_ = ((size_t)0ULL);
v___x_1502_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_vs_1490_, v___x_1500_, v___x_1501_, v_x_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec_ref(v_vs_1490_);
return v___x_1502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(lean_object* v_as_1504_, size_t v_i_1505_, size_t v_stop_1506_, lean_object* v_b_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
uint8_t v___x_1513_; 
v___x_1513_ = lean_usize_dec_eq(v_i_1505_, v_stop_1506_);
if (v___x_1513_ == 0)
{
size_t v___x_1514_; size_t v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1514_ = ((size_t)1ULL);
v___x_1515_ = lean_usize_sub(v_i_1505_, v___x_1514_);
v___x_1516_ = lean_array_uget_borrowed(v_as_1504_, v___x_1515_);
lean_inc(v___x_1516_);
v___x_1517_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v___x_1516_, v_b_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
v_i_1505_ = v___x_1515_;
v_b_1507_ = v_a_1518_;
goto _start;
}
else
{
return v___x_1517_;
}
}
else
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v_b_1507_);
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_as_1521_, lean_object* v_i_1522_, lean_object* v_stop_1523_, lean_object* v_b_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
size_t v_i_boxed_1530_; size_t v_stop_boxed_1531_; lean_object* v_res_1532_; 
v_i_boxed_1530_ = lean_unbox_usize(v_i_1522_);
lean_dec(v_i_1522_);
v_stop_boxed_1531_ = lean_unbox_usize(v_stop_1523_);
lean_dec(v_stop_1523_);
v_res_1532_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1_spec__3(v_as_1521_, v_i_boxed_1530_, v_stop_boxed_1531_, v_b_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec_ref(v_as_1521_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1___boxed(lean_object* v_x_1533_, lean_object* v_x_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_x_1533_, v_x_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(lean_object* v_t_1541_, lean_object* v_init_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_root_1548_; lean_object* v_tail_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v_root_1548_ = lean_ctor_get(v_t_1541_, 0);
lean_inc_ref(v_root_1548_);
v_tail_1549_ = lean_ctor_get(v_t_1541_, 1);
lean_inc_ref(v_tail_1549_);
lean_dec_ref(v_t_1541_);
v___x_1550_ = lean_array_get_size(v_tail_1549_);
v___x_1551_ = lean_unsigned_to_nat(0u);
v___x_1552_ = lean_nat_dec_lt(v___x_1551_, v___x_1550_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
lean_dec_ref(v_tail_1549_);
v___x_1553_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1548_, v_init_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
return v___x_1553_;
}
else
{
size_t v___x_1554_; size_t v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = lean_usize_of_nat(v___x_1550_);
v___x_1555_ = ((size_t)0ULL);
v___x_1556_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2(v_tail_1549_, v___x_1554_, v___x_1555_, v_init_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
lean_dec_ref(v_tail_1549_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1558_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
v___x_1558_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__1(v_root_1548_, v_a_1557_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
return v___x_1558_;
}
else
{
lean_dec_ref(v_root_1548_);
return v___x_1556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0___boxed(lean_object* v_t_1559_, lean_object* v_init_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_t_1559_, v_init_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(lean_object* v_lctx_1567_, lean_object* v_init_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_decls_1574_; lean_object* v___x_1575_; 
v_decls_1574_ = lean_ctor_get(v_lctx_1567_, 1);
lean_inc_ref(v_decls_1574_);
lean_dec_ref(v_lctx_1567_);
v___x_1575_ = l_Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0(v_decls_1574_, v_init_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0___boxed(lean_object* v_lctx_1576_, lean_object* v_init_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_lctx_1576_, v_init_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(size_t v_sz_1584_, size_t v_i_1585_, lean_object* v_bs_1586_, lean_object* v___y_1587_){
_start:
{
uint8_t v___x_1589_; 
v___x_1589_ = lean_usize_dec_lt(v_i_1585_, v_sz_1584_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; 
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v_bs_1586_);
return v___x_1590_;
}
else
{
lean_object* v_v_1591_; lean_object* v___x_1592_; lean_object* v_bs_x27_1593_; lean_object* v_a_1595_; 
v_v_1591_ = lean_array_uget(v_bs_1586_, v_i_1585_);
v___x_1592_ = lean_unsigned_to_nat(0u);
v_bs_x27_1593_ = lean_array_uset(v_bs_1586_, v_i_1585_, v___x_1592_);
if (lean_obj_tag(v_v_1591_) == 0)
{
v_a_1595_ = v_v_1591_;
goto v___jp_1594_;
}
else
{
lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1614_; 
v_isSharedCheck_1614_ = !lean_is_exclusive(v_v_1591_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; 
v_unused_1615_ = lean_ctor_get(v_v_1591_, 0);
lean_dec(v_unused_1615_);
v___x_1601_ = v_v_1591_;
v_isShared_1602_ = v_isSharedCheck_1614_;
goto v_resetjp_1600_;
}
else
{
lean_dec(v_v_1591_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1614_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1603_ = lean_st_ref_take(v___y_1587_);
v___x_1604_ = l_Lean_instInhabitedLocalDecl_default;
v___x_1605_ = lean_array_get_size(v___x_1603_);
v___x_1606_ = lean_unsigned_to_nat(1u);
v___x_1607_ = lean_nat_sub(v___x_1605_, v___x_1606_);
v___x_1608_ = lean_array_get(v___x_1604_, v___x_1603_, v___x_1607_);
lean_dec(v___x_1607_);
v___x_1609_ = lean_array_pop(v___x_1603_);
v___x_1610_ = lean_st_ref_put(v___y_1587_, v___x_1609_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1608_);
v___x_1612_ = v___x_1601_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1608_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
v_a_1595_ = v___x_1612_;
goto v___jp_1594_;
}
}
}
v___jp_1594_:
{
size_t v___x_1596_; size_t v___x_1597_; lean_object* v___x_1598_; 
v___x_1596_ = ((size_t)1ULL);
v___x_1597_ = lean_usize_add(v_i_1585_, v___x_1596_);
v___x_1598_ = lean_array_uset(v_bs_x27_1593_, v_i_1585_, v_a_1595_);
v_i_1585_ = v___x_1597_;
v_bs_1586_ = v___x_1598_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg___boxed(lean_object* v_sz_1616_, lean_object* v_i_1617_, lean_object* v_bs_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
size_t v_sz_boxed_1621_; size_t v_i_boxed_1622_; lean_object* v_res_1623_; 
v_sz_boxed_1621_ = lean_unbox_usize(v_sz_1616_);
lean_dec(v_sz_1616_);
v_i_boxed_1622_ = lean_unbox_usize(v_i_1617_);
lean_dec(v_i_1617_);
v_res_1623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_boxed_1621_, v_i_boxed_1622_, v_bs_1618_, v___y_1619_);
lean_dec(v___y_1619_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(lean_object* v_x_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
if (lean_obj_tag(v_x_1624_) == 0)
{
lean_object* v_cs_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1657_; 
v_cs_1631_ = lean_ctor_get(v_x_1624_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_x_1624_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1633_ = v_x_1624_;
v_isShared_1634_ = v_isSharedCheck_1657_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_cs_1631_);
lean_dec(v_x_1624_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1657_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
size_t v_sz_1635_; size_t v___x_1636_; lean_object* v___x_1637_; 
v_sz_1635_ = lean_array_size(v_cs_1631_);
v___x_1636_ = ((size_t)0ULL);
v___x_1637_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_1635_, v___x_1636_, v_cs_1631_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1648_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1648_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1648_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v_a_1638_);
v___x_1643_ = v___x_1633_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1645_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1643_);
v___x_1645_ = v___x_1640_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_del_object(v___x_1633_);
v_a_1649_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1637_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1637_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
else
{
lean_object* v_vs_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1684_; 
v_vs_1658_ = lean_ctor_get(v_x_1624_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_x_1624_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1660_ = v_x_1624_;
v_isShared_1661_ = v_isSharedCheck_1684_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_vs_1658_);
lean_dec(v_x_1624_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1684_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
size_t v_sz_1662_; size_t v___x_1663_; lean_object* v___x_1664_; 
v_sz_1662_ = lean_array_size(v_vs_1658_);
v___x_1663_ = ((size_t)0ULL);
v___x_1664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1662_, v___x_1663_, v_vs_1658_, v___y_1625_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1675_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1667_ = v___x_1664_;
v_isShared_1668_ = v_isSharedCheck_1675_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1664_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1675_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v_a_1665_);
v___x_1670_ = v___x_1660_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1672_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1670_);
v___x_1672_ = v___x_1667_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_del_object(v___x_1660_);
v_a_1676_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1664_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1664_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(size_t v_sz_1685_, size_t v_i_1686_, lean_object* v_bs_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
uint8_t v___x_1694_; 
v___x_1694_ = lean_usize_dec_lt(v_i_1686_, v_sz_1685_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1695_, 0, v_bs_1687_);
return v___x_1695_;
}
else
{
lean_object* v_v_1696_; lean_object* v___x_1697_; 
v_v_1696_ = lean_array_uget_borrowed(v_bs_1687_, v_i_1686_);
lean_inc(v_v_1696_);
v___x_1697_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_v_1696_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1699_; lean_object* v_bs_x27_1700_; size_t v___x_1701_; size_t v___x_1702_; lean_object* v___x_1703_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1697_, 1);
v___x_1699_ = lean_unsigned_to_nat(0u);
v_bs_x27_1700_ = lean_array_uset(v_bs_1687_, v_i_1686_, v___x_1699_);
v___x_1701_ = ((size_t)1ULL);
v___x_1702_ = lean_usize_add(v_i_1686_, v___x_1701_);
v___x_1703_ = lean_array_uset(v_bs_x27_1700_, v_i_1686_, v_a_1698_);
v_i_1686_ = v___x_1702_;
v_bs_1687_ = v___x_1703_;
goto _start;
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec_ref(v_bs_1687_);
v_a_1705_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1697_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1697_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5___boxed(lean_object* v_sz_1713_, lean_object* v_i_1714_, lean_object* v_bs_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
size_t v_sz_boxed_1722_; size_t v_i_boxed_1723_; lean_object* v_res_1724_; 
v_sz_boxed_1722_ = lean_unbox_usize(v_sz_1713_);
lean_dec(v_sz_1713_);
v_i_boxed_1723_ = lean_unbox_usize(v_i_1714_);
lean_dec(v_i_1714_);
v_res_1724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2_spec__5(v_sz_boxed_1722_, v_i_boxed_1723_, v_bs_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2___boxed(lean_object* v_x_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_x_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(lean_object* v_t_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_root_1740_; lean_object* v_tail_1741_; lean_object* v_size_1742_; size_t v_shift_1743_; lean_object* v_tailOff_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1780_; 
v_root_1740_ = lean_ctor_get(v_t_1733_, 0);
v_tail_1741_ = lean_ctor_get(v_t_1733_, 1);
v_size_1742_ = lean_ctor_get(v_t_1733_, 2);
v_shift_1743_ = lean_ctor_get_usize(v_t_1733_, 4);
v_tailOff_1744_ = lean_ctor_get(v_t_1733_, 3);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_t_1733_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1746_ = v_t_1733_;
v_isShared_1747_ = v_isSharedCheck_1780_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_tailOff_1744_);
lean_inc(v_size_1742_);
lean_inc(v_tail_1741_);
lean_inc(v_root_1740_);
lean_dec(v_t_1733_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1780_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__2(v_root_1740_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; size_t v_sz_1750_; size_t v___x_1751_; lean_object* v___x_1752_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref_known(v___x_1748_, 1);
v_sz_1750_ = lean_array_size(v_tail_1741_);
v___x_1751_ = ((size_t)0ULL);
v___x_1752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1750_, v___x_1751_, v_tail_1741_, v___y_1734_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1763_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1763_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1763_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 1, v_a_1753_);
lean_ctor_set(v___x_1746_, 0, v_a_1749_);
v___x_1758_ = v___x_1746_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1749_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_a_1753_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_size_1742_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_tailOff_1744_);
lean_ctor_set_usize(v_reuseFailAlloc_1762_, 4, v_shift_1743_);
v___x_1758_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1760_; 
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1758_);
v___x_1760_ = v___x_1755_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec(v_a_1749_);
lean_del_object(v___x_1746_);
lean_dec(v_tailOff_1744_);
lean_dec(v_size_1742_);
v_a_1764_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1752_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1752_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_del_object(v___x_1746_);
lean_dec(v_tailOff_1744_);
lean_dec(v_size_1742_);
lean_dec_ref(v_tail_1741_);
v_a_1772_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1748_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1748_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1___boxed(lean_object* v_t_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_t_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx(lean_object* v_ctx_1789_, lean_object* v_targetUses_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_decls_1796_; lean_object* v_fvarIdToDecl_1797_; lean_object* v_auxDeclToFullName_1798_; lean_object* v_size_1799_; lean_object* v_decls_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v_decls_1796_ = lean_ctor_get(v_ctx_1789_, 1);
lean_inc_ref(v_decls_1796_);
v_fvarIdToDecl_1797_ = lean_ctor_get(v_ctx_1789_, 0);
lean_inc_ref(v_fvarIdToDecl_1797_);
v_auxDeclToFullName_1798_ = lean_ctor_get(v_ctx_1789_, 2);
lean_inc(v_auxDeclToFullName_1798_);
v_size_1799_ = lean_ctor_get(v_decls_1796_, 2);
v_decls_1800_ = lean_mk_empty_array_with_capacity(v_size_1799_);
v___x_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1801_, 0, v_decls_1800_);
lean_ctor_set(v___x_1801_, 1, v_targetUses_1790_);
v___x_1802_ = l_Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0(v_ctx_1789_, v___x_1801_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v_fst_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref_known(v___x_1802_, 1);
v_fst_1804_ = lean_ctor_get(v_a_1803_, 0);
lean_inc(v_fst_1804_);
lean_dec(v_a_1803_);
v___x_1805_ = lean_st_mk_ref(v_fst_1804_);
v___x_1806_ = l_Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1(v_decls_1796_, v___x_1805_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1816_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1816_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1816_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1811_ = lean_st_ref_get(v___x_1805_);
lean_dec(v___x_1805_);
lean_dec(v___x_1811_);
v___x_1812_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1812_, 0, v_fvarIdToDecl_1797_);
lean_ctor_set(v___x_1812_, 1, v_a_1807_);
lean_ctor_set(v___x_1812_, 2, v_auxDeclToFullName_1798_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1812_);
v___x_1814_ = v___x_1809_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec(v___x_1805_);
lean_dec(v_auxDeclToFullName_1798_);
lean_dec_ref(v_fvarIdToDecl_1797_);
v_a_1817_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1806_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1806_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_dec(v_auxDeclToFullName_1798_);
lean_dec_ref(v_fvarIdToDecl_1797_);
lean_dec_ref(v_decls_1796_);
v_a_1825_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1802_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1802_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_countUsesLCtx___boxed(lean_object* v_ctx_1833_, lean_object* v_targetUses_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_ctx_1833_, v_targetUses_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(size_t v_sz_1841_, size_t v_i_1842_, lean_object* v_bs_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___redArg(v_sz_1841_, v_i_1842_, v_bs_1843_, v___y_1844_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3___boxed(lean_object* v_sz_1851_, lean_object* v_i_1852_, lean_object* v_bs_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
size_t v_sz_boxed_1860_; size_t v_i_boxed_1861_; lean_object* v_res_1862_; 
v_sz_boxed_1860_ = lean_unbox_usize(v_sz_1851_);
lean_dec(v_sz_1851_);
v_i_boxed_1861_ = lean_unbox_usize(v_i_1852_);
lean_dec(v_i_1852_);
v_res_1862_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__1_spec__3(v_sz_boxed_1860_, v_i_boxed_1861_, v_bs_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
return v_res_1862_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_doNotDup(uint8_t v_u_1863_, lean_object* v_rhs_1864_, uint8_t v_elimTrivial_1865_){
_start:
{
uint8_t v___x_1866_; uint8_t v___x_1867_; 
v___x_1866_ = 2;
v___x_1867_ = l_Lean_Elab_Tactic_Do_instBEqUses_beq(v_u_1863_, v___x_1866_);
if (v___x_1867_ == 0)
{
return v___x_1867_;
}
else
{
if (v_elimTrivial_1865_ == 0)
{
return v___x_1867_;
}
else
{
uint8_t v___x_1868_; 
v___x_1868_ = l___private_Lean_Elab_Tactic_Do_LetElim_0__Lean_Elab_Tactic_Do_okToDup(v_rhs_1864_);
if (v___x_1868_ == 0)
{
return v___x_1867_;
}
else
{
uint8_t v___x_1869_; 
v___x_1869_ = 0;
return v___x_1869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_doNotDup___boxed(lean_object* v_u_1870_, lean_object* v_rhs_1871_, lean_object* v_elimTrivial_1872_){
_start:
{
uint8_t v_u_boxed_1873_; uint8_t v_elimTrivial_boxed_1874_; uint8_t v_res_1875_; lean_object* v_r_1876_; 
v_u_boxed_1873_ = lean_unbox(v_u_1870_);
v_elimTrivial_boxed_1874_ = lean_unbox(v_elimTrivial_1872_);
v_res_1875_ = l_Lean_Elab_Tactic_Do_doNotDup(v_u_boxed_1873_, v_rhs_1871_, v_elimTrivial_boxed_1874_);
lean_dec_ref(v_rhs_1871_);
v_r_1876_ = lean_box(v_res_1875_);
return v_r_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(uint8_t v_elimTrivial_1879_, lean_object* v_e_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
if (lean_obj_tag(v_e_1880_) == 8)
{
lean_object* v_type_1887_; 
v_type_1887_ = lean_ctor_get(v_e_1880_, 1);
if (lean_obj_tag(v_type_1887_) == 10)
{
lean_object* v_value_1888_; lean_object* v_body_1889_; lean_object* v_data_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v_uses_1894_; uint8_t v___x_1895_; 
v_value_1888_ = lean_ctor_get(v_e_1880_, 2);
v_body_1889_ = lean_ctor_get(v_e_1880_, 3);
v_data_1890_ = lean_ctor_get(v_type_1887_, 0);
v___x_1891_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_1892_ = lean_unsigned_to_nat(2u);
v___x_1893_ = l_Lean_KVMap_getNat(v_data_1890_, v___x_1891_, v___x_1892_);
v_uses_1894_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_1893_);
lean_dec(v___x_1893_);
v___x_1895_ = l_Lean_Elab_Tactic_Do_doNotDup(v_uses_1894_, v_value_1888_, v_elimTrivial_1879_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1896_ = lean_expr_instantiate1(v_body_1889_, v_value_1888_);
v___x_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
return v___x_1898_;
}
else
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
return v___x_1902_;
}
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___closed__0));
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
return v___x_1904_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed(lean_object* v_elimTrivial_1905_, lean_object* v_e_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
uint8_t v_elimTrivial_boxed_1913_; lean_object* v_res_1914_; 
v_elimTrivial_boxed_1913_ = lean_unbox(v_elimTrivial_1905_);
v_res_1914_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0(v_elimTrivial_boxed_1913_, v_e_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v_e_1906_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(lean_object* v_e_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v_e_1915_);
v___x_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1___boxed(lean_object* v_e_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_Elab_Tactic_Do_elimLetsCore___lam__1(v_e_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
return v_res_1931_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = l_Lean_maxRecDepthErrorMessage;
v___x_1938_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
return v___x_1938_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__3);
v___x_1940_ = l_Lean_MessageData_ofFormat(v___x_1939_);
return v___x_1940_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1941_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__4);
v___x_1942_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__2));
v___x_1943_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
lean_ctor_set(v___x_1943_, 1, v___x_1941_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(lean_object* v_ref_1944_){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___closed__5);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v_ref_1944_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg___boxed(lean_object* v_ref_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1949_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(lean_object* v_x_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___y_1961_; lean_object* v_fileName_1970_; lean_object* v_fileMap_1971_; lean_object* v_options_1972_; lean_object* v_currRecDepth_1973_; lean_object* v_maxRecDepth_1974_; lean_object* v_ref_1975_; lean_object* v_currNamespace_1976_; lean_object* v_openDecls_1977_; lean_object* v_initHeartbeats_1978_; lean_object* v_maxHeartbeats_1979_; lean_object* v_quotContext_1980_; lean_object* v_currMacroScope_1981_; uint8_t v_diag_1982_; lean_object* v_cancelTk_x3f_1983_; uint8_t v_suppressElabErrors_1984_; lean_object* v_inheritedTraceOptions_1985_; lean_object* v___x_1991_; uint8_t v___x_1992_; 
v_fileName_1970_ = lean_ctor_get(v___y_1957_, 0);
v_fileMap_1971_ = lean_ctor_get(v___y_1957_, 1);
v_options_1972_ = lean_ctor_get(v___y_1957_, 2);
v_currRecDepth_1973_ = lean_ctor_get(v___y_1957_, 3);
v_maxRecDepth_1974_ = lean_ctor_get(v___y_1957_, 4);
v_ref_1975_ = lean_ctor_get(v___y_1957_, 5);
v_currNamespace_1976_ = lean_ctor_get(v___y_1957_, 6);
v_openDecls_1977_ = lean_ctor_get(v___y_1957_, 7);
v_initHeartbeats_1978_ = lean_ctor_get(v___y_1957_, 8);
v_maxHeartbeats_1979_ = lean_ctor_get(v___y_1957_, 9);
v_quotContext_1980_ = lean_ctor_get(v___y_1957_, 10);
v_currMacroScope_1981_ = lean_ctor_get(v___y_1957_, 11);
v_diag_1982_ = lean_ctor_get_uint8(v___y_1957_, sizeof(void*)*14);
v_cancelTk_x3f_1983_ = lean_ctor_get(v___y_1957_, 12);
v_suppressElabErrors_1984_ = lean_ctor_get_uint8(v___y_1957_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1985_ = lean_ctor_get(v___y_1957_, 13);
v___x_1991_ = lean_unsigned_to_nat(0u);
v___x_1992_ = lean_nat_dec_eq(v_maxRecDepth_1974_, v___x_1991_);
if (v___x_1992_ == 0)
{
uint8_t v___x_1993_; 
v___x_1993_ = lean_nat_dec_eq(v_currRecDepth_1973_, v_maxRecDepth_1974_);
if (v___x_1993_ == 0)
{
goto v___jp_1986_;
}
else
{
lean_object* v___x_1994_; 
lean_dec_ref(v_x_1952_);
lean_inc(v_ref_1975_);
v___x_1994_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_1975_);
v___y_1961_ = v___x_1994_;
goto v___jp_1960_;
}
}
else
{
goto v___jp_1986_;
}
v___jp_1960_:
{
if (lean_obj_tag(v___y_1961_) == 0)
{
return v___y_1961_;
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
v_a_1962_ = lean_ctor_get(v___y_1961_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___y_1961_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___y_1961_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___y_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
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
v___jp_1986_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1987_ = lean_unsigned_to_nat(1u);
v___x_1988_ = lean_nat_add(v_currRecDepth_1973_, v___x_1987_);
lean_inc_ref(v_inheritedTraceOptions_1985_);
lean_inc(v_cancelTk_x3f_1983_);
lean_inc(v_currMacroScope_1981_);
lean_inc(v_quotContext_1980_);
lean_inc(v_maxHeartbeats_1979_);
lean_inc(v_initHeartbeats_1978_);
lean_inc(v_openDecls_1977_);
lean_inc(v_currNamespace_1976_);
lean_inc(v_ref_1975_);
lean_inc(v_maxRecDepth_1974_);
lean_inc_ref(v_options_1972_);
lean_inc_ref(v_fileMap_1971_);
lean_inc_ref(v_fileName_1970_);
v___x_1989_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1989_, 0, v_fileName_1970_);
lean_ctor_set(v___x_1989_, 1, v_fileMap_1971_);
lean_ctor_set(v___x_1989_, 2, v_options_1972_);
lean_ctor_set(v___x_1989_, 3, v___x_1988_);
lean_ctor_set(v___x_1989_, 4, v_maxRecDepth_1974_);
lean_ctor_set(v___x_1989_, 5, v_ref_1975_);
lean_ctor_set(v___x_1989_, 6, v_currNamespace_1976_);
lean_ctor_set(v___x_1989_, 7, v_openDecls_1977_);
lean_ctor_set(v___x_1989_, 8, v_initHeartbeats_1978_);
lean_ctor_set(v___x_1989_, 9, v_maxHeartbeats_1979_);
lean_ctor_set(v___x_1989_, 10, v_quotContext_1980_);
lean_ctor_set(v___x_1989_, 11, v_currMacroScope_1981_);
lean_ctor_set(v___x_1989_, 12, v_cancelTk_x3f_1983_);
lean_ctor_set(v___x_1989_, 13, v_inheritedTraceOptions_1985_);
lean_ctor_set_uint8(v___x_1989_, sizeof(void*)*14, v_diag_1982_);
lean_ctor_set_uint8(v___x_1989_, sizeof(void*)*14 + 1, v_suppressElabErrors_1984_);
lean_inc(v___y_1958_);
lean_inc(v___y_1956_);
lean_inc_ref(v___y_1955_);
lean_inc(v___y_1954_);
lean_inc(v___y_1953_);
v___x_1990_ = lean_apply_7(v_x_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___x_1989_, v___y_1958_, lean_box(0));
v___y_1961_ = v___x_1990_;
goto v___jp_1960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg___boxed(lean_object* v_x_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec(v___y_1996_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(lean_object* v_m_2004_, lean_object* v_query_2005_, lean_object* v_x_2006_, lean_object* v_x_2007_, lean_object* v_x_2008_){
_start:
{
lean_object* v_zero_2009_; uint8_t v_isZero_2010_; 
v_zero_2009_ = lean_unsigned_to_nat(0u);
v_isZero_2010_ = lean_nat_dec_eq(v_x_2007_, v_zero_2009_);
if (v_isZero_2010_ == 1)
{
lean_dec(v_x_2008_);
lean_dec(v_x_2007_);
if (lean_obj_tag(v_x_2006_) == 0)
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_box(2);
return v___x_2011_;
}
else
{
lean_object* v_val_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
v_val_2012_ = lean_ctor_get(v_x_2006_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_x_2006_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v_x_2006_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_val_2012_);
lean_dec(v_x_2006_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_val_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
else
{
lean_object* v_keyArray_2020_; lean_object* v_valueArray_2021_; lean_object* v___x_2022_; uint8_t v_isSome_2023_; 
v_keyArray_2020_ = lean_ctor_get(v_m_2004_, 1);
v_valueArray_2021_ = lean_ctor_get(v_m_2004_, 2);
v___x_2022_ = lean_array_fget_borrowed(v_keyArray_2020_, v_x_2008_);
v_isSome_2023_ = lean_noption_is_some(v___x_2022_);
if (v_isSome_2023_ == 0)
{
lean_dec(v_x_2007_);
if (lean_obj_tag(v_x_2006_) == 0)
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2024_, 0, v_x_2008_);
return v___x_2024_;
}
else
{
lean_object* v_val_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec(v_x_2008_);
v_val_2025_ = lean_ctor_get(v_x_2006_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_x_2006_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v_x_2006_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_val_2025_);
lean_dec(v_x_2006_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_val_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_object* v_one_2033_; lean_object* v_n_2034_; lean_object* v___y_2036_; 
v_one_2033_ = lean_unsigned_to_nat(1u);
v_n_2034_ = lean_nat_sub(v_x_2007_, v_one_2033_);
lean_dec(v_x_2007_);
if (v_isSome_2023_ == 0)
{
goto v___jp_2042_;
}
else
{
lean_object* v___x_2044_; uint8_t v_isSome_2045_; 
v___x_2044_ = lean_array_fget_borrowed(v_valueArray_2021_, v_x_2008_);
v_isSome_2045_ = lean_noption_is_some(v___x_2044_);
if (v_isSome_2045_ == 0)
{
goto v___jp_2042_;
}
else
{
lean_object* v_val_2046_; uint8_t v___x_2047_; 
lean_inc(v___x_2022_);
v_val_2046_ = lean_noption_get(v___x_2022_);
v___x_2047_ = l_Lean_ExprStructEq_beq(v_val_2046_, v_query_2005_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
lean_dec(v_val_2046_);
v___x_2048_ = lean_array_get_size(v_keyArray_2020_);
v___x_2049_ = lean_nat_add(v_x_2008_, v_one_2033_);
lean_dec(v_x_2008_);
v___x_2050_ = lean_nat_dec_lt(v___x_2049_, v___x_2048_);
if (v___x_2050_ == 0)
{
lean_dec(v___x_2049_);
v_x_2007_ = v_n_2034_;
v_x_2008_ = v_zero_2009_;
goto _start;
}
else
{
v_x_2007_ = v_n_2034_;
v_x_2008_ = v___x_2049_;
goto _start;
}
}
else
{
lean_object* v_val_2053_; lean_object* v___x_2054_; 
lean_dec(v_n_2034_);
lean_dec(v_x_2006_);
lean_inc(v___x_2044_);
v_val_2053_ = lean_noption_get(v___x_2044_);
v___x_2054_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2054_, 0, v_x_2008_);
lean_ctor_set(v___x_2054_, 1, v_val_2046_);
lean_ctor_set(v___x_2054_, 2, v_val_2053_);
return v___x_2054_;
}
}
}
v___jp_2035_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2037_ = lean_array_get_size(v_keyArray_2020_);
v___x_2038_ = lean_nat_add(v_x_2008_, v_one_2033_);
lean_dec(v_x_2008_);
v___x_2039_ = lean_nat_dec_lt(v___x_2038_, v___x_2037_);
if (v___x_2039_ == 0)
{
lean_dec(v___x_2038_);
v_x_2006_ = v___y_2036_;
v_x_2007_ = v_n_2034_;
v_x_2008_ = v_zero_2009_;
goto _start;
}
else
{
v_x_2006_ = v___y_2036_;
v_x_2007_ = v_n_2034_;
v_x_2008_ = v___x_2038_;
goto _start;
}
}
v___jp_2042_:
{
if (lean_obj_tag(v_x_2006_) == 0)
{
lean_object* v___x_2043_; 
lean_inc(v_x_2008_);
v___x_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2043_, 0, v_x_2008_);
v___y_2036_ = v___x_2043_;
goto v___jp_2035_;
}
else
{
v___y_2036_ = v_x_2006_;
goto v___jp_2035_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg___boxed(lean_object* v_m_2055_, lean_object* v_query_2056_, lean_object* v_x_2057_, lean_object* v_x_2058_, lean_object* v_x_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_m_2055_, v_query_2056_, v_x_2057_, v_x_2058_, v_x_2059_);
lean_dec_ref(v_query_2056_);
lean_dec_ref(v_m_2055_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(lean_object* v_m_2061_, lean_object* v_query_2062_){
_start:
{
lean_object* v_keyArray_2063_; lean_object* v___x_2064_; uint64_t v___x_2065_; uint64_t v___x_2066_; uint64_t v___x_2067_; uint64_t v_fold_2068_; uint64_t v___x_2069_; uint64_t v___x_2070_; uint64_t v___x_2071_; size_t v___x_2072_; size_t v___x_2073_; size_t v___x_2074_; size_t v___x_2075_; size_t v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v_keyArray_2063_ = lean_ctor_get(v_m_2061_, 1);
v___x_2064_ = lean_array_get_size(v_keyArray_2063_);
v___x_2065_ = l_Lean_ExprStructEq_hash(v_query_2062_);
v___x_2066_ = 32ULL;
v___x_2067_ = lean_uint64_shift_right(v___x_2065_, v___x_2066_);
v_fold_2068_ = lean_uint64_xor(v___x_2065_, v___x_2067_);
v___x_2069_ = 16ULL;
v___x_2070_ = lean_uint64_shift_right(v_fold_2068_, v___x_2069_);
v___x_2071_ = lean_uint64_xor(v_fold_2068_, v___x_2070_);
v___x_2072_ = lean_uint64_to_usize(v___x_2071_);
v___x_2073_ = lean_usize_of_nat(v___x_2064_);
v___x_2074_ = ((size_t)1ULL);
v___x_2075_ = lean_usize_sub(v___x_2073_, v___x_2074_);
v___x_2076_ = lean_usize_land(v___x_2072_, v___x_2075_);
v___x_2077_ = lean_usize_to_nat(v___x_2076_);
v___x_2078_ = lean_box(0);
v___x_2079_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_m_2061_, v_query_2062_, v___x_2078_, v___x_2064_, v___x_2077_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg___boxed(lean_object* v_m_2080_, lean_object* v_query_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v_m_2080_, v_query_2081_);
lean_dec_ref(v_query_2081_);
lean_dec_ref(v_m_2080_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(lean_object* v_m_2083_, lean_object* v_query_2084_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v_m_2083_, v_query_2084_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_index_2086_; lean_object* v_key_2087_; lean_object* v_value_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
v_index_2086_ = lean_ctor_get(v___x_2085_, 0);
v_key_2087_ = lean_ctor_get(v___x_2085_, 1);
v_value_2088_ = lean_ctor_get(v___x_2085_, 2);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2085_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_value_2088_);
lean_inc(v_key_2087_);
lean_inc(v_index_2086_);
lean_dec(v___x_2085_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_index_2086_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_key_2087_);
lean_ctor_set(v_reuseFailAlloc_2094_, 2, v_value_2088_);
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
lean_object* v___x_2096_; 
lean_dec(v___x_2085_);
v___x_2096_ = lean_box(1);
return v___x_2096_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg___boxed(lean_object* v_m_2097_, lean_object* v_query_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_m_2097_, v_query_2098_);
lean_dec_ref(v_query_2098_);
lean_dec_ref(v_m_2097_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(lean_object* v_m_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_m_2100_, v_a_2101_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_value_2103_; lean_object* v___x_2104_; 
v_value_2103_ = lean_ctor_get(v___x_2102_, 2);
lean_inc(v_value_2103_);
lean_dec_ref_known(v___x_2102_, 3);
v___x_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2104_, 0, v_value_2103_);
return v___x_2104_;
}
else
{
lean_object* v___x_2105_; 
v___x_2105_ = lean_box(0);
return v___x_2105_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_m_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_2106_, v_a_2107_);
lean_dec_ref(v_a_2107_);
lean_dec_ref(v_m_2106_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(lean_object* v_k_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v_b_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2118_; 
lean_inc(v___y_2116_);
lean_inc_ref(v___y_2115_);
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
lean_inc(v___y_2111_);
lean_inc(v___y_2110_);
v___x_2118_ = lean_apply_8(v_k_2109_, v_b_2112_, v___y_2110_, v___y_2111_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, lean_box(0));
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v_b_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0(v_k_2119_, v___y_2120_, v___y_2121_, v_b_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2121_);
lean_dec(v___y_2120_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(lean_object* v_name_2129_, lean_object* v_type_2130_, lean_object* v_val_2131_, lean_object* v_k_2132_, uint8_t v_nondep_2133_, uint8_t v_kind_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v___f_2142_; lean_object* v___x_2143_; 
lean_inc(v___y_2136_);
lean_inc(v___y_2135_);
v___f_2142_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2142_, 0, v_k_2132_);
lean_closure_set(v___f_2142_, 1, v___y_2135_);
lean_closure_set(v___f_2142_, 2, v___y_2136_);
v___x_2143_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2129_, v_type_2130_, v_val_2131_, v___f_2142_, v_nondep_2133_, v_kind_2134_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
if (lean_obj_tag(v___x_2143_) == 0)
{
return v___x_2143_;
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg___boxed(lean_object* v_name_2152_, lean_object* v_type_2153_, lean_object* v_val_2154_, lean_object* v_k_2155_, lean_object* v_nondep_2156_, lean_object* v_kind_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
uint8_t v_nondep_boxed_2165_; uint8_t v_kind_boxed_2166_; lean_object* v_res_2167_; 
v_nondep_boxed_2165_ = lean_unbox(v_nondep_2156_);
v_kind_boxed_2166_ = lean_unbox(v_kind_2157_);
v_res_2167_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_2152_, v_type_2153_, v_val_2154_, v_k_2155_, v_nondep_boxed_2165_, v_kind_boxed_2166_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec(v___y_2158_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_name_2168_, uint8_t v_bi_2169_, lean_object* v_type_2170_, lean_object* v_k_2171_, uint8_t v_kind_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v___f_2180_; lean_object* v___x_2181_; 
lean_inc(v___y_2174_);
lean_inc(v___y_2173_);
v___f_2180_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2180_, 0, v_k_2171_);
lean_closure_set(v___f_2180_, 1, v___y_2173_);
lean_closure_set(v___f_2180_, 2, v___y_2174_);
v___x_2181_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2168_, v_bi_2169_, v_type_2170_, v___f_2180_, v_kind_2172_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
if (lean_obj_tag(v___x_2181_) == 0)
{
return v___x_2181_;
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_name_2190_, lean_object* v_bi_2191_, lean_object* v_type_2192_, lean_object* v_k_2193_, lean_object* v_kind_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
uint8_t v_bi_boxed_2202_; uint8_t v_kind_boxed_2203_; lean_object* v_res_2204_; 
v_bi_boxed_2202_ = lean_unbox(v_bi_2191_);
v_kind_boxed_2203_ = lean_unbox(v_kind_2194_);
v_res_2204_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_2190_, v_bi_boxed_2202_, v_type_2192_, v_k_2193_, v_kind_boxed_2203_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec(v___y_2195_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(lean_object* v___x_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2205_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed(lean_object* v___x_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2(v___x_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2221_, lean_object* v_x_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_apply_1(v_x_2222_, lean_box(0));
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2231_, lean_object* v_x_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(v_00_u03b1_2231_, v_x_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17_spec__18___redArg(lean_object* v_b_2240_, lean_object* v_acc_2241_, lean_object* v_i_2242_){
_start:
{
lean_object* v___y_2244_; lean_object* v_keyArray_2252_; lean_object* v_valueArray_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; 
v_keyArray_2252_ = lean_ctor_get(v_b_2240_, 1);
v_valueArray_2253_ = lean_ctor_get(v_b_2240_, 2);
v___x_2254_ = lean_array_get_size(v_keyArray_2252_);
v___x_2255_ = lean_nat_dec_lt(v_i_2242_, v___x_2254_);
if (v___x_2255_ == 0)
{
lean_dec(v_i_2242_);
return v_acc_2241_;
}
else
{
lean_object* v___x_2256_; uint8_t v_isSome_2257_; 
v___x_2256_ = lean_array_fget_borrowed(v_keyArray_2252_, v_i_2242_);
v_isSome_2257_ = lean_noption_is_some(v___x_2256_);
if (v_isSome_2257_ == 0)
{
goto v___jp_2248_;
}
else
{
lean_object* v___x_2258_; uint8_t v_isSome_2259_; 
v___x_2258_ = lean_array_fget_borrowed(v_valueArray_2253_, v_i_2242_);
v_isSome_2259_ = lean_noption_is_some(v___x_2258_);
if (v_isSome_2259_ == 0)
{
goto v___jp_2248_;
}
else
{
lean_object* v_val_2260_; lean_object* v_val_2261_; lean_object* v_i_2263_; lean_object* v___x_2268_; 
lean_inc(v___x_2256_);
v_val_2260_ = lean_noption_get(v___x_2256_);
lean_inc(v___x_2258_);
v_val_2261_ = lean_noption_get(v___x_2258_);
v___x_2268_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v_acc_2241_, v_val_2260_);
switch(lean_obj_tag(v___x_2268_))
{
case 0:
{
lean_object* v_index_2269_; lean_object* v_size_2270_; lean_object* v___x_2271_; 
v_index_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_index_2269_);
lean_dec_ref_known(v___x_2268_, 3);
v_size_2270_ = lean_ctor_get(v_acc_2241_, 0);
lean_inc(v_size_2270_);
v___x_2271_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2241_, v_size_2270_, v_index_2269_, v_val_2260_, v_val_2261_);
lean_dec(v_index_2269_);
v___y_2244_ = v___x_2271_;
goto v___jp_2243_;
}
case 1:
{
lean_object* v_index_2272_; 
v_index_2272_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_index_2272_);
lean_dec_ref_known(v___x_2268_, 1);
v_i_2263_ = v_index_2272_;
goto v___jp_2262_;
}
default: 
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_2241_, v___x_2273_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_index_2275_; 
v_index_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_index_2275_);
lean_dec_ref_known(v___x_2274_, 1);
v_i_2263_ = v_index_2275_;
goto v___jp_2262_;
}
else
{
lean_dec(v_val_2261_);
lean_dec(v_val_2260_);
v___y_2244_ = v_acc_2241_;
goto v___jp_2243_;
}
}
}
v___jp_2262_:
{
lean_object* v_size_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v_size_2264_ = lean_ctor_get(v_acc_2241_, 0);
v___x_2265_ = lean_unsigned_to_nat(1u);
v___x_2266_ = lean_nat_add(v_size_2264_, v___x_2265_);
v___x_2267_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2241_, v___x_2266_, v_i_2263_, v_val_2260_, v_val_2261_);
lean_dec(v_i_2263_);
v___y_2244_ = v___x_2267_;
goto v___jp_2243_;
}
}
}
}
v___jp_2243_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = lean_unsigned_to_nat(1u);
v___x_2246_ = lean_nat_add(v_i_2242_, v___x_2245_);
lean_dec(v_i_2242_);
v_acc_2241_ = v___y_2244_;
v_i_2242_ = v___x_2246_;
goto _start;
}
v___jp_2248_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = lean_unsigned_to_nat(1u);
v___x_2250_ = lean_nat_add(v_i_2242_, v___x_2249_);
lean_dec(v_i_2242_);
v_i_2242_ = v___x_2250_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17_spec__18___redArg___boxed(lean_object* v_b_2276_, lean_object* v_acc_2277_, lean_object* v_i_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17_spec__18___redArg(v_b_2276_, v_acc_2277_, v_i_2278_);
lean_dec_ref(v_b_2276_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17___redArg(lean_object* v_init_2280_, lean_object* v_b_2281_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17_spec__18___redArg(v_b_2281_, v_init_2280_, v___x_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17___redArg___boxed(lean_object* v_init_2284_, lean_object* v_b_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17___redArg(v_init_2284_, v_b_2285_);
lean_dec_ref(v_b_2285_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11___redArg(lean_object* v_m_2287_){
_start:
{
lean_object* v_keyArray_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v_cellCount_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v_target_2295_; lean_object* v___x_2296_; 
v_keyArray_2288_ = lean_ctor_get(v_m_2287_, 1);
v___x_2289_ = lean_array_get_size(v_keyArray_2288_);
v___x_2290_ = lean_unsigned_to_nat(2u);
v_cellCount_2291_ = lean_nat_mul(v___x_2289_, v___x_2290_);
v___x_2292_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_2291_);
v___x_2293_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2291_);
v___x_2294_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2291_);
v_target_2295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_2295_, 0, v___x_2292_);
lean_ctor_set(v_target_2295_, 1, v___x_2293_);
lean_ctor_set(v_target_2295_, 2, v___x_2294_);
v___x_2296_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17___redArg(v_target_2295_, v_m_2287_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11___redArg___boxed(lean_object* v_m_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11___redArg(v_m_2297_);
lean_dec_ref(v_m_2297_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(lean_object* v_a_2299_, lean_object* v_e_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___y_2306_; lean_object* v___y_2309_; lean_object* v_i_2310_; lean_object* v___y_2326_; lean_object* v_i_2327_; lean_object* v___y_2333_; lean_object* v___x_2342_; 
v___x_2303_ = lean_st_ref_take(v_a_2299_);
v___x_2304_ = lean_box(0);
v___x_2342_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v___x_2303_, v_e_2300_);
switch(lean_obj_tag(v___x_2342_))
{
case 0:
{
lean_object* v_index_2343_; lean_object* v_size_2344_; lean_object* v___x_2345_; 
v_index_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_index_2343_);
lean_dec_ref_known(v___x_2342_, 3);
v_size_2344_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_size_2344_);
v___x_2345_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2303_, v_size_2344_, v_index_2343_, v_e_2300_, v_a_2301_);
lean_dec(v_index_2343_);
v___y_2306_ = v___x_2345_;
goto v___jp_2305_;
}
case 1:
{
lean_object* v_index_2346_; lean_object* v_size_2347_; lean_object* v_keyArray_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; 
v_index_2346_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_index_2346_);
lean_dec_ref_known(v___x_2342_, 1);
v_size_2347_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_size_2347_);
v_keyArray_2348_ = lean_ctor_get(v___x_2303_, 1);
lean_inc_ref(v_keyArray_2348_);
v___x_2349_ = lean_unsigned_to_nat(1u);
v___x_2350_ = lean_nat_add(v_size_2347_, v___x_2349_);
lean_dec(v_size_2347_);
v___x_2351_ = lean_array_get_size(v_keyArray_2348_);
lean_dec_ref(v_keyArray_2348_);
v___x_2352_ = lean_nat_dec_lt(v___x_2350_, v___x_2351_);
if (v___x_2352_ == 0)
{
lean_dec(v___x_2350_);
lean_dec(v_index_2346_);
goto v___jp_2315_;
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2353_ = lean_unsigned_to_nat(4u);
v___x_2354_ = lean_nat_mul(v___x_2350_, v___x_2353_);
v___x_2355_ = lean_unsigned_to_nat(3u);
v___x_2356_ = lean_nat_mul(v___x_2351_, v___x_2355_);
v___x_2357_ = lean_nat_dec_le(v___x_2354_, v___x_2356_);
lean_dec(v___x_2356_);
lean_dec(v___x_2354_);
if (v___x_2357_ == 0)
{
lean_dec(v___x_2350_);
lean_dec(v_index_2346_);
goto v___jp_2315_;
}
else
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2303_, v___x_2350_, v_index_2346_, v_e_2300_, v_a_2301_);
lean_dec(v_index_2346_);
v___y_2306_ = v___x_2358_;
goto v___jp_2305_;
}
}
}
default: 
{
lean_object* v_size_2359_; lean_object* v_keyArray_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v_size_2359_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_size_2359_);
v_keyArray_2360_ = lean_ctor_get(v___x_2303_, 1);
lean_inc_ref(v_keyArray_2360_);
v___x_2361_ = lean_unsigned_to_nat(1u);
v___x_2362_ = lean_nat_add(v_size_2359_, v___x_2361_);
lean_dec(v_size_2359_);
v___x_2363_ = lean_array_get_size(v_keyArray_2360_);
lean_dec_ref(v_keyArray_2360_);
v___x_2364_ = lean_nat_dec_lt(v___x_2362_, v___x_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; 
lean_dec(v___x_2362_);
v___x_2365_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11___redArg(v___x_2303_);
lean_dec(v___x_2303_);
v___y_2333_ = v___x_2365_;
goto v___jp_2332_;
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; 
v___x_2366_ = lean_unsigned_to_nat(4u);
v___x_2367_ = lean_nat_mul(v___x_2362_, v___x_2366_);
lean_dec(v___x_2362_);
v___x_2368_ = lean_unsigned_to_nat(3u);
v___x_2369_ = lean_nat_mul(v___x_2363_, v___x_2368_);
v___x_2370_ = lean_nat_dec_le(v___x_2367_, v___x_2369_);
lean_dec(v___x_2369_);
lean_dec(v___x_2367_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11___redArg(v___x_2303_);
lean_dec(v___x_2303_);
v___y_2333_ = v___x_2371_;
goto v___jp_2332_;
}
else
{
v___y_2333_ = v___x_2303_;
goto v___jp_2332_;
}
}
}
}
v___jp_2305_:
{
lean_object* v___x_2307_; 
v___x_2307_ = lean_st_ref_put(v_a_2299_, v___y_2306_);
return v___x_2304_;
}
v___jp_2308_:
{
lean_object* v_size_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v_size_2311_ = lean_ctor_get(v___y_2309_, 0);
v___x_2312_ = lean_unsigned_to_nat(1u);
v___x_2313_ = lean_nat_add(v_size_2311_, v___x_2312_);
v___x_2314_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2309_, v___x_2313_, v_i_2310_, v_e_2300_, v_a_2301_);
lean_dec(v_i_2310_);
v___y_2306_ = v___x_2314_;
goto v___jp_2305_;
}
v___jp_2315_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11___redArg(v___x_2303_);
lean_dec(v___x_2303_);
v___x_2317_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v___x_2316_, v_e_2300_);
switch(lean_obj_tag(v___x_2317_))
{
case 0:
{
lean_object* v_index_2318_; lean_object* v_size_2319_; lean_object* v___x_2320_; 
v_index_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_index_2318_);
lean_dec_ref_known(v___x_2317_, 3);
v_size_2319_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_size_2319_);
v___x_2320_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2316_, v_size_2319_, v_index_2318_, v_e_2300_, v_a_2301_);
lean_dec(v_index_2318_);
v___y_2306_ = v___x_2320_;
goto v___jp_2305_;
}
case 1:
{
lean_object* v_index_2321_; 
v_index_2321_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_index_2321_);
lean_dec_ref_known(v___x_2317_, 1);
v___y_2309_ = v___x_2316_;
v_i_2310_ = v_index_2321_;
goto v___jp_2308_;
}
default: 
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = lean_unsigned_to_nat(0u);
v___x_2323_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2316_, v___x_2322_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_index_2324_; 
v_index_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_index_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v___y_2309_ = v___x_2316_;
v_i_2310_ = v_index_2324_;
goto v___jp_2308_;
}
else
{
lean_dec_ref(v_a_2301_);
lean_dec_ref(v_e_2300_);
v___y_2306_ = v___x_2316_;
goto v___jp_2305_;
}
}
}
}
v___jp_2325_:
{
lean_object* v_size_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v_size_2328_ = lean_ctor_get(v___y_2326_, 0);
v___x_2329_ = lean_unsigned_to_nat(1u);
v___x_2330_ = lean_nat_add(v_size_2328_, v___x_2329_);
v___x_2331_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2326_, v___x_2330_, v_i_2327_, v_e_2300_, v_a_2301_);
lean_dec(v_i_2327_);
v___y_2306_ = v___x_2331_;
goto v___jp_2305_;
}
v___jp_2332_:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v___y_2333_, v_e_2300_);
switch(lean_obj_tag(v___x_2334_))
{
case 0:
{
lean_object* v_index_2335_; lean_object* v_size_2336_; lean_object* v___x_2337_; 
v_index_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_index_2335_);
lean_dec_ref_known(v___x_2334_, 3);
v_size_2336_ = lean_ctor_get(v___y_2333_, 0);
lean_inc(v_size_2336_);
v___x_2337_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2333_, v_size_2336_, v_index_2335_, v_e_2300_, v_a_2301_);
lean_dec(v_index_2335_);
v___y_2306_ = v___x_2337_;
goto v___jp_2305_;
}
case 1:
{
lean_object* v_index_2338_; 
v_index_2338_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_index_2338_);
lean_dec_ref_known(v___x_2334_, 1);
v___y_2326_ = v___y_2333_;
v_i_2327_ = v_index_2338_;
goto v___jp_2325_;
}
default: 
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = lean_unsigned_to_nat(0u);
v___x_2340_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2333_, v___x_2339_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_index_2341_; 
v_index_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_index_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v___y_2326_ = v___y_2333_;
v_i_2327_ = v_index_2341_;
goto v___jp_2325_;
}
else
{
lean_dec_ref(v_a_2301_);
lean_dec_ref(v_e_2300_);
v___y_2306_ = v___y_2333_;
goto v___jp_2305_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2372_, lean_object* v_e_2373_, lean_object* v_a_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2(v_a_2372_, v_e_2373_, v_a_2374_);
lean_dec(v_a_2372_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(lean_object* v_fvars_2380_, lean_object* v_pre_2381_, lean_object* v_post_2382_, uint8_t v_usedLetOnly_2383_, uint8_t v_skipConstInApp_2384_, uint8_t v_skipInstances_2385_, lean_object* v_body_2386_, lean_object* v_x_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_array_push(v_fvars_2380_, v_x_2387_);
v___x_2396_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2381_, v_post_2382_, v_usedLetOnly_2383_, v_skipConstInApp_2384_, v_skipInstances_2385_, v___x_2395_, v_body_2386_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed(lean_object* v_fvars_2397_, lean_object* v_pre_2398_, lean_object* v_post_2399_, lean_object* v_usedLetOnly_2400_, lean_object* v_skipConstInApp_2401_, lean_object* v_skipInstances_2402_, lean_object* v_body_2403_, lean_object* v_x_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
uint8_t v_usedLetOnly_boxed_2412_; uint8_t v_skipConstInApp_boxed_2413_; uint8_t v_skipInstances_boxed_2414_; lean_object* v_res_2415_; 
v_usedLetOnly_boxed_2412_ = lean_unbox(v_usedLetOnly_2400_);
v_skipConstInApp_boxed_2413_ = lean_unbox(v_skipConstInApp_2401_);
v_skipInstances_boxed_2414_ = lean_unbox(v_skipInstances_2402_);
v_res_2415_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0(v_fvars_2397_, v_pre_2398_, v_post_2399_, v_usedLetOnly_boxed_2412_, v_skipConstInApp_boxed_2413_, v_skipInstances_boxed_2414_, v_body_2403_, v_x_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec(v___y_2405_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(lean_object* v_pre_2416_, lean_object* v_post_2417_, uint8_t v_usedLetOnly_2418_, uint8_t v_skipConstInApp_2419_, uint8_t v_skipInstances_2420_, lean_object* v_e_2421_, lean_object* v_a_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v___x_2429_; 
lean_inc_ref(v_post_2417_);
lean_inc(v___y_2427_);
lean_inc_ref(v___y_2426_);
lean_inc(v___y_2425_);
lean_inc_ref(v___y_2424_);
lean_inc(v___y_2423_);
lean_inc_ref(v_e_2421_);
v___x_2429_ = lean_apply_7(v_post_2417_, v_e_2421_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, lean_box(0));
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2448_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2448_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2448_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
switch(lean_obj_tag(v_a_2430_))
{
case 0:
{
lean_object* v_e_2434_; lean_object* v___x_2436_; 
lean_dec_ref(v_e_2421_);
lean_dec_ref(v_post_2417_);
lean_dec_ref(v_pre_2416_);
v_e_2434_ = lean_ctor_get(v_a_2430_, 0);
lean_inc_ref(v_e_2434_);
lean_dec_ref_known(v_a_2430_, 1);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v_e_2434_);
v___x_2436_ = v___x_2432_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_e_2434_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
case 1:
{
lean_object* v_e_2438_; lean_object* v___x_2439_; 
lean_del_object(v___x_2432_);
lean_dec_ref(v_e_2421_);
v_e_2438_ = lean_ctor_get(v_a_2430_, 0);
lean_inc_ref(v_e_2438_);
lean_dec_ref_known(v_a_2430_, 1);
v___x_2439_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2416_, v_post_2417_, v_usedLetOnly_2418_, v_skipConstInApp_2419_, v_skipInstances_2420_, v_e_2438_, v_a_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
return v___x_2439_;
}
default: 
{
lean_object* v_e_x3f_2440_; 
lean_dec_ref(v_post_2417_);
lean_dec_ref(v_pre_2416_);
v_e_x3f_2440_ = lean_ctor_get(v_a_2430_, 0);
lean_inc(v_e_x3f_2440_);
lean_dec_ref_known(v_a_2430_, 1);
if (lean_obj_tag(v_e_x3f_2440_) == 0)
{
lean_object* v___x_2442_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v_e_2421_);
v___x_2442_ = v___x_2432_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_e_2421_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
else
{
lean_object* v_val_2444_; lean_object* v___x_2446_; 
lean_dec_ref(v_e_2421_);
v_val_2444_ = lean_ctor_get(v_e_x3f_2440_, 0);
lean_inc(v_val_2444_);
lean_dec_ref_known(v_e_x3f_2440_, 1);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v_val_2444_);
v___x_2446_ = v___x_2432_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_val_2444_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
}
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_dec_ref(v_e_2421_);
lean_dec_ref(v_post_2417_);
lean_dec_ref(v_pre_2416_);
v_a_2449_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2429_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2429_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(lean_object* v_pre_2457_, lean_object* v_post_2458_, uint8_t v_usedLetOnly_2459_, uint8_t v_skipConstInApp_2460_, uint8_t v_skipInstances_2461_, lean_object* v_fvars_2462_, lean_object* v_e_2463_, lean_object* v_a_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
if (lean_obj_tag(v_e_2463_) == 6)
{
lean_object* v_binderName_2471_; lean_object* v_binderType_2472_; lean_object* v_body_2473_; uint8_t v_binderInfo_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_binderName_2471_ = lean_ctor_get(v_e_2463_, 0);
lean_inc(v_binderName_2471_);
v_binderType_2472_ = lean_ctor_get(v_e_2463_, 1);
lean_inc_ref(v_binderType_2472_);
v_body_2473_ = lean_ctor_get(v_e_2463_, 2);
lean_inc_ref(v_body_2473_);
v_binderInfo_2474_ = lean_ctor_get_uint8(v_e_2463_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2463_, 3);
v___x_2475_ = lean_expr_instantiate_rev(v_binderType_2472_, v_fvars_2462_);
lean_dec_ref(v_binderType_2472_);
lean_inc_ref(v_post_2458_);
lean_inc_ref(v_pre_2457_);
v___x_2476_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2457_, v_post_2458_, v_usedLetOnly_2459_, v_skipConstInApp_2460_, v_skipInstances_2461_, v___x_2475_, v_a_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___f_2481_; uint8_t v___x_2482_; lean_object* v___x_2483_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
lean_dec_ref_known(v___x_2476_, 1);
v___x_2478_ = lean_box(v_usedLetOnly_2459_);
v___x_2479_ = lean_box(v_skipConstInApp_2460_);
v___x_2480_ = lean_box(v_skipInstances_2461_);
v___f_2481_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2481_, 0, v_fvars_2462_);
lean_closure_set(v___f_2481_, 1, v_pre_2457_);
lean_closure_set(v___f_2481_, 2, v_post_2458_);
lean_closure_set(v___f_2481_, 3, v___x_2478_);
lean_closure_set(v___f_2481_, 4, v___x_2479_);
lean_closure_set(v___f_2481_, 5, v___x_2480_);
lean_closure_set(v___f_2481_, 6, v_body_2473_);
v___x_2482_ = 0;
v___x_2483_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2471_, v_binderInfo_2474_, v_a_2477_, v___f_2481_, v___x_2482_, v_a_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
return v___x_2483_;
}
else
{
lean_dec_ref(v_body_2473_);
lean_dec(v_binderName_2471_);
lean_dec_ref(v_fvars_2462_);
lean_dec_ref(v_post_2458_);
lean_dec_ref(v_pre_2457_);
return v___x_2476_;
}
}
else
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = lean_expr_instantiate_rev(v_e_2463_, v_fvars_2462_);
lean_dec_ref(v_e_2463_);
lean_inc_ref(v_post_2458_);
lean_inc_ref(v_pre_2457_);
v___x_2485_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2457_, v_post_2458_, v_usedLetOnly_2459_, v_skipConstInApp_2460_, v_skipInstances_2461_, v___x_2484_, v_a_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; uint8_t v___x_2487_; uint8_t v___x_2488_; uint8_t v___x_2489_; lean_object* v___x_2490_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2486_);
lean_dec_ref_known(v___x_2485_, 1);
v___x_2487_ = 0;
v___x_2488_ = 1;
v___x_2489_ = 1;
v___x_2490_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2462_, v_a_2486_, v___x_2487_, v_usedLetOnly_2459_, v___x_2487_, v___x_2488_, v___x_2489_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
lean_dec_ref(v_fvars_2462_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; lean_object* v___x_2492_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_a_2491_);
lean_dec_ref_known(v___x_2490_, 1);
v___x_2492_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2457_, v_post_2458_, v_usedLetOnly_2459_, v_skipConstInApp_2460_, v_skipInstances_2461_, v_a_2491_, v_a_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
return v___x_2492_;
}
else
{
lean_dec_ref(v_post_2458_);
lean_dec_ref(v_pre_2457_);
return v___x_2490_;
}
}
else
{
lean_dec_ref(v_fvars_2462_);
lean_dec_ref(v_post_2458_);
lean_dec_ref(v_pre_2457_);
return v___x_2485_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(lean_object* v_fvars_2493_, lean_object* v_pre_2494_, lean_object* v_post_2495_, uint8_t v_usedLetOnly_2496_, uint8_t v_skipConstInApp_2497_, uint8_t v_skipInstances_2498_, lean_object* v_body_2499_, lean_object* v_x_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_array_push(v_fvars_2493_, v_x_2500_);
v___x_2509_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2494_, v_post_2495_, v_usedLetOnly_2496_, v_skipConstInApp_2497_, v_skipInstances_2498_, v___x_2508_, v_body_2499_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed(lean_object* v_fvars_2510_, lean_object* v_pre_2511_, lean_object* v_post_2512_, lean_object* v_usedLetOnly_2513_, lean_object* v_skipConstInApp_2514_, lean_object* v_skipInstances_2515_, lean_object* v_body_2516_, lean_object* v_x_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
uint8_t v_usedLetOnly_boxed_2525_; uint8_t v_skipConstInApp_boxed_2526_; uint8_t v_skipInstances_boxed_2527_; lean_object* v_res_2528_; 
v_usedLetOnly_boxed_2525_ = lean_unbox(v_usedLetOnly_2513_);
v_skipConstInApp_boxed_2526_ = lean_unbox(v_skipConstInApp_2514_);
v_skipInstances_boxed_2527_ = lean_unbox(v_skipInstances_2515_);
v_res_2528_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0(v_fvars_2510_, v_pre_2511_, v_post_2512_, v_usedLetOnly_boxed_2525_, v_skipConstInApp_boxed_2526_, v_skipInstances_boxed_2527_, v_body_2516_, v_x_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec(v___y_2518_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(lean_object* v_pre_2529_, lean_object* v_post_2530_, uint8_t v_usedLetOnly_2531_, uint8_t v_skipConstInApp_2532_, uint8_t v_skipInstances_2533_, lean_object* v_fvars_2534_, lean_object* v_e_2535_, lean_object* v_a_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
if (lean_obj_tag(v_e_2535_) == 8)
{
lean_object* v_declName_2543_; lean_object* v_type_2544_; lean_object* v_value_2545_; lean_object* v_body_2546_; uint8_t v_nondep_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v_declName_2543_ = lean_ctor_get(v_e_2535_, 0);
lean_inc(v_declName_2543_);
v_type_2544_ = lean_ctor_get(v_e_2535_, 1);
lean_inc_ref(v_type_2544_);
v_value_2545_ = lean_ctor_get(v_e_2535_, 2);
lean_inc_ref(v_value_2545_);
v_body_2546_ = lean_ctor_get(v_e_2535_, 3);
lean_inc_ref(v_body_2546_);
v_nondep_2547_ = lean_ctor_get_uint8(v_e_2535_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2535_, 4);
v___x_2548_ = lean_expr_instantiate_rev(v_type_2544_, v_fvars_2534_);
lean_dec_ref(v_type_2544_);
lean_inc_ref(v_post_2530_);
lean_inc_ref(v_pre_2529_);
v___x_2549_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2529_, v_post_2530_, v_usedLetOnly_2531_, v_skipConstInApp_2532_, v_skipInstances_2533_, v___x_2548_, v_a_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref_known(v___x_2549_, 1);
v___x_2551_ = lean_expr_instantiate_rev(v_value_2545_, v_fvars_2534_);
lean_dec_ref(v_value_2545_);
lean_inc_ref(v_post_2530_);
lean_inc_ref(v_pre_2529_);
v___x_2552_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2529_, v_post_2530_, v_usedLetOnly_2531_, v_skipConstInApp_2532_, v_skipInstances_2533_, v___x_2551_, v_a_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___f_2557_; uint8_t v___x_2558_; lean_object* v___x_2559_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v___x_2554_ = lean_box(v_usedLetOnly_2531_);
v___x_2555_ = lean_box(v_skipConstInApp_2532_);
v___x_2556_ = lean_box(v_skipInstances_2533_);
v___f_2557_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2557_, 0, v_fvars_2534_);
lean_closure_set(v___f_2557_, 1, v_pre_2529_);
lean_closure_set(v___f_2557_, 2, v_post_2530_);
lean_closure_set(v___f_2557_, 3, v___x_2554_);
lean_closure_set(v___f_2557_, 4, v___x_2555_);
lean_closure_set(v___f_2557_, 5, v___x_2556_);
lean_closure_set(v___f_2557_, 6, v_body_2546_);
v___x_2558_ = 0;
v___x_2559_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_declName_2543_, v_a_2550_, v_a_2553_, v___f_2557_, v_nondep_2547_, v___x_2558_, v_a_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
return v___x_2559_;
}
else
{
lean_dec(v_a_2550_);
lean_dec_ref(v_body_2546_);
lean_dec(v_declName_2543_);
lean_dec_ref(v_fvars_2534_);
lean_dec_ref(v_post_2530_);
lean_dec_ref(v_pre_2529_);
return v___x_2552_;
}
}
else
{
lean_dec_ref(v_body_2546_);
lean_dec_ref(v_value_2545_);
lean_dec(v_declName_2543_);
lean_dec_ref(v_fvars_2534_);
lean_dec_ref(v_post_2530_);
lean_dec_ref(v_pre_2529_);
return v___x_2549_;
}
}
else
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = lean_expr_instantiate_rev(v_e_2535_, v_fvars_2534_);
lean_dec_ref(v_e_2535_);
lean_inc_ref(v_post_2530_);
lean_inc_ref(v_pre_2529_);
v___x_2561_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2529_, v_post_2530_, v_usedLetOnly_2531_, v_skipConstInApp_2532_, v_skipInstances_2533_, v___x_2560_, v_a_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; uint8_t v___x_2563_; uint8_t v___x_2564_; lean_object* v___x_2565_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
v___x_2563_ = 0;
v___x_2564_ = 1;
v___x_2565_ = l_Lean_Meta_mkLetFVars(v_fvars_2534_, v_a_2562_, v_usedLetOnly_2531_, v___x_2563_, v___x_2564_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec_ref(v_fvars_2534_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2567_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
v___x_2567_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2529_, v_post_2530_, v_usedLetOnly_2531_, v_skipConstInApp_2532_, v_skipInstances_2533_, v_a_2566_, v_a_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
return v___x_2567_;
}
else
{
lean_dec_ref(v_post_2530_);
lean_dec_ref(v_pre_2529_);
return v___x_2565_;
}
}
else
{
lean_dec_ref(v_fvars_2534_);
lean_dec_ref(v_post_2530_);
lean_dec_ref(v_pre_2529_);
return v___x_2561_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2568_; lean_object* v_dummy_2569_; 
v___x_2568_ = lean_box(0);
v_dummy_2569_ = l_Lean_Expr_sort___override(v___x_2568_);
return v_dummy_2569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(lean_object* v_pre_2570_, lean_object* v_post_2571_, uint8_t v_usedLetOnly_2572_, uint8_t v_skipConstInApp_2573_, uint8_t v_skipInstances_2574_, size_t v_sz_2575_, size_t v_i_2576_, lean_object* v_bs_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
uint8_t v___x_2585_; 
v___x_2585_ = lean_usize_dec_lt(v_i_2576_, v_sz_2575_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; 
lean_dec_ref(v_post_2571_);
lean_dec_ref(v_pre_2570_);
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_bs_2577_);
return v___x_2586_;
}
else
{
lean_object* v_v_2587_; lean_object* v___x_2588_; 
v_v_2587_ = lean_array_uget_borrowed(v_bs_2577_, v_i_2576_);
lean_inc(v_v_2587_);
lean_inc_ref(v_post_2571_);
lean_inc_ref(v_pre_2570_);
v___x_2588_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2570_, v_post_2571_, v_usedLetOnly_2572_, v_skipConstInApp_2573_, v_skipInstances_2574_, v_v_2587_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2590_; lean_object* v_bs_x27_2591_; size_t v___x_2592_; size_t v___x_2593_; lean_object* v___x_2594_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
v___x_2590_ = lean_unsigned_to_nat(0u);
v_bs_x27_2591_ = lean_array_uset(v_bs_2577_, v_i_2576_, v___x_2590_);
v___x_2592_ = ((size_t)1ULL);
v___x_2593_ = lean_usize_add(v_i_2576_, v___x_2592_);
v___x_2594_ = lean_array_uset(v_bs_x27_2591_, v_i_2576_, v_a_2589_);
v_i_2576_ = v___x_2593_;
v_bs_2577_ = v___x_2594_;
goto _start;
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec_ref(v_bs_2577_);
lean_dec_ref(v_post_2571_);
lean_dec_ref(v_pre_2570_);
v_a_2596_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2588_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2588_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(lean_object* v_pre_2604_, lean_object* v_post_2605_, uint8_t v_usedLetOnly_2606_, uint8_t v_skipConstInApp_2607_, uint8_t v_skipInstances_2608_, lean_object* v___x_2609_, lean_object* v___y_2610_, lean_object* v_b_2611_, lean_object* v_a_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2604_, v_post_2605_, v_usedLetOnly_2606_, v_skipConstInApp_2607_, v_skipInstances_2608_, v___x_2609_, v___y_2610_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2629_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2629_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2629_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2627_; 
v___x_2624_ = lean_array_fset(v_b_2611_, v_a_2612_, v_a_2620_);
v___x_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2625_);
v___x_2627_ = v___x_2622_;
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
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
lean_dec_ref(v_b_2611_);
v_a_2630_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2619_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2619_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed(lean_object* v_pre_2638_, lean_object* v_post_2639_, lean_object* v_usedLetOnly_2640_, lean_object* v_skipConstInApp_2641_, lean_object* v_skipInstances_2642_, lean_object* v___x_2643_, lean_object* v___y_2644_, lean_object* v_b_2645_, lean_object* v_a_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
uint8_t v_usedLetOnly_boxed_2653_; uint8_t v_skipConstInApp_boxed_2654_; uint8_t v_skipInstances_boxed_2655_; lean_object* v_res_2656_; 
v_usedLetOnly_boxed_2653_ = lean_unbox(v_usedLetOnly_2640_);
v_skipConstInApp_boxed_2654_ = lean_unbox(v_skipConstInApp_2641_);
v_skipInstances_boxed_2655_ = lean_unbox(v_skipInstances_2642_);
v_res_2656_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0(v_pre_2638_, v_post_2639_, v_usedLetOnly_boxed_2653_, v_skipConstInApp_boxed_2654_, v_skipInstances_boxed_2655_, v___x_2643_, v___y_2644_, v_b_2645_, v_a_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec(v_a_2646_);
lean_dec(v___y_2644_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(lean_object* v_upperBound_2657_, lean_object* v___x_2658_, lean_object* v_pre_2659_, lean_object* v_post_2660_, uint8_t v_usedLetOnly_2661_, uint8_t v_skipConstInApp_2662_, uint8_t v_skipInstances_2663_, lean_object* v_a_2664_, lean_object* v_b_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v___y_2674_; uint8_t v___x_2697_; 
v___x_2697_ = lean_nat_dec_lt(v_a_2664_, v_upperBound_2657_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; 
lean_dec(v_a_2664_);
lean_dec_ref(v_post_2660_);
lean_dec_ref(v_pre_2659_);
v___x_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2698_, 0, v_b_2665_);
return v___x_2698_;
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; 
v___x_2699_ = lean_array_fget_borrowed(v_b_2665_, v_a_2664_);
v___x_2700_ = lean_array_get_size(v___x_2658_);
v___x_2701_ = lean_nat_dec_lt(v_a_2664_, v___x_2700_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___f_2705_; 
lean_inc(v___x_2699_);
v___x_2702_ = lean_box(v_usedLetOnly_2661_);
v___x_2703_ = lean_box(v_skipConstInApp_2662_);
v___x_2704_ = lean_box(v_skipInstances_2663_);
lean_inc(v_a_2664_);
lean_inc(v___y_2666_);
lean_inc_ref(v_post_2660_);
lean_inc_ref(v_pre_2659_);
v___f_2705_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2705_, 0, v_pre_2659_);
lean_closure_set(v___f_2705_, 1, v_post_2660_);
lean_closure_set(v___f_2705_, 2, v___x_2702_);
lean_closure_set(v___f_2705_, 3, v___x_2703_);
lean_closure_set(v___f_2705_, 4, v___x_2704_);
lean_closure_set(v___f_2705_, 5, v___x_2699_);
lean_closure_set(v___f_2705_, 6, v___y_2666_);
lean_closure_set(v___f_2705_, 7, v_b_2665_);
lean_closure_set(v___f_2705_, 8, v_a_2664_);
v___y_2674_ = v___f_2705_;
goto v___jp_2673_;
}
else
{
lean_object* v___x_2706_; uint8_t v_isInstance_2707_; 
v___x_2706_ = lean_array_fget_borrowed(v___x_2658_, v_a_2664_);
v_isInstance_2707_ = lean_ctor_get_uint8(v___x_2706_, sizeof(void*)*1 + 4);
if (v_isInstance_2707_ == 0)
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___f_2711_; 
lean_inc(v___x_2699_);
v___x_2708_ = lean_box(v_usedLetOnly_2661_);
v___x_2709_ = lean_box(v_skipConstInApp_2662_);
v___x_2710_ = lean_box(v_skipInstances_2663_);
lean_inc(v_a_2664_);
lean_inc(v___y_2666_);
lean_inc_ref(v_post_2660_);
lean_inc_ref(v_pre_2659_);
v___f_2711_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2711_, 0, v_pre_2659_);
lean_closure_set(v___f_2711_, 1, v_post_2660_);
lean_closure_set(v___f_2711_, 2, v___x_2708_);
lean_closure_set(v___f_2711_, 3, v___x_2709_);
lean_closure_set(v___f_2711_, 4, v___x_2710_);
lean_closure_set(v___f_2711_, 5, v___x_2699_);
lean_closure_set(v___f_2711_, 6, v___y_2666_);
lean_closure_set(v___f_2711_, 7, v_b_2665_);
lean_closure_set(v___f_2711_, 8, v_a_2664_);
v___y_2674_ = v___f_2711_;
goto v___jp_2673_;
}
else
{
lean_object* v___x_2712_; lean_object* v___f_2713_; 
v___x_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2712_, 0, v_b_2665_);
v___f_2713_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2713_, 0, v___x_2712_);
v___y_2674_ = v___f_2713_;
goto v___jp_2673_;
}
}
}
v___jp_2673_:
{
lean_object* v___x_2675_; 
lean_inc(v___y_2671_);
lean_inc_ref(v___y_2670_);
lean_inc(v___y_2669_);
lean_inc_ref(v___y_2668_);
lean_inc(v___y_2667_);
v___x_2675_ = lean_apply_6(v___y_2674_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, lean_box(0));
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2688_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2678_ = v___x_2675_;
v_isShared_2679_ = v_isSharedCheck_2688_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2675_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2688_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
if (lean_obj_tag(v_a_2676_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2682_; 
lean_dec(v_a_2664_);
lean_dec_ref(v_post_2660_);
lean_dec_ref(v_pre_2659_);
v_a_2680_ = lean_ctor_get(v_a_2676_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v_a_2676_, 1);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v_a_2680_);
v___x_2682_ = v___x_2678_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
lean_del_object(v___x_2678_);
v_a_2684_ = lean_ctor_get(v_a_2676_, 0);
lean_inc(v_a_2684_);
lean_dec_ref_known(v_a_2676_, 1);
v___x_2685_ = lean_unsigned_to_nat(1u);
v___x_2686_ = lean_nat_add(v_a_2664_, v___x_2685_);
lean_dec(v_a_2664_);
v_a_2664_ = v___x_2686_;
v_b_2665_ = v_a_2684_;
goto _start;
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec(v_a_2664_);
lean_dec_ref(v_post_2660_);
lean_dec_ref(v_pre_2659_);
v_a_2689_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2675_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2675_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(uint8_t v_skipInstances_2714_, lean_object* v_pre_2715_, lean_object* v_post_2716_, uint8_t v_usedLetOnly_2717_, uint8_t v_skipConstInApp_2718_, lean_object* v_x_2719_, lean_object* v_x_2720_, lean_object* v_x_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v_f_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v___y_2736_; 
if (lean_obj_tag(v_x_2719_) == 5)
{
lean_object* v_fn_2779_; lean_object* v_arg_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v_fn_2779_ = lean_ctor_get(v_x_2719_, 0);
lean_inc_ref(v_fn_2779_);
v_arg_2780_ = lean_ctor_get(v_x_2719_, 1);
lean_inc_ref(v_arg_2780_);
lean_dec_ref_known(v_x_2719_, 2);
v___x_2781_ = lean_array_set(v_x_2720_, v_x_2721_, v_arg_2780_);
v___x_2782_ = lean_unsigned_to_nat(1u);
v___x_2783_ = lean_nat_sub(v_x_2721_, v___x_2782_);
lean_dec(v_x_2721_);
v_x_2719_ = v_fn_2779_;
v_x_2720_ = v___x_2781_;
v_x_2721_ = v___x_2783_;
goto _start;
}
else
{
lean_dec(v_x_2721_);
if (v_skipConstInApp_2718_ == 0)
{
goto v___jp_2776_;
}
else
{
uint8_t v___x_2785_; 
v___x_2785_ = l_Lean_Expr_isConst(v_x_2719_);
if (v___x_2785_ == 0)
{
goto v___jp_2776_;
}
else
{
v_f_2730_ = v_x_2719_;
v___y_2731_ = v___y_2722_;
v___y_2732_ = v___y_2723_;
v___y_2733_ = v___y_2724_;
v___y_2734_ = v___y_2725_;
v___y_2735_ = v___y_2726_;
v___y_2736_ = v___y_2727_;
goto v___jp_2729_;
}
}
}
v___jp_2729_:
{
if (v_skipInstances_2714_ == 0)
{
size_t v_sz_2737_; size_t v___x_2738_; lean_object* v___x_2739_; 
v_sz_2737_ = lean_array_size(v_x_2720_);
v___x_2738_ = ((size_t)0ULL);
lean_inc_ref(v_post_2716_);
lean_inc_ref(v_pre_2715_);
v___x_2739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_2715_, v_post_2716_, v_usedLetOnly_2717_, v_skipConstInApp_2718_, v_skipInstances_2714_, v_sz_2737_, v___x_2738_, v_x_2720_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_a_2740_);
lean_dec_ref_known(v___x_2739_, 1);
v___x_2741_ = l_Lean_mkAppN(v_f_2730_, v_a_2740_);
lean_dec(v_a_2740_);
v___x_2742_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2715_, v_post_2716_, v_usedLetOnly_2717_, v_skipConstInApp_2718_, v_skipInstances_2714_, v___x_2741_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
return v___x_2742_;
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec_ref(v_f_2730_);
lean_dec_ref(v_post_2716_);
lean_dec_ref(v_pre_2715_);
v_a_2743_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2739_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2739_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = lean_array_get_size(v_x_2720_);
lean_inc_ref(v_f_2730_);
v___x_2752_ = l_Lean_Meta_getFunInfoNArgs(v_f_2730_, v___x_2751_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v_paramInfo_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v___x_2752_, 1);
v_paramInfo_2754_ = lean_ctor_get(v_a_2753_, 0);
lean_inc_ref(v_paramInfo_2754_);
lean_dec(v_a_2753_);
v___x_2755_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2716_);
lean_inc_ref(v_pre_2715_);
v___x_2756_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v___x_2751_, v_paramInfo_2754_, v_pre_2715_, v_post_2716_, v_usedLetOnly_2717_, v_skipConstInApp_2718_, v_skipInstances_2714_, v___x_2755_, v_x_2720_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec_ref(v_paramInfo_2754_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2756_, 1);
v___x_2758_ = l_Lean_mkAppN(v_f_2730_, v_a_2757_);
lean_dec(v_a_2757_);
v___x_2759_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2715_, v_post_2716_, v_usedLetOnly_2717_, v_skipConstInApp_2718_, v_skipInstances_2714_, v___x_2758_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
return v___x_2759_;
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec_ref(v_f_2730_);
lean_dec_ref(v_post_2716_);
lean_dec_ref(v_pre_2715_);
v_a_2760_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2756_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2756_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec_ref(v_f_2730_);
lean_dec_ref(v_x_2720_);
lean_dec_ref(v_post_2716_);
lean_dec_ref(v_pre_2715_);
v_a_2768_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2752_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2752_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
v___jp_2776_:
{
lean_object* v___x_2777_; 
lean_inc_ref(v_post_2716_);
lean_inc_ref(v_pre_2715_);
v___x_2777_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2715_, v_post_2716_, v_usedLetOnly_2717_, v_skipConstInApp_2718_, v_skipInstances_2714_, v_x_2719_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v___x_2777_, 1);
v_f_2730_ = v_a_2778_;
v___y_2731_ = v___y_2722_;
v___y_2732_ = v___y_2723_;
v___y_2733_ = v___y_2724_;
v___y_2734_ = v___y_2725_;
v___y_2735_ = v___y_2726_;
v___y_2736_ = v___y_2727_;
goto v___jp_2729_;
}
else
{
lean_dec_ref(v_x_2720_);
lean_dec_ref(v_post_2716_);
lean_dec_ref(v_pre_2715_);
return v___x_2777_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(lean_object* v___x_2786_, lean_object* v_pre_2787_, lean_object* v_e_2788_, lean_object* v_post_2789_, uint8_t v_usedLetOnly_2790_, uint8_t v_skipConstInApp_2791_, uint8_t v_skipInstances_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_Core_checkSystem(v___x_2786_, v___y_2797_, v___y_2798_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v___x_2801_; 
lean_dec_ref_known(v___x_2800_, 1);
lean_inc_ref(v_pre_2787_);
lean_inc(v___y_2798_);
lean_inc_ref(v___y_2797_);
lean_inc(v___y_2796_);
lean_inc_ref(v___y_2795_);
lean_inc(v___y_2794_);
lean_inc_ref(v_e_2788_);
v___x_2801_ = lean_apply_7(v_pre_2787_, v_e_2788_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, lean_box(0));
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2850_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2804_ = v___x_2801_;
v_isShared_2805_ = v_isSharedCheck_2850_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2801_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2850_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___y_2807_; 
switch(lean_obj_tag(v_a_2802_))
{
case 0:
{
lean_object* v_e_2842_; lean_object* v___x_2844_; 
lean_dec_ref(v_post_2789_);
lean_dec_ref(v_e_2788_);
lean_dec_ref(v_pre_2787_);
v_e_2842_ = lean_ctor_get(v_a_2802_, 0);
lean_inc_ref(v_e_2842_);
lean_dec_ref_known(v_a_2802_, 1);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v_e_2842_);
v___x_2844_ = v___x_2804_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_e_2842_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
case 1:
{
lean_object* v_e_2846_; lean_object* v___x_2847_; 
lean_del_object(v___x_2804_);
lean_dec_ref(v_e_2788_);
v_e_2846_ = lean_ctor_get(v_a_2802_, 0);
lean_inc_ref(v_e_2846_);
lean_dec_ref_known(v_a_2802_, 1);
v___x_2847_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2787_, v_post_2789_, v_usedLetOnly_2790_, v_skipConstInApp_2791_, v_skipInstances_2792_, v_e_2846_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2847_;
}
default: 
{
lean_object* v_e_x3f_2848_; 
lean_del_object(v___x_2804_);
v_e_x3f_2848_ = lean_ctor_get(v_a_2802_, 0);
lean_inc(v_e_x3f_2848_);
lean_dec_ref_known(v_a_2802_, 1);
if (lean_obj_tag(v_e_x3f_2848_) == 0)
{
v___y_2807_ = v_e_2788_;
goto v___jp_2806_;
}
else
{
lean_object* v_val_2849_; 
lean_dec_ref(v_e_2788_);
v_val_2849_ = lean_ctor_get(v_e_x3f_2848_, 0);
lean_inc(v_val_2849_);
lean_dec_ref_known(v_e_x3f_2848_, 1);
v___y_2807_ = v_val_2849_;
goto v___jp_2806_;
}
}
}
v___jp_2806_:
{
switch(lean_obj_tag(v___y_2807_))
{
case 7:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2809_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2787_, v_post_2789_, v_usedLetOnly_2790_, v_skipConstInApp_2791_, v_skipInstances_2792_, v___x_2808_, v___y_2807_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2809_;
}
case 6:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2811_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_2787_, v_post_2789_, v_usedLetOnly_2790_, v_skipConstInApp_2791_, v_skipInstances_2792_, v___x_2810_, v___y_2807_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2811_;
}
case 8:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2812_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__0));
v___x_2813_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_2787_, v_post_2789_, v_usedLetOnly_2790_, v_skipConstInApp_2791_, v_skipInstances_2792_, v___x_2812_, v___y_2807_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2813_;
}
case 5:
{
lean_object* v_dummy_2814_; lean_object* v_nargs_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v_dummy_2814_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1, &l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1_once, _init_l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___closed__1);
v_nargs_2815_ = l_Lean_Expr_getAppNumArgs(v___y_2807_);
lean_inc(v_nargs_2815_);
v___x_2816_ = lean_mk_array(v_nargs_2815_, v_dummy_2814_);
v___x_2817_ = lean_unsigned_to_nat(1u);
v___x_2818_ = lean_nat_sub(v_nargs_2815_, v___x_2817_);
lean_dec(v_nargs_2815_);
v___x_2819_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_2792_, v_pre_2787_, v_post_2789_, v_usedLetOnly_2790_, v_skipConstInApp_2791_, v___y_2807_, v___x_2816_, v___x_2818_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2819_;
}
case 10:
{
lean_object* v_data_2820_; lean_object* v_expr_2821_; lean_object* v___x_2822_; 
v_data_2820_ = lean_ctor_get(v___y_2807_, 0);
v_expr_2821_ = lean_ctor_get(v___y_2807_, 1);
lean_inc_ref(v_expr_2821_);
lean_inc_ref(v_post_2789_);
lean_inc_ref(v_pre_2787_);
v___x_2822_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2787_, v_post_2789_, v_usedLetOnly_2790_, v_skipConstInApp_2791_, v_skipInstances_2792_, v_expr_2821_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; size_t v___x_2824_; size_t v___x_2825_; uint8_t v___x_2826_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2822_, 1);
v___x_2824_ = lean_ptr_addr(v_expr_2821_);
v___x_2825_ = lean_ptr_addr(v_a_2823_);
v___x_2826_ = lean_usize_dec_eq(v___x_2824_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
lean_inc(v_data_2820_);
lean_dec_ref_known(v___y_2807_, 2);
v___x_2827_ = l_Lean_Expr_mdata___override(v_data_2820_, v_a_2823_);
v___x_2828_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2787_, v_post_2789_, v_usedLetOnly_2790_, v_skipConstInApp_2791_, v_skipInstances_2792_, v___x_2827_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2828_;
}
else
{
lean_object* v___x_2829_; 
lean_dec(v_a_2823_);
v___x_2829_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2787_, v_post_2789_, v_usedLetOnly_2790_, v_skipConstInApp_2791_, v_skipInstances_2792_, v___y_2807_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2829_;
}
}
else
{
lean_dec_ref_known(v___y_2807_, 2);
lean_dec_ref(v_post_2789_);
lean_dec_ref(v_pre_2787_);
return v___x_2822_;
}
}
case 11:
{
lean_object* v_typeName_2830_; lean_object* v_idx_2831_; lean_object* v_struct_2832_; lean_object* v___x_2833_; 
v_typeName_2830_ = lean_ctor_get(v___y_2807_, 0);
v_idx_2831_ = lean_ctor_get(v___y_2807_, 1);
v_struct_2832_ = lean_ctor_get(v___y_2807_, 2);
lean_inc_ref(v_struct_2832_);
lean_inc_ref(v_post_2789_);
lean_inc_ref(v_pre_2787_);
v___x_2833_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2787_, v_post_2789_, v_usedLetOnly_2790_, v_skipConstInApp_2791_, v_skipInstances_2792_, v_struct_2832_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; size_t v___x_2835_; size_t v___x_2836_; uint8_t v___x_2837_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v___x_2833_, 1);
v___x_2835_ = lean_ptr_addr(v_struct_2832_);
v___x_2836_ = lean_ptr_addr(v_a_2834_);
v___x_2837_ = lean_usize_dec_eq(v___x_2835_, v___x_2836_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_inc(v_idx_2831_);
lean_inc(v_typeName_2830_);
lean_dec_ref_known(v___y_2807_, 3);
v___x_2838_ = l_Lean_Expr_proj___override(v_typeName_2830_, v_idx_2831_, v_a_2834_);
v___x_2839_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2787_, v_post_2789_, v_usedLetOnly_2790_, v_skipConstInApp_2791_, v_skipInstances_2792_, v___x_2838_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2839_;
}
else
{
lean_object* v___x_2840_; 
lean_dec(v_a_2834_);
v___x_2840_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2787_, v_post_2789_, v_usedLetOnly_2790_, v_skipConstInApp_2791_, v_skipInstances_2792_, v___y_2807_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2840_;
}
}
else
{
lean_dec_ref_known(v___y_2807_, 3);
lean_dec_ref(v_post_2789_);
lean_dec_ref(v_pre_2787_);
return v___x_2833_;
}
}
default: 
{
lean_object* v___x_2841_; 
v___x_2841_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2787_, v_post_2789_, v_usedLetOnly_2790_, v_skipConstInApp_2791_, v_skipInstances_2792_, v___y_2807_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2841_;
}
}
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec_ref(v_post_2789_);
lean_dec_ref(v_e_2788_);
lean_dec_ref(v_pre_2787_);
v_a_2851_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2801_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2801_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_dec_ref(v_post_2789_);
lean_dec_ref(v_e_2788_);
lean_dec_ref(v_pre_2787_);
v_a_2859_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2800_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2800_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed(lean_object* v___x_2867_, lean_object* v_pre_2868_, lean_object* v_e_2869_, lean_object* v_post_2870_, lean_object* v_usedLetOnly_2871_, lean_object* v_skipConstInApp_2872_, lean_object* v_skipInstances_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
uint8_t v_usedLetOnly_boxed_2881_; uint8_t v_skipConstInApp_boxed_2882_; uint8_t v_skipInstances_boxed_2883_; lean_object* v_res_2884_; 
v_usedLetOnly_boxed_2881_ = lean_unbox(v_usedLetOnly_2871_);
v_skipConstInApp_boxed_2882_ = lean_unbox(v_skipConstInApp_2872_);
v_skipInstances_boxed_2883_ = lean_unbox(v_skipInstances_2873_);
v_res_2884_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1(v___x_2867_, v_pre_2868_, v_e_2869_, v_post_2870_, v_usedLetOnly_boxed_2881_, v_skipConstInApp_boxed_2882_, v_skipInstances_boxed_2883_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec(v___y_2874_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(lean_object* v_pre_2885_, lean_object* v_post_2886_, uint8_t v_usedLetOnly_2887_, uint8_t v_skipConstInApp_2888_, uint8_t v_skipInstances_2889_, lean_object* v_e_2890_, lean_object* v_a_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
lean_inc(v_a_2891_);
v___x_2898_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2898_, 0, lean_box(0));
lean_closure_set(v___x_2898_, 1, lean_box(0));
lean_closure_set(v___x_2898_, 2, v_a_2891_);
v___x_2899_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___x_2898_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2934_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2902_ = v___x_2899_;
v_isShared_2903_ = v_isSharedCheck_2934_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2899_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2934_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2904_; 
v___x_2904_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_a_2900_, v_e_2890_);
lean_dec(v_a_2900_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___f_2909_; lean_object* v___x_2910_; 
lean_del_object(v___x_2902_);
v___x_2905_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___closed__0));
v___x_2906_ = lean_box(v_usedLetOnly_2887_);
v___x_2907_ = lean_box(v_skipConstInApp_2888_);
v___x_2908_ = lean_box(v_skipInstances_2889_);
lean_inc_ref(v_e_2890_);
v___f_2909_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__1___boxed), 14, 7);
lean_closure_set(v___f_2909_, 0, v___x_2905_);
lean_closure_set(v___f_2909_, 1, v_pre_2885_);
lean_closure_set(v___f_2909_, 2, v_e_2890_);
lean_closure_set(v___f_2909_, 3, v_post_2886_);
lean_closure_set(v___f_2909_, 4, v___x_2906_);
lean_closure_set(v___f_2909_, 5, v___x_2907_);
lean_closure_set(v___f_2909_, 6, v___x_2908_);
v___x_2910_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v___f_2909_, v_a_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___f_2912_; lean_object* v___x_2913_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc_n(v_a_2911_, 2);
lean_dec_ref_known(v___x_2910_, 1);
lean_inc(v_a_2891_);
v___f_2912_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2912_, 0, v_a_2891_);
lean_closure_set(v___f_2912_, 1, v_e_2890_);
lean_closure_set(v___f_2912_, 2, v_a_2911_);
v___x_2913_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___lam__0(lean_box(0), v___f_2912_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2920_ == 0)
{
lean_object* v_unused_2921_; 
v_unused_2921_ = lean_ctor_get(v___x_2913_, 0);
lean_dec(v_unused_2921_);
v___x_2915_ = v___x_2913_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_dec(v___x_2913_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 0, v_a_2911_);
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2911_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec(v_a_2911_);
v_a_2922_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2913_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2913_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
else
{
lean_dec_ref(v_e_2890_);
return v___x_2910_;
}
}
else
{
lean_object* v_val_2930_; lean_object* v___x_2932_; 
lean_dec_ref(v_e_2890_);
lean_dec_ref(v_post_2886_);
lean_dec_ref(v_pre_2885_);
v_val_2930_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_val_2930_);
lean_dec_ref_known(v___x_2904_, 1);
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 0, v_val_2930_);
v___x_2932_ = v___x_2902_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_val_2930_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_dec_ref(v_e_2890_);
lean_dec_ref(v_post_2886_);
lean_dec_ref(v_pre_2885_);
v_a_2935_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2899_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2899_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed(lean_object* v_fvars_2943_, lean_object* v_pre_2944_, lean_object* v_post_2945_, lean_object* v_usedLetOnly_2946_, lean_object* v_skipConstInApp_2947_, lean_object* v_skipInstances_2948_, lean_object* v_body_2949_, lean_object* v_x_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
uint8_t v_usedLetOnly_boxed_2958_; uint8_t v_skipConstInApp_boxed_2959_; uint8_t v_skipInstances_boxed_2960_; lean_object* v_res_2961_; 
v_usedLetOnly_boxed_2958_ = lean_unbox(v_usedLetOnly_2946_);
v_skipConstInApp_boxed_2959_ = lean_unbox(v_skipConstInApp_2947_);
v_skipInstances_boxed_2960_ = lean_unbox(v_skipInstances_2948_);
v_res_2961_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(v_fvars_2943_, v_pre_2944_, v_post_2945_, v_usedLetOnly_boxed_2958_, v_skipConstInApp_boxed_2959_, v_skipInstances_boxed_2960_, v_body_2949_, v_x_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec(v___y_2951_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(lean_object* v_pre_2962_, lean_object* v_post_2963_, uint8_t v_usedLetOnly_2964_, uint8_t v_skipConstInApp_2965_, uint8_t v_skipInstances_2966_, lean_object* v_fvars_2967_, lean_object* v_e_2968_, lean_object* v_a_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
if (lean_obj_tag(v_e_2968_) == 7)
{
lean_object* v_binderName_2976_; lean_object* v_binderType_2977_; lean_object* v_body_2978_; uint8_t v_binderInfo_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v_binderName_2976_ = lean_ctor_get(v_e_2968_, 0);
lean_inc(v_binderName_2976_);
v_binderType_2977_ = lean_ctor_get(v_e_2968_, 1);
lean_inc_ref(v_binderType_2977_);
v_body_2978_ = lean_ctor_get(v_e_2968_, 2);
lean_inc_ref(v_body_2978_);
v_binderInfo_2979_ = lean_ctor_get_uint8(v_e_2968_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2968_, 3);
v___x_2980_ = lean_expr_instantiate_rev(v_binderType_2977_, v_fvars_2967_);
lean_dec_ref(v_binderType_2977_);
lean_inc_ref(v_post_2963_);
lean_inc_ref(v_pre_2962_);
v___x_2981_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2962_, v_post_2963_, v_usedLetOnly_2964_, v_skipConstInApp_2965_, v_skipInstances_2966_, v___x_2980_, v_a_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___f_2986_; uint8_t v___x_2987_; lean_object* v___x_2988_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_a_2982_);
lean_dec_ref_known(v___x_2981_, 1);
v___x_2983_ = lean_box(v_usedLetOnly_2964_);
v___x_2984_ = lean_box(v_skipConstInApp_2965_);
v___x_2985_ = lean_box(v_skipInstances_2966_);
v___f_2986_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0___boxed), 15, 7);
lean_closure_set(v___f_2986_, 0, v_fvars_2967_);
lean_closure_set(v___f_2986_, 1, v_pre_2962_);
lean_closure_set(v___f_2986_, 2, v_post_2963_);
lean_closure_set(v___f_2986_, 3, v___x_2983_);
lean_closure_set(v___f_2986_, 4, v___x_2984_);
lean_closure_set(v___f_2986_, 5, v___x_2985_);
lean_closure_set(v___f_2986_, 6, v_body_2978_);
v___x_2987_ = 0;
v___x_2988_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_binderName_2976_, v_binderInfo_2979_, v_a_2982_, v___f_2986_, v___x_2987_, v_a_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
return v___x_2988_;
}
else
{
lean_dec_ref(v_body_2978_);
lean_dec(v_binderName_2976_);
lean_dec_ref(v_fvars_2967_);
lean_dec_ref(v_post_2963_);
lean_dec_ref(v_pre_2962_);
return v___x_2981_;
}
}
else
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = lean_expr_instantiate_rev(v_e_2968_, v_fvars_2967_);
lean_dec_ref(v_e_2968_);
lean_inc_ref(v_post_2963_);
lean_inc_ref(v_pre_2962_);
v___x_2990_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_2962_, v_post_2963_, v_usedLetOnly_2964_, v_skipConstInApp_2965_, v_skipInstances_2966_, v___x_2989_, v_a_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; uint8_t v___x_2992_; uint8_t v___x_2993_; uint8_t v___x_2994_; lean_object* v___x_2995_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___x_2990_, 1);
v___x_2992_ = 0;
v___x_2993_ = 1;
v___x_2994_ = 1;
v___x_2995_ = l_Lean_Meta_mkForallFVars(v_fvars_2967_, v_a_2991_, v___x_2992_, v_usedLetOnly_2964_, v___x_2993_, v___x_2994_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
lean_dec_ref(v_fvars_2967_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2997_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2995_, 1);
v___x_2997_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_2962_, v_post_2963_, v_usedLetOnly_2964_, v_skipConstInApp_2965_, v_skipInstances_2966_, v_a_2996_, v_a_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
return v___x_2997_;
}
else
{
lean_dec_ref(v_post_2963_);
lean_dec_ref(v_pre_2962_);
return v___x_2995_;
}
}
else
{
lean_dec_ref(v_fvars_2967_);
lean_dec_ref(v_post_2963_);
lean_dec_ref(v_pre_2962_);
return v___x_2990_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___lam__0(lean_object* v_fvars_2998_, lean_object* v_pre_2999_, lean_object* v_post_3000_, uint8_t v_usedLetOnly_3001_, uint8_t v_skipConstInApp_3002_, uint8_t v_skipInstances_3003_, lean_object* v_body_3004_, lean_object* v_x_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = lean_array_push(v_fvars_2998_, v_x_3005_);
v___x_3014_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_2999_, v_post_3000_, v_usedLetOnly_3001_, v_skipConstInApp_3002_, v_skipInstances_3003_, v___x_3013_, v_body_3004_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_3015_, lean_object* v_post_3016_, lean_object* v_usedLetOnly_3017_, lean_object* v_skipConstInApp_3018_, lean_object* v_skipInstances_3019_, lean_object* v_e_3020_, lean_object* v_a_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
uint8_t v_usedLetOnly_boxed_3028_; uint8_t v_skipConstInApp_boxed_3029_; uint8_t v_skipInstances_boxed_3030_; lean_object* v_res_3031_; 
v_usedLetOnly_boxed_3028_ = lean_unbox(v_usedLetOnly_3017_);
v_skipConstInApp_boxed_3029_ = lean_unbox(v_skipConstInApp_3018_);
v_skipInstances_boxed_3030_ = lean_unbox(v_skipInstances_3019_);
v_res_3031_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__2(v_pre_3015_, v_post_3016_, v_usedLetOnly_boxed_3028_, v_skipConstInApp_boxed_3029_, v_skipInstances_boxed_3030_, v_e_3020_, v_a_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec(v_a_3021_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_3032_, lean_object* v_post_3033_, lean_object* v_usedLetOnly_3034_, lean_object* v_skipConstInApp_3035_, lean_object* v_skipInstances_3036_, lean_object* v_sz_3037_, lean_object* v_i_3038_, lean_object* v_bs_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
uint8_t v_usedLetOnly_boxed_3047_; uint8_t v_skipConstInApp_boxed_3048_; uint8_t v_skipInstances_boxed_3049_; size_t v_sz_boxed_3050_; size_t v_i_boxed_3051_; lean_object* v_res_3052_; 
v_usedLetOnly_boxed_3047_ = lean_unbox(v_usedLetOnly_3034_);
v_skipConstInApp_boxed_3048_ = lean_unbox(v_skipConstInApp_3035_);
v_skipInstances_boxed_3049_ = lean_unbox(v_skipInstances_3036_);
v_sz_boxed_3050_ = lean_unbox_usize(v_sz_3037_);
lean_dec(v_sz_3037_);
v_i_boxed_3051_ = lean_unbox_usize(v_i_3038_);
lean_dec(v_i_3038_);
v_res_3052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__1(v_pre_3032_, v_post_3033_, v_usedLetOnly_boxed_3047_, v_skipConstInApp_boxed_3048_, v_skipInstances_boxed_3049_, v_sz_boxed_3050_, v_i_boxed_3051_, v_bs_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec(v___y_3040_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0___boxed(lean_object* v_pre_3053_, lean_object* v_post_3054_, lean_object* v_usedLetOnly_3055_, lean_object* v_skipConstInApp_3056_, lean_object* v_skipInstances_3057_, lean_object* v_e_3058_, lean_object* v_a_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
uint8_t v_usedLetOnly_boxed_3066_; uint8_t v_skipConstInApp_boxed_3067_; uint8_t v_skipInstances_boxed_3068_; lean_object* v_res_3069_; 
v_usedLetOnly_boxed_3066_ = lean_unbox(v_usedLetOnly_3055_);
v_skipConstInApp_boxed_3067_ = lean_unbox(v_skipConstInApp_3056_);
v_skipInstances_boxed_3068_ = lean_unbox(v_skipInstances_3057_);
v_res_3069_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_3053_, v_post_3054_, v_usedLetOnly_boxed_3066_, v_skipConstInApp_boxed_3067_, v_skipInstances_boxed_3068_, v_e_3058_, v_a_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec(v_a_3059_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5___boxed(lean_object* v_pre_3070_, lean_object* v_post_3071_, lean_object* v_usedLetOnly_3072_, lean_object* v_skipConstInApp_3073_, lean_object* v_skipInstances_3074_, lean_object* v_fvars_3075_, lean_object* v_e_3076_, lean_object* v_a_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_){
_start:
{
uint8_t v_usedLetOnly_boxed_3084_; uint8_t v_skipConstInApp_boxed_3085_; uint8_t v_skipInstances_boxed_3086_; lean_object* v_res_3087_; 
v_usedLetOnly_boxed_3084_ = lean_unbox(v_usedLetOnly_3072_);
v_skipConstInApp_boxed_3085_ = lean_unbox(v_skipConstInApp_3073_);
v_skipInstances_boxed_3086_ = lean_unbox(v_skipInstances_3074_);
v_res_3087_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5(v_pre_3070_, v_post_3071_, v_usedLetOnly_boxed_3084_, v_skipConstInApp_boxed_3085_, v_skipInstances_boxed_3086_, v_fvars_3075_, v_e_3076_, v_a_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec(v_a_3077_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6___boxed(lean_object* v_pre_3088_, lean_object* v_post_3089_, lean_object* v_usedLetOnly_3090_, lean_object* v_skipConstInApp_3091_, lean_object* v_skipInstances_3092_, lean_object* v_fvars_3093_, lean_object* v_e_3094_, lean_object* v_a_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
uint8_t v_usedLetOnly_boxed_3102_; uint8_t v_skipConstInApp_boxed_3103_; uint8_t v_skipInstances_boxed_3104_; lean_object* v_res_3105_; 
v_usedLetOnly_boxed_3102_ = lean_unbox(v_usedLetOnly_3090_);
v_skipConstInApp_boxed_3103_ = lean_unbox(v_skipConstInApp_3091_);
v_skipInstances_boxed_3104_ = lean_unbox(v_skipInstances_3092_);
v_res_3105_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__6(v_pre_3088_, v_post_3089_, v_usedLetOnly_boxed_3102_, v_skipConstInApp_boxed_3103_, v_skipInstances_boxed_3104_, v_fvars_3093_, v_e_3094_, v_a_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec(v_a_3095_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7___boxed(lean_object* v_pre_3106_, lean_object* v_post_3107_, lean_object* v_usedLetOnly_3108_, lean_object* v_skipConstInApp_3109_, lean_object* v_skipInstances_3110_, lean_object* v_fvars_3111_, lean_object* v_e_3112_, lean_object* v_a_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
uint8_t v_usedLetOnly_boxed_3120_; uint8_t v_skipConstInApp_boxed_3121_; uint8_t v_skipInstances_boxed_3122_; lean_object* v_res_3123_; 
v_usedLetOnly_boxed_3120_ = lean_unbox(v_usedLetOnly_3108_);
v_skipConstInApp_boxed_3121_ = lean_unbox(v_skipConstInApp_3109_);
v_skipInstances_boxed_3122_ = lean_unbox(v_skipInstances_3110_);
v_res_3123_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7(v_pre_3106_, v_post_3107_, v_usedLetOnly_boxed_3120_, v_skipConstInApp_boxed_3121_, v_skipInstances_boxed_3122_, v_fvars_3111_, v_e_3112_, v_a_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec(v_a_3113_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_upperBound_3124_, lean_object* v___x_3125_, lean_object* v_pre_3126_, lean_object* v_post_3127_, lean_object* v_usedLetOnly_3128_, lean_object* v_skipConstInApp_3129_, lean_object* v_skipInstances_3130_, lean_object* v_a_3131_, lean_object* v_b_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
uint8_t v_usedLetOnly_boxed_3140_; uint8_t v_skipConstInApp_boxed_3141_; uint8_t v_skipInstances_boxed_3142_; lean_object* v_res_3143_; 
v_usedLetOnly_boxed_3140_ = lean_unbox(v_usedLetOnly_3128_);
v_skipConstInApp_boxed_3141_ = lean_unbox(v_skipConstInApp_3129_);
v_skipInstances_boxed_3142_ = lean_unbox(v_skipInstances_3130_);
v_res_3143_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_3124_, v___x_3125_, v_pre_3126_, v_post_3127_, v_usedLetOnly_boxed_3140_, v_skipConstInApp_boxed_3141_, v_skipInstances_boxed_3142_, v_a_3131_, v_b_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___x_3125_);
lean_dec(v_upperBound_3124_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8___boxed(lean_object* v_skipInstances_3144_, lean_object* v_pre_3145_, lean_object* v_post_3146_, lean_object* v_usedLetOnly_3147_, lean_object* v_skipConstInApp_3148_, lean_object* v_x_3149_, lean_object* v_x_3150_, lean_object* v_x_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_){
_start:
{
uint8_t v_skipInstances_boxed_3159_; uint8_t v_usedLetOnly_boxed_3160_; uint8_t v_skipConstInApp_boxed_3161_; lean_object* v_res_3162_; 
v_skipInstances_boxed_3159_ = lean_unbox(v_skipInstances_3144_);
v_usedLetOnly_boxed_3160_ = lean_unbox(v_usedLetOnly_3147_);
v_skipConstInApp_boxed_3161_ = lean_unbox(v_skipConstInApp_3148_);
v_res_3162_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__8(v_skipInstances_boxed_3159_, v_pre_3145_, v_post_3146_, v_usedLetOnly_boxed_3160_, v_skipConstInApp_boxed_3161_, v_x_3149_, v_x_3150_, v_x_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec(v___y_3152_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_object* v_00_u03b1_3163_, lean_object* v_x_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = lean_apply_1(v_x_3164_, lean_box(0));
v___x_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0___boxed(lean_object* v_00_u03b1_3173_, lean_object* v_x_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(v_00_u03b1_3173_, v_x_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
return v_res_3181_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0(void){
_start:
{
lean_object* v_cellCount_3182_; lean_object* v___x_3183_; 
v_cellCount_3182_ = lean_unsigned_to_nat(16u);
v___x_3183_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_3182_);
return v___x_3183_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1(void){
_start:
{
lean_object* v_cellCount_3184_; lean_object* v___x_3185_; 
v_cellCount_3184_ = lean_unsigned_to_nat(16u);
v___x_3185_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3184_);
return v___x_3185_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3186_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__1);
v___x_3187_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__0);
v___x_3188_ = lean_unsigned_to_nat(0u);
v___x_3189_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
lean_ctor_set(v___x_3189_, 1, v___x_3187_);
lean_ctor_set(v___x_3189_, 2, v___x_3186_);
return v___x_3189_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__2);
v___x_3191_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3191_, 0, lean_box(0));
lean_closure_set(v___x_3191_, 1, lean_box(0));
lean_closure_set(v___x_3191_, 2, v___x_3190_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(lean_object* v_input_3192_, lean_object* v_pre_3193_, lean_object* v_post_3194_, uint8_t v_usedLetOnly_3195_, uint8_t v_skipConstInApp_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v_a_3205_; uint8_t v___x_3206_; lean_object* v___x_3207_; 
v___x_3203_ = lean_obj_once(&l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__3, &l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__3_once, _init_l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___closed__3);
v___x_3204_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3203_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref(v___x_3204_);
v___x_3206_ = 0;
v___x_3207_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0(v_pre_3193_, v_post_3194_, v_usedLetOnly_3195_, v_skipConstInApp_3196_, v___x_3206_, v_input_3192_, v_a_3205_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref_known(v___x_3207_, 1);
v___x_3209_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3209_, 0, lean_box(0));
lean_closure_set(v___x_3209_, 1, lean_box(0));
lean_closure_set(v___x_3209_, 2, v_a_3205_);
v___x_3210_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___lam__0(lean_box(0), v___x_3209_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3217_ == 0)
{
lean_object* v_unused_3218_; 
v_unused_3218_ = lean_ctor_get(v___x_3210_, 0);
lean_dec(v_unused_3218_);
v___x_3212_ = v___x_3210_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_dec(v___x_3210_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v_a_3208_);
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3208_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
else
{
lean_dec(v_a_3205_);
return v___x_3207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0___boxed(lean_object* v_input_3219_, lean_object* v_pre_3220_, lean_object* v_post_3221_, lean_object* v_usedLetOnly_3222_, lean_object* v_skipConstInApp_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
uint8_t v_usedLetOnly_boxed_3230_; uint8_t v_skipConstInApp_boxed_3231_; lean_object* v_res_3232_; 
v_usedLetOnly_boxed_3230_ = lean_unbox(v_usedLetOnly_3222_);
v_skipConstInApp_boxed_3231_ = lean_unbox(v_skipConstInApp_3223_);
v_res_3232_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_input_3219_, v_pre_3220_, v_post_3221_, v_usedLetOnly_boxed_3230_, v_skipConstInApp_boxed_3231_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
return v_res_3232_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0(void){
_start:
{
lean_object* v_cellCount_3233_; lean_object* v___x_3234_; 
v_cellCount_3233_ = lean_unsigned_to_nat(16u);
v___x_3234_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3233_);
return v___x_3234_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_elimLetsCore___closed__1(void){
_start:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3235_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0, &l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0_once, _init_l_Lean_Elab_Tactic_Do_elimLetsCore___closed__0);
v___x_3236_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2, &l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2_once, _init_l_Lean_Elab_Tactic_Do_countUsesDecl___closed__2);
v___x_3237_ = lean_unsigned_to_nat(0u);
v___x_3238_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
lean_ctor_set(v___x_3238_, 1, v___x_3236_);
lean_ctor_set(v___x_3238_, 2, v___x_3235_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore(lean_object* v_e_3240_, uint8_t v_elimTrivial_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_){
_start:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v_pre_3250_; lean_object* v___f_3251_; uint8_t v___x_3252_; lean_object* v___x_3253_; 
v___x_3247_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_elimLetsCore___closed__1, &l_Lean_Elab_Tactic_Do_elimLetsCore___closed__1_once, _init_l_Lean_Elab_Tactic_Do_elimLetsCore___closed__1);
v___x_3248_ = lean_st_mk_ref(v___x_3247_);
v___x_3249_ = lean_box(v_elimTrivial_3241_);
v_pre_3250_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLetsCore___lam__0___boxed), 8, 1);
lean_closure_set(v_pre_3250_, 0, v___x_3249_);
v___f_3251_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLetsCore___closed__2));
v___x_3252_ = 0;
v___x_3253_ = l_Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0(v_e_3240_, v_pre_3250_, v___f_3251_, v___x_3252_, v___x_3252_, v___x_3248_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3262_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3256_ = v___x_3253_;
v_isShared_3257_ = v_isSharedCheck_3262_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3253_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3262_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3258_; lean_object* v___x_3260_; 
v___x_3258_ = lean_st_ref_get(v___x_3248_);
lean_dec(v___x_3248_);
lean_dec(v___x_3258_);
if (v_isShared_3257_ == 0)
{
v___x_3260_ = v___x_3256_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3254_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
else
{
lean_dec(v___x_3248_);
return v___x_3253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLetsCore___boxed(lean_object* v_e_3263_, lean_object* v_elimTrivial_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_){
_start:
{
uint8_t v_elimTrivial_boxed_3270_; lean_object* v_res_3271_; 
v_elimTrivial_boxed_3270_ = lean_unbox(v_elimTrivial_3264_);
v_res_3271_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v_e_3263_, v_elimTrivial_boxed_3270_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_);
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(lean_object* v_upperBound_3272_, lean_object* v___x_3273_, lean_object* v_pre_3274_, lean_object* v_post_3275_, uint8_t v_usedLetOnly_3276_, uint8_t v_skipConstInApp_3277_, uint8_t v_skipInstances_3278_, lean_object* v___x_3279_, lean_object* v_inst_3280_, lean_object* v_R_3281_, lean_object* v_a_3282_, lean_object* v_b_3283_, lean_object* v_c_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___redArg(v_upperBound_3272_, v___x_3273_, v_pre_3274_, v_post_3275_, v_usedLetOnly_3276_, v_skipConstInApp_3277_, v_skipInstances_3278_, v_a_3282_, v_b_3283_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3___boxed(lean_object** _args){
lean_object* v_upperBound_3293_ = _args[0];
lean_object* v___x_3294_ = _args[1];
lean_object* v_pre_3295_ = _args[2];
lean_object* v_post_3296_ = _args[3];
lean_object* v_usedLetOnly_3297_ = _args[4];
lean_object* v_skipConstInApp_3298_ = _args[5];
lean_object* v_skipInstances_3299_ = _args[6];
lean_object* v___x_3300_ = _args[7];
lean_object* v_inst_3301_ = _args[8];
lean_object* v_R_3302_ = _args[9];
lean_object* v_a_3303_ = _args[10];
lean_object* v_b_3304_ = _args[11];
lean_object* v_c_3305_ = _args[12];
lean_object* v___y_3306_ = _args[13];
lean_object* v___y_3307_ = _args[14];
lean_object* v___y_3308_ = _args[15];
lean_object* v___y_3309_ = _args[16];
lean_object* v___y_3310_ = _args[17];
lean_object* v___y_3311_ = _args[18];
lean_object* v___y_3312_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_3313_; uint8_t v_skipConstInApp_boxed_3314_; uint8_t v_skipInstances_boxed_3315_; lean_object* v_res_3316_; 
v_usedLetOnly_boxed_3313_ = lean_unbox(v_usedLetOnly_3297_);
v_skipConstInApp_boxed_3314_ = lean_unbox(v_skipConstInApp_3298_);
v_skipInstances_boxed_3315_ = lean_unbox(v_skipInstances_3299_);
v_res_3316_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__3(v_upperBound_3293_, v___x_3294_, v_pre_3295_, v_post_3296_, v_usedLetOnly_boxed_3313_, v_skipConstInApp_boxed_3314_, v_skipInstances_boxed_3315_, v___x_3300_, v_inst_3301_, v_R_3302_, v_a_3303_, v_b_3304_, v_c_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec(v___x_3300_);
lean_dec_ref(v___x_3294_);
lean_dec(v_upperBound_3293_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3317_, lean_object* v_m_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v___x_3320_; 
v___x_3320_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___redArg(v_m_3318_, v_a_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_3321_, lean_object* v_m_3322_, lean_object* v_a_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4(v_00_u03b2_3321_, v_m_3322_, v_a_3323_);
lean_dec_ref(v_a_3323_);
lean_dec_ref(v_m_3322_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_3325_, lean_object* v_name_3326_, uint8_t v_bi_3327_, lean_object* v_type_3328_, lean_object* v_k_3329_, uint8_t v_kind_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___redArg(v_name_3326_, v_bi_3327_, v_type_3328_, v_k_3329_, v_kind_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3339_, lean_object* v_name_3340_, lean_object* v_bi_3341_, lean_object* v_type_3342_, lean_object* v_k_3343_, lean_object* v_kind_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
uint8_t v_bi_boxed_3352_; uint8_t v_kind_boxed_3353_; lean_object* v_res_3354_; 
v_bi_boxed_3352_ = lean_unbox(v_bi_3341_);
v_kind_boxed_3353_ = lean_unbox(v_kind_3344_);
v_res_3354_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_3339_, v_name_3340_, v_bi_boxed_3352_, v_type_3342_, v_k_3343_, v_kind_boxed_3353_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec(v___y_3345_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(lean_object* v_00_u03b1_3355_, lean_object* v_name_3356_, lean_object* v_type_3357_, lean_object* v_val_3358_, lean_object* v_k_3359_, uint8_t v_nondep_3360_, uint8_t v_kind_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v___x_3369_; 
v___x_3369_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___redArg(v_name_3356_, v_type_3357_, v_val_3358_, v_k_3359_, v_nondep_3360_, v_kind_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10___boxed(lean_object* v_00_u03b1_3370_, lean_object* v_name_3371_, lean_object* v_type_3372_, lean_object* v_val_3373_, lean_object* v_k_3374_, lean_object* v_nondep_3375_, lean_object* v_kind_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
uint8_t v_nondep_boxed_3384_; uint8_t v_kind_boxed_3385_; lean_object* v_res_3386_; 
v_nondep_boxed_3384_ = lean_unbox(v_nondep_3375_);
v_kind_boxed_3385_ = lean_unbox(v_kind_3376_);
v_res_3386_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__7_spec__10(v_00_u03b1_3370_, v_name_3371_, v_type_3372_, v_val_3373_, v_k_3374_, v_nondep_boxed_3384_, v_kind_boxed_3385_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec(v___y_3377_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(lean_object* v_00_u03b1_3387_, lean_object* v_ref_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v___x_3394_; 
v___x_3394_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___redArg(v_ref_3388_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13___boxed(lean_object* v_00_u03b1_3395_, lean_object* v_ref_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9_spec__13(v_00_u03b1_3395_, v_ref_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(lean_object* v_00_u03b1_3403_, lean_object* v_x_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v___x_3412_; 
v___x_3412_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___redArg(v_x_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9___boxed(lean_object* v_00_u03b1_3413_, lean_object* v_x_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__9(v_00_u03b1_3413_, v_x_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec(v___y_3415_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(lean_object* v_00_u03b2_3423_, lean_object* v_m_3424_, lean_object* v_query_3425_){
_start:
{
lean_object* v___x_3426_; 
v___x_3426_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___redArg(v_m_3424_, v_query_3425_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10___boxed(lean_object* v_00_u03b2_3427_, lean_object* v_m_3428_, lean_object* v_query_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10(v_00_u03b2_3427_, v_m_3428_, v_query_3429_);
lean_dec_ref(v_query_3429_);
lean_dec_ref(v_m_3428_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11(lean_object* v_00_u03b2_3431_, lean_object* v_m_3432_){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11___redArg(v_m_3432_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11___boxed(lean_object* v_00_u03b2_3434_, lean_object* v_m_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11(v_00_u03b2_3434_, v_m_3435_);
lean_dec_ref(v_m_3435_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(lean_object* v_00_u03b2_3437_, lean_object* v_m_3438_, lean_object* v_query_3439_){
_start:
{
lean_object* v___x_3440_; 
v___x_3440_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___redArg(v_m_3438_, v_query_3439_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5___boxed(lean_object* v_00_u03b2_3441_, lean_object* v_m_3442_, lean_object* v_query_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__4_spec__5(v_00_u03b2_3441_, v_m_3442_, v_query_3443_);
lean_dec_ref(v_query_3443_);
lean_dec_ref(v_m_3442_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(lean_object* v_00_u03b2_3445_, lean_object* v_m_3446_, lean_object* v_query_3447_, lean_object* v_x_3448_, lean_object* v_x_3449_, lean_object* v_x_3450_, lean_object* v_x_3451_){
_start:
{
lean_object* v___x_3452_; 
v___x_3452_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___redArg(v_m_3446_, v_query_3447_, v_x_3448_, v_x_3449_, v_x_3450_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15___boxed(lean_object* v_00_u03b2_3453_, lean_object* v_m_3454_, lean_object* v_query_3455_, lean_object* v_x_3456_, lean_object* v_x_3457_, lean_object* v_x_3458_, lean_object* v_x_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__10_spec__15(v_00_u03b2_3453_, v_m_3454_, v_query_3455_, v_x_3456_, v_x_3457_, v_x_3458_, v_x_3459_);
lean_dec_ref(v_query_3455_);
lean_dec_ref(v_m_3454_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17(lean_object* v_00_u03b2_3461_, lean_object* v_init_3462_, lean_object* v_b_3463_){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17___redArg(v_init_3462_, v_b_3463_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17___boxed(lean_object* v_00_u03b2_3465_, lean_object* v_init_3466_, lean_object* v_b_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17(v_00_u03b2_3465_, v_init_3466_, v_b_3467_);
lean_dec_ref(v_b_3467_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17_spec__18(lean_object* v_00_u03b2_3469_, lean_object* v_b_3470_, lean_object* v_acc_3471_, lean_object* v_i_3472_){
_start:
{
lean_object* v___x_3473_; 
v___x_3473_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17_spec__18___redArg(v_b_3470_, v_acc_3471_, v_i_3472_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17_spec__18___boxed(lean_object* v_00_u03b2_3474_, lean_object* v_b_3475_, lean_object* v_acc_3476_, lean_object* v_i_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Elab_Tactic_Do_elimLetsCore_spec__0_spec__0_spec__11_spec__17_spec__18(v_00_u03b2_3474_, v_b_3475_, v_acc_3476_, v_i_3477_);
lean_dec_ref(v_b_3475_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(lean_object* v_mvarId_3479_, lean_object* v_x_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v___x_3486_; 
v___x_3486_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3479_, v_x_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3486_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3486_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
v_a_3495_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3486_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3486_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg___boxed(lean_object* v_mvarId_3503_, lean_object* v_x_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3503_, v_x_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(lean_object* v_00_u03b1_3511_, lean_object* v_mvarId_3512_, lean_object* v_x_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v___x_3519_; 
v___x_3519_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvarId_3512_, v_x_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___boxed(lean_object* v_00_u03b1_3520_, lean_object* v_mvarId_3521_, lean_object* v_x_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3(v_00_u03b1_3520_, v_mvarId_3521_, v_x_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(uint8_t v_elimTrivial_3529_, lean_object* v_as_3530_, size_t v_sz_3531_, size_t v_i_3532_, lean_object* v_b_3533_){
_start:
{
uint8_t v___x_3535_; 
v___x_3535_ = lean_usize_dec_lt(v_i_3532_, v_sz_3531_);
if (v___x_3535_ == 0)
{
lean_object* v___x_3536_; 
v___x_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3536_, 0, v_b_3533_);
return v___x_3536_;
}
else
{
lean_object* v_snd_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3584_; 
v_snd_3537_ = lean_ctor_get(v_b_3533_, 1);
v_isSharedCheck_3584_ = !lean_is_exclusive(v_b_3533_);
if (v_isSharedCheck_3584_ == 0)
{
lean_object* v_unused_3585_; 
v_unused_3585_ = lean_ctor_get(v_b_3533_, 0);
lean_dec(v_unused_3585_);
v___x_3539_ = v_b_3533_;
v_isShared_3540_ = v_isSharedCheck_3584_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_snd_3537_);
lean_dec(v_b_3533_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3584_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; lean_object* v_a_3543_; lean_object* v_a_3550_; 
v___x_3541_ = lean_box(0);
v_a_3550_ = lean_array_uget_borrowed(v_as_3530_, v_i_3532_);
if (lean_obj_tag(v_a_3550_) == 0)
{
v_a_3543_ = v_snd_3537_;
goto v___jp_3542_;
}
else
{
lean_object* v_val_3551_; lean_object* v_fst_3552_; lean_object* v_snd_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3583_; 
v_val_3551_ = lean_ctor_get(v_a_3550_, 0);
v_fst_3552_ = lean_ctor_get(v_snd_3537_, 0);
v_snd_3553_ = lean_ctor_get(v_snd_3537_, 1);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_snd_3537_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3555_ = v_snd_3537_;
v_isShared_3556_ = v_isSharedCheck_3583_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_snd_3553_);
lean_inc(v_fst_3552_);
lean_dec(v_snd_3537_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3583_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
uint8_t v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = 0;
v___x_3558_ = l_Lean_LocalDecl_value_x3f(v_val_3551_, v___x_3557_);
if (lean_obj_tag(v___x_3558_) == 1)
{
lean_object* v_val_3559_; lean_object* v___x_3560_; 
v_val_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_val_3559_);
lean_dec_ref_known(v___x_3558_, 1);
v___x_3560_ = l_Lean_LocalDecl_type(v_val_3551_);
if (lean_obj_tag(v___x_3560_) == 10)
{
lean_object* v_data_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; uint8_t v___x_3566_; 
v_data_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_data_3561_);
lean_dec_ref_known(v___x_3560_, 2);
v___x_3562_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3563_ = lean_unsigned_to_nat(2u);
v___x_3564_ = l_Lean_KVMap_getNat(v_data_3561_, v___x_3562_, v___x_3563_);
lean_dec(v_data_3561_);
v___x_3565_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3564_);
lean_dec(v___x_3564_);
v___x_3566_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3565_, v_val_3559_, v_elimTrivial_3529_);
if (v___x_3566_ == 0)
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
v___x_3567_ = l_Lean_LocalDecl_fvarId(v_val_3551_);
v___x_3568_ = l_Lean_mkFVar(v___x_3567_);
v___x_3569_ = lean_array_push(v_fst_3552_, v___x_3568_);
v___x_3570_ = lean_array_push(v_snd_3553_, v_val_3559_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 1, v___x_3570_);
lean_ctor_set(v___x_3555_, 0, v___x_3569_);
v___x_3572_ = v___x_3555_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3569_);
lean_ctor_set(v_reuseFailAlloc_3573_, 1, v___x_3570_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
v_a_3543_ = v___x_3572_;
goto v___jp_3542_;
}
}
else
{
lean_object* v___x_3575_; 
lean_dec(v_val_3559_);
if (v_isShared_3556_ == 0)
{
v___x_3575_ = v___x_3555_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_fst_3552_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v_snd_3553_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
v_a_3543_ = v___x_3575_;
goto v___jp_3542_;
}
}
}
else
{
lean_object* v___x_3578_; 
lean_dec_ref(v___x_3560_);
lean_dec(v_val_3559_);
if (v_isShared_3556_ == 0)
{
v___x_3578_ = v___x_3555_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_fst_3552_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_snd_3553_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
v_a_3543_ = v___x_3578_;
goto v___jp_3542_;
}
}
}
else
{
lean_object* v___x_3581_; 
lean_dec(v___x_3558_);
if (v_isShared_3556_ == 0)
{
v___x_3581_ = v___x_3555_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_fst_3552_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v_snd_3553_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
v_a_3543_ = v___x_3581_;
goto v___jp_3542_;
}
}
}
}
v___jp_3542_:
{
lean_object* v___x_3545_; 
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 1, v_a_3543_);
lean_ctor_set(v___x_3539_, 0, v___x_3541_);
v___x_3545_ = v___x_3539_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3541_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v_a_3543_);
v___x_3545_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
size_t v___x_3546_; size_t v___x_3547_; 
v___x_3546_ = ((size_t)1ULL);
v___x_3547_ = lean_usize_add(v_i_3532_, v___x_3546_);
v_i_3532_ = v___x_3547_;
v_b_3533_ = v___x_3545_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_elimTrivial_3586_, lean_object* v_as_3587_, lean_object* v_sz_3588_, lean_object* v_i_3589_, lean_object* v_b_3590_, lean_object* v___y_3591_){
_start:
{
uint8_t v_elimTrivial_boxed_3592_; size_t v_sz_boxed_3593_; size_t v_i_boxed_3594_; lean_object* v_res_3595_; 
v_elimTrivial_boxed_3592_ = lean_unbox(v_elimTrivial_3586_);
v_sz_boxed_3593_ = lean_unbox_usize(v_sz_3588_);
lean_dec(v_sz_3588_);
v_i_boxed_3594_ = lean_unbox_usize(v_i_3589_);
lean_dec(v_i_3589_);
v_res_3595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_boxed_3592_, v_as_3587_, v_sz_boxed_3593_, v_i_boxed_3594_, v_b_3590_);
lean_dec_ref(v_as_3587_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(uint8_t v_elimTrivial_3596_, lean_object* v_as_3597_, size_t v_sz_3598_, size_t v_i_3599_, lean_object* v_b_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
uint8_t v___x_3606_; 
v___x_3606_ = lean_usize_dec_lt(v_i_3599_, v_sz_3598_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; 
v___x_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3607_, 0, v_b_3600_);
return v___x_3607_;
}
else
{
lean_object* v_snd_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3655_; 
v_snd_3608_ = lean_ctor_get(v_b_3600_, 1);
v_isSharedCheck_3655_ = !lean_is_exclusive(v_b_3600_);
if (v_isSharedCheck_3655_ == 0)
{
lean_object* v_unused_3656_; 
v_unused_3656_ = lean_ctor_get(v_b_3600_, 0);
lean_dec(v_unused_3656_);
v___x_3610_ = v_b_3600_;
v_isShared_3611_ = v_isSharedCheck_3655_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_snd_3608_);
lean_dec(v_b_3600_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3655_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3612_; lean_object* v_a_3614_; lean_object* v_a_3621_; 
v___x_3612_ = lean_box(0);
v_a_3621_ = lean_array_uget_borrowed(v_as_3597_, v_i_3599_);
if (lean_obj_tag(v_a_3621_) == 0)
{
v_a_3614_ = v_snd_3608_;
goto v___jp_3613_;
}
else
{
lean_object* v_val_3622_; lean_object* v_fst_3623_; lean_object* v_snd_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3654_; 
v_val_3622_ = lean_ctor_get(v_a_3621_, 0);
v_fst_3623_ = lean_ctor_get(v_snd_3608_, 0);
v_snd_3624_ = lean_ctor_get(v_snd_3608_, 1);
v_isSharedCheck_3654_ = !lean_is_exclusive(v_snd_3608_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3626_ = v_snd_3608_;
v_isShared_3627_ = v_isSharedCheck_3654_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_snd_3624_);
lean_inc(v_fst_3623_);
lean_dec(v_snd_3608_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3654_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
uint8_t v___x_3628_; lean_object* v___x_3629_; 
v___x_3628_ = 0;
v___x_3629_ = l_Lean_LocalDecl_value_x3f(v_val_3622_, v___x_3628_);
if (lean_obj_tag(v___x_3629_) == 1)
{
lean_object* v_val_3630_; lean_object* v___x_3631_; 
v_val_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc(v_val_3630_);
lean_dec_ref_known(v___x_3629_, 1);
v___x_3631_ = l_Lean_LocalDecl_type(v_val_3622_);
if (lean_obj_tag(v___x_3631_) == 10)
{
lean_object* v_data_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; uint8_t v___x_3636_; uint8_t v___x_3637_; 
v_data_3632_ = lean_ctor_get(v___x_3631_, 0);
lean_inc(v_data_3632_);
lean_dec_ref_known(v___x_3631_, 2);
v___x_3633_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3634_ = lean_unsigned_to_nat(2u);
v___x_3635_ = l_Lean_KVMap_getNat(v_data_3632_, v___x_3633_, v___x_3634_);
lean_dec(v_data_3632_);
v___x_3636_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3635_);
lean_dec(v___x_3635_);
v___x_3637_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3636_, v_val_3630_, v_elimTrivial_3596_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3643_; 
v___x_3638_ = l_Lean_LocalDecl_fvarId(v_val_3622_);
v___x_3639_ = l_Lean_mkFVar(v___x_3638_);
v___x_3640_ = lean_array_push(v_fst_3623_, v___x_3639_);
v___x_3641_ = lean_array_push(v_snd_3624_, v_val_3630_);
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 1, v___x_3641_);
lean_ctor_set(v___x_3626_, 0, v___x_3640_);
v___x_3643_ = v___x_3626_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3640_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v___x_3641_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
v_a_3614_ = v___x_3643_;
goto v___jp_3613_;
}
}
else
{
lean_object* v___x_3646_; 
lean_dec(v_val_3630_);
if (v_isShared_3627_ == 0)
{
v___x_3646_ = v___x_3626_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_fst_3623_);
lean_ctor_set(v_reuseFailAlloc_3647_, 1, v_snd_3624_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
v_a_3614_ = v___x_3646_;
goto v___jp_3613_;
}
}
}
else
{
lean_object* v___x_3649_; 
lean_dec_ref(v___x_3631_);
lean_dec(v_val_3630_);
if (v_isShared_3627_ == 0)
{
v___x_3649_ = v___x_3626_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_fst_3623_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_snd_3624_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
v_a_3614_ = v___x_3649_;
goto v___jp_3613_;
}
}
}
else
{
lean_object* v___x_3652_; 
lean_dec(v___x_3629_);
if (v_isShared_3627_ == 0)
{
v___x_3652_ = v___x_3626_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_fst_3623_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_snd_3624_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
v_a_3614_ = v___x_3652_;
goto v___jp_3613_;
}
}
}
}
v___jp_3613_:
{
lean_object* v___x_3616_; 
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 1, v_a_3614_);
lean_ctor_set(v___x_3610_, 0, v___x_3612_);
v___x_3616_ = v___x_3610_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_a_3614_);
v___x_3616_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
size_t v___x_3617_; size_t v___x_3618_; lean_object* v___x_3619_; 
v___x_3617_ = ((size_t)1ULL);
v___x_3618_ = lean_usize_add(v_i_3599_, v___x_3617_);
v___x_3619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_3596_, v_as_3597_, v_sz_3598_, v___x_3618_, v___x_3616_);
return v___x_3619_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1___boxed(lean_object* v_elimTrivial_3657_, lean_object* v_as_3658_, lean_object* v_sz_3659_, lean_object* v_i_3660_, lean_object* v_b_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
uint8_t v_elimTrivial_boxed_3667_; size_t v_sz_boxed_3668_; size_t v_i_boxed_3669_; lean_object* v_res_3670_; 
v_elimTrivial_boxed_3667_ = lean_unbox(v_elimTrivial_3657_);
v_sz_boxed_3668_ = lean_unbox_usize(v_sz_3659_);
lean_dec(v_sz_3659_);
v_i_boxed_3669_ = lean_unbox_usize(v_i_3660_);
lean_dec(v_i_3660_);
v_res_3670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_boxed_3667_, v_as_3658_, v_sz_boxed_3668_, v_i_boxed_3669_, v_b_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
lean_dec_ref(v_as_3658_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(uint8_t v_elimTrivial_3671_, lean_object* v_as_3672_, size_t v_sz_3673_, size_t v_i_3674_, lean_object* v_b_3675_){
_start:
{
uint8_t v___x_3677_; 
v___x_3677_ = lean_usize_dec_lt(v_i_3674_, v_sz_3673_);
if (v___x_3677_ == 0)
{
lean_object* v___x_3678_; 
v___x_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3678_, 0, v_b_3675_);
return v___x_3678_;
}
else
{
lean_object* v_snd_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3726_; 
v_snd_3679_ = lean_ctor_get(v_b_3675_, 1);
v_isSharedCheck_3726_ = !lean_is_exclusive(v_b_3675_);
if (v_isSharedCheck_3726_ == 0)
{
lean_object* v_unused_3727_; 
v_unused_3727_ = lean_ctor_get(v_b_3675_, 0);
lean_dec(v_unused_3727_);
v___x_3681_ = v_b_3675_;
v_isShared_3682_ = v_isSharedCheck_3726_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_snd_3679_);
lean_dec(v_b_3675_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3726_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3683_; lean_object* v_a_3685_; lean_object* v_a_3692_; 
v___x_3683_ = lean_box(0);
v_a_3692_ = lean_array_uget_borrowed(v_as_3672_, v_i_3674_);
if (lean_obj_tag(v_a_3692_) == 0)
{
v_a_3685_ = v_snd_3679_;
goto v___jp_3684_;
}
else
{
lean_object* v_val_3693_; lean_object* v_fst_3694_; lean_object* v_snd_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3725_; 
v_val_3693_ = lean_ctor_get(v_a_3692_, 0);
v_fst_3694_ = lean_ctor_get(v_snd_3679_, 0);
v_snd_3695_ = lean_ctor_get(v_snd_3679_, 1);
v_isSharedCheck_3725_ = !lean_is_exclusive(v_snd_3679_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3697_ = v_snd_3679_;
v_isShared_3698_ = v_isSharedCheck_3725_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_snd_3695_);
lean_inc(v_fst_3694_);
lean_dec(v_snd_3679_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3725_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
uint8_t v___x_3699_; lean_object* v___x_3700_; 
v___x_3699_ = 0;
v___x_3700_ = l_Lean_LocalDecl_value_x3f(v_val_3693_, v___x_3699_);
if (lean_obj_tag(v___x_3700_) == 1)
{
lean_object* v_val_3701_; lean_object* v___x_3702_; 
v_val_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_val_3701_);
lean_dec_ref_known(v___x_3700_, 1);
v___x_3702_ = l_Lean_LocalDecl_type(v_val_3693_);
if (lean_obj_tag(v___x_3702_) == 10)
{
lean_object* v_data_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; uint8_t v___x_3707_; uint8_t v___x_3708_; 
v_data_3703_ = lean_ctor_get(v___x_3702_, 0);
lean_inc(v_data_3703_);
lean_dec_ref_known(v___x_3702_, 2);
v___x_3704_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3705_ = lean_unsigned_to_nat(2u);
v___x_3706_ = l_Lean_KVMap_getNat(v_data_3703_, v___x_3704_, v___x_3705_);
lean_dec(v_data_3703_);
v___x_3707_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3706_);
lean_dec(v___x_3706_);
v___x_3708_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3707_, v_val_3701_, v_elimTrivial_3671_);
if (v___x_3708_ == 0)
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3714_; 
v___x_3709_ = l_Lean_LocalDecl_fvarId(v_val_3693_);
v___x_3710_ = l_Lean_mkFVar(v___x_3709_);
v___x_3711_ = lean_array_push(v_fst_3694_, v___x_3710_);
v___x_3712_ = lean_array_push(v_snd_3695_, v_val_3701_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 1, v___x_3712_);
lean_ctor_set(v___x_3697_, 0, v___x_3711_);
v___x_3714_ = v___x_3697_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v___x_3711_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v___x_3712_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
v_a_3685_ = v___x_3714_;
goto v___jp_3684_;
}
}
else
{
lean_object* v___x_3717_; 
lean_dec(v_val_3701_);
if (v_isShared_3698_ == 0)
{
v___x_3717_ = v___x_3697_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_fst_3694_);
lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_snd_3695_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
v_a_3685_ = v___x_3717_;
goto v___jp_3684_;
}
}
}
else
{
lean_object* v___x_3720_; 
lean_dec_ref(v___x_3702_);
lean_dec(v_val_3701_);
if (v_isShared_3698_ == 0)
{
v___x_3720_ = v___x_3697_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_fst_3694_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_snd_3695_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
v_a_3685_ = v___x_3720_;
goto v___jp_3684_;
}
}
}
else
{
lean_object* v___x_3723_; 
lean_dec(v___x_3700_);
if (v_isShared_3698_ == 0)
{
v___x_3723_ = v___x_3697_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_fst_3694_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v_snd_3695_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
v_a_3685_ = v___x_3723_;
goto v___jp_3684_;
}
}
}
}
v___jp_3684_:
{
lean_object* v___x_3687_; 
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 1, v_a_3685_);
lean_ctor_set(v___x_3681_, 0, v___x_3683_);
v___x_3687_ = v___x_3681_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3683_);
lean_ctor_set(v_reuseFailAlloc_3691_, 1, v_a_3685_);
v___x_3687_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
size_t v___x_3688_; size_t v___x_3689_; 
v___x_3688_ = ((size_t)1ULL);
v___x_3689_ = lean_usize_add(v_i_3674_, v___x_3688_);
v_i_3674_ = v___x_3689_;
v_b_3675_ = v___x_3687_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg___boxed(lean_object* v_elimTrivial_3728_, lean_object* v_as_3729_, lean_object* v_sz_3730_, lean_object* v_i_3731_, lean_object* v_b_3732_, lean_object* v___y_3733_){
_start:
{
uint8_t v_elimTrivial_boxed_3734_; size_t v_sz_boxed_3735_; size_t v_i_boxed_3736_; lean_object* v_res_3737_; 
v_elimTrivial_boxed_3734_ = lean_unbox(v_elimTrivial_3728_);
v_sz_boxed_3735_ = lean_unbox_usize(v_sz_3730_);
lean_dec(v_sz_3730_);
v_i_boxed_3736_ = lean_unbox_usize(v_i_3731_);
lean_dec(v_i_3731_);
v_res_3737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_boxed_3734_, v_as_3729_, v_sz_boxed_3735_, v_i_boxed_3736_, v_b_3732_);
lean_dec_ref(v_as_3729_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(uint8_t v_elimTrivial_3738_, lean_object* v_as_3739_, size_t v_sz_3740_, size_t v_i_3741_, lean_object* v_b_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
uint8_t v___x_3748_; 
v___x_3748_ = lean_usize_dec_lt(v_i_3741_, v_sz_3740_);
if (v___x_3748_ == 0)
{
lean_object* v___x_3749_; 
v___x_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3749_, 0, v_b_3742_);
return v___x_3749_;
}
else
{
lean_object* v_snd_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3797_; 
v_snd_3750_ = lean_ctor_get(v_b_3742_, 1);
v_isSharedCheck_3797_ = !lean_is_exclusive(v_b_3742_);
if (v_isSharedCheck_3797_ == 0)
{
lean_object* v_unused_3798_; 
v_unused_3798_ = lean_ctor_get(v_b_3742_, 0);
lean_dec(v_unused_3798_);
v___x_3752_ = v_b_3742_;
v_isShared_3753_ = v_isSharedCheck_3797_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_snd_3750_);
lean_dec(v_b_3742_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3797_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3754_; lean_object* v_a_3756_; lean_object* v_a_3763_; 
v___x_3754_ = lean_box(0);
v_a_3763_ = lean_array_uget_borrowed(v_as_3739_, v_i_3741_);
if (lean_obj_tag(v_a_3763_) == 0)
{
v_a_3756_ = v_snd_3750_;
goto v___jp_3755_;
}
else
{
lean_object* v_val_3764_; lean_object* v_fst_3765_; lean_object* v_snd_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3796_; 
v_val_3764_ = lean_ctor_get(v_a_3763_, 0);
v_fst_3765_ = lean_ctor_get(v_snd_3750_, 0);
v_snd_3766_ = lean_ctor_get(v_snd_3750_, 1);
v_isSharedCheck_3796_ = !lean_is_exclusive(v_snd_3750_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3768_ = v_snd_3750_;
v_isShared_3769_ = v_isSharedCheck_3796_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_snd_3766_);
lean_inc(v_fst_3765_);
lean_dec(v_snd_3750_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3796_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
uint8_t v___x_3770_; lean_object* v___x_3771_; 
v___x_3770_ = 0;
v___x_3771_ = l_Lean_LocalDecl_value_x3f(v_val_3764_, v___x_3770_);
if (lean_obj_tag(v___x_3771_) == 1)
{
lean_object* v_val_3772_; lean_object* v___x_3773_; 
v_val_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_val_3772_);
lean_dec_ref_known(v___x_3771_, 1);
v___x_3773_ = l_Lean_LocalDecl_type(v_val_3764_);
if (lean_obj_tag(v___x_3773_) == 10)
{
lean_object* v_data_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; uint8_t v___x_3778_; uint8_t v___x_3779_; 
v_data_3774_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_data_3774_);
lean_dec_ref_known(v___x_3773_, 2);
v___x_3775_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_countUsesDecl___closed__1));
v___x_3776_ = lean_unsigned_to_nat(2u);
v___x_3777_ = l_Lean_KVMap_getNat(v_data_3774_, v___x_3775_, v___x_3776_);
lean_dec(v_data_3774_);
v___x_3778_ = l_Lean_Elab_Tactic_Do_Uses_fromNat(v___x_3777_);
lean_dec(v___x_3777_);
v___x_3779_ = l_Lean_Elab_Tactic_Do_doNotDup(v___x_3778_, v_val_3772_, v_elimTrivial_3738_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3785_; 
v___x_3780_ = l_Lean_LocalDecl_fvarId(v_val_3764_);
v___x_3781_ = l_Lean_mkFVar(v___x_3780_);
v___x_3782_ = lean_array_push(v_fst_3765_, v___x_3781_);
v___x_3783_ = lean_array_push(v_snd_3766_, v_val_3772_);
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 1, v___x_3783_);
lean_ctor_set(v___x_3768_, 0, v___x_3782_);
v___x_3785_ = v___x_3768_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3782_);
lean_ctor_set(v_reuseFailAlloc_3786_, 1, v___x_3783_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
v_a_3756_ = v___x_3785_;
goto v___jp_3755_;
}
}
else
{
lean_object* v___x_3788_; 
lean_dec(v_val_3772_);
if (v_isShared_3769_ == 0)
{
v___x_3788_ = v___x_3768_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_fst_3765_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v_snd_3766_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
v_a_3756_ = v___x_3788_;
goto v___jp_3755_;
}
}
}
else
{
lean_object* v___x_3791_; 
lean_dec_ref(v___x_3773_);
lean_dec(v_val_3772_);
if (v_isShared_3769_ == 0)
{
v___x_3791_ = v___x_3768_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_fst_3765_);
lean_ctor_set(v_reuseFailAlloc_3792_, 1, v_snd_3766_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
v_a_3756_ = v___x_3791_;
goto v___jp_3755_;
}
}
}
else
{
lean_object* v___x_3794_; 
lean_dec(v___x_3771_);
if (v_isShared_3769_ == 0)
{
v___x_3794_ = v___x_3768_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_fst_3765_);
lean_ctor_set(v_reuseFailAlloc_3795_, 1, v_snd_3766_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
v_a_3756_ = v___x_3794_;
goto v___jp_3755_;
}
}
}
}
v___jp_3755_:
{
lean_object* v___x_3758_; 
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 1, v_a_3756_);
lean_ctor_set(v___x_3752_, 0, v___x_3754_);
v___x_3758_ = v___x_3752_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3754_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_a_3756_);
v___x_3758_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
size_t v___x_3759_; size_t v___x_3760_; lean_object* v___x_3761_; 
v___x_3759_ = ((size_t)1ULL);
v___x_3760_ = lean_usize_add(v_i_3741_, v___x_3759_);
v___x_3761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_3738_, v_as_3739_, v_sz_3740_, v___x_3760_, v___x_3758_);
return v___x_3761_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3___boxed(lean_object* v_elimTrivial_3799_, lean_object* v_as_3800_, lean_object* v_sz_3801_, lean_object* v_i_3802_, lean_object* v_b_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
uint8_t v_elimTrivial_boxed_3809_; size_t v_sz_boxed_3810_; size_t v_i_boxed_3811_; lean_object* v_res_3812_; 
v_elimTrivial_boxed_3809_ = lean_unbox(v_elimTrivial_3799_);
v_sz_boxed_3810_ = lean_unbox_usize(v_sz_3801_);
lean_dec(v_sz_3801_);
v_i_boxed_3811_ = lean_unbox_usize(v_i_3802_);
lean_dec(v_i_3802_);
v_res_3812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_boxed_3809_, v_as_3800_, v_sz_boxed_3810_, v_i_boxed_3811_, v_b_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec_ref(v_as_3800_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(lean_object* v_init_3813_, uint8_t v_elimTrivial_3814_, lean_object* v_n_3815_, lean_object* v_b_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
if (lean_obj_tag(v_n_3815_) == 0)
{
lean_object* v_cs_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; size_t v_sz_3825_; size_t v___x_3826_; lean_object* v___x_3827_; 
v_cs_3822_ = lean_ctor_get(v_n_3815_, 0);
v___x_3823_ = lean_box(0);
v___x_3824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
lean_ctor_set(v___x_3824_, 1, v_b_3816_);
v_sz_3825_ = lean_array_size(v_cs_3822_);
v___x_3826_ = ((size_t)0ULL);
v___x_3827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3813_, v_elimTrivial_3814_, v_cs_3822_, v_sz_3825_, v___x_3826_, v___x_3824_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3842_; 
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3830_ = v___x_3827_;
v_isShared_3831_ = v_isSharedCheck_3842_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3827_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3842_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v_fst_3832_; 
v_fst_3832_ = lean_ctor_get(v_a_3828_, 0);
if (lean_obj_tag(v_fst_3832_) == 0)
{
lean_object* v_snd_3833_; lean_object* v___x_3834_; lean_object* v___x_3836_; 
v_snd_3833_ = lean_ctor_get(v_a_3828_, 1);
lean_inc(v_snd_3833_);
lean_dec(v_a_3828_);
v___x_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3834_, 0, v_snd_3833_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 0, v___x_3834_);
v___x_3836_ = v___x_3830_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3834_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
else
{
lean_object* v_val_3838_; lean_object* v___x_3840_; 
lean_inc_ref(v_fst_3832_);
lean_dec(v_a_3828_);
v_val_3838_ = lean_ctor_get(v_fst_3832_, 0);
lean_inc(v_val_3838_);
lean_dec_ref_known(v_fst_3832_, 1);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 0, v_val_3838_);
v___x_3840_ = v___x_3830_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_val_3838_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
v_a_3843_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3827_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3827_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
else
{
lean_object* v_vs_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; size_t v_sz_3854_; size_t v___x_3855_; lean_object* v___x_3856_; 
v_vs_3851_ = lean_ctor_get(v_n_3815_, 0);
v___x_3852_ = lean_box(0);
v___x_3853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3852_);
lean_ctor_set(v___x_3853_, 1, v_b_3816_);
v_sz_3854_ = lean_array_size(v_vs_3851_);
v___x_3855_ = ((size_t)0ULL);
v___x_3856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3(v_elimTrivial_3814_, v_vs_3851_, v_sz_3854_, v___x_3855_, v___x_3853_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3871_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3859_ = v___x_3856_;
v_isShared_3860_ = v_isSharedCheck_3871_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3856_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3871_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v_fst_3861_; 
v_fst_3861_ = lean_ctor_get(v_a_3857_, 0);
if (lean_obj_tag(v_fst_3861_) == 0)
{
lean_object* v_snd_3862_; lean_object* v___x_3863_; lean_object* v___x_3865_; 
v_snd_3862_ = lean_ctor_get(v_a_3857_, 1);
lean_inc(v_snd_3862_);
lean_dec(v_a_3857_);
v___x_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3863_, 0, v_snd_3862_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 0, v___x_3863_);
v___x_3865_ = v___x_3859_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3863_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
else
{
lean_object* v_val_3867_; lean_object* v___x_3869_; 
lean_inc_ref(v_fst_3861_);
lean_dec(v_a_3857_);
v_val_3867_ = lean_ctor_get(v_fst_3861_, 0);
lean_inc(v_val_3867_);
lean_dec_ref_known(v_fst_3861_, 1);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 0, v_val_3867_);
v___x_3869_ = v___x_3859_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_val_3867_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
v_a_3872_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3874_ = v___x_3856_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3856_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v_a_3872_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(lean_object* v_init_3880_, uint8_t v_elimTrivial_3881_, lean_object* v_as_3882_, size_t v_sz_3883_, size_t v_i_3884_, lean_object* v_b_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
uint8_t v___x_3891_; 
v___x_3891_ = lean_usize_dec_lt(v_i_3884_, v_sz_3883_);
if (v___x_3891_ == 0)
{
lean_object* v___x_3892_; 
v___x_3892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3892_, 0, v_b_3885_);
return v___x_3892_;
}
else
{
lean_object* v_snd_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3927_; 
v_snd_3893_ = lean_ctor_get(v_b_3885_, 1);
v_isSharedCheck_3927_ = !lean_is_exclusive(v_b_3885_);
if (v_isSharedCheck_3927_ == 0)
{
lean_object* v_unused_3928_; 
v_unused_3928_ = lean_ctor_get(v_b_3885_, 0);
lean_dec(v_unused_3928_);
v___x_3895_ = v_b_3885_;
v_isShared_3896_ = v_isSharedCheck_3927_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_snd_3893_);
lean_dec(v_b_3885_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3927_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v_a_3897_; lean_object* v___x_3898_; 
v_a_3897_ = lean_array_uget_borrowed(v_as_3882_, v_i_3884_);
lean_inc(v_snd_3893_);
v___x_3898_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3880_, v_elimTrivial_3881_, v_a_3897_, v_snd_3893_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3918_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3901_ = v___x_3898_;
v_isShared_3902_ = v_isSharedCheck_3918_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3898_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3918_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
if (lean_obj_tag(v_a_3899_) == 0)
{
lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3903_, 0, v_a_3899_);
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v___x_3903_);
v___x_3905_ = v___x_3895_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3903_);
lean_ctor_set(v_reuseFailAlloc_3909_, 1, v_snd_3893_);
v___x_3905_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3907_; 
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3905_);
v___x_3907_ = v___x_3901_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3905_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
else
{
lean_object* v_a_3910_; lean_object* v___x_3911_; lean_object* v___x_3913_; 
lean_del_object(v___x_3901_);
lean_dec(v_snd_3893_);
v_a_3910_ = lean_ctor_get(v_a_3899_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v_a_3899_, 1);
v___x_3911_ = lean_box(0);
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 1, v_a_3910_);
lean_ctor_set(v___x_3895_, 0, v___x_3911_);
v___x_3913_ = v___x_3895_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3911_);
lean_ctor_set(v_reuseFailAlloc_3917_, 1, v_a_3910_);
v___x_3913_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
size_t v___x_3914_; size_t v___x_3915_; 
v___x_3914_ = ((size_t)1ULL);
v___x_3915_ = lean_usize_add(v_i_3884_, v___x_3914_);
v_i_3884_ = v___x_3915_;
v_b_3885_ = v___x_3913_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
lean_del_object(v___x_3895_);
lean_dec(v_snd_3893_);
v_a_3919_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v___x_3898_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3898_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
if (v_isShared_3922_ == 0)
{
v___x_3924_ = v___x_3921_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2___boxed(lean_object* v_init_3929_, lean_object* v_elimTrivial_3930_, lean_object* v_as_3931_, lean_object* v_sz_3932_, lean_object* v_i_3933_, lean_object* v_b_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
uint8_t v_elimTrivial_boxed_3940_; size_t v_sz_boxed_3941_; size_t v_i_boxed_3942_; lean_object* v_res_3943_; 
v_elimTrivial_boxed_3940_ = lean_unbox(v_elimTrivial_3930_);
v_sz_boxed_3941_ = lean_unbox_usize(v_sz_3932_);
lean_dec(v_sz_3932_);
v_i_boxed_3942_ = lean_unbox_usize(v_i_3933_);
lean_dec(v_i_3933_);
v_res_3943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__2(v_init_3929_, v_elimTrivial_boxed_3940_, v_as_3931_, v_sz_boxed_3941_, v_i_boxed_3942_, v_b_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec_ref(v_as_3931_);
lean_dec_ref(v_init_3929_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0___boxed(lean_object* v_init_3944_, lean_object* v_elimTrivial_3945_, lean_object* v_n_3946_, lean_object* v_b_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
uint8_t v_elimTrivial_boxed_3953_; lean_object* v_res_3954_; 
v_elimTrivial_boxed_3953_ = lean_unbox(v_elimTrivial_3945_);
v_res_3954_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3944_, v_elimTrivial_boxed_3953_, v_n_3946_, v_b_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec_ref(v_n_3946_);
lean_dec_ref(v_init_3944_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(uint8_t v_elimTrivial_3955_, lean_object* v_t_3956_, lean_object* v_init_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
lean_object* v_root_3963_; lean_object* v_tail_3964_; lean_object* v___x_3965_; 
v_root_3963_ = lean_ctor_get(v_t_3956_, 0);
v_tail_3964_ = lean_ctor_get(v_t_3956_, 1);
lean_inc_ref(v_init_3957_);
v___x_3965_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0(v_init_3957_, v_elimTrivial_3955_, v_root_3963_, v_init_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
lean_dec_ref(v_init_3957_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_4002_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3968_ = v___x_3965_;
v_isShared_3969_ = v_isSharedCheck_4002_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3965_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_4002_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
if (lean_obj_tag(v_a_3966_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3972_; 
v_a_3970_ = lean_ctor_get(v_a_3966_, 0);
lean_inc(v_a_3970_);
lean_dec_ref_known(v_a_3966_, 1);
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 0, v_a_3970_);
v___x_3972_ = v___x_3968_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3970_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
else
{
lean_object* v_a_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; size_t v_sz_3977_; size_t v___x_3978_; lean_object* v___x_3979_; 
lean_del_object(v___x_3968_);
v_a_3974_ = lean_ctor_get(v_a_3966_, 0);
lean_inc(v_a_3974_);
lean_dec_ref_known(v_a_3966_, 1);
v___x_3975_ = lean_box(0);
v___x_3976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3975_);
lean_ctor_set(v___x_3976_, 1, v_a_3974_);
v_sz_3977_ = lean_array_size(v_tail_3964_);
v___x_3978_ = ((size_t)0ULL);
v___x_3979_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1(v_elimTrivial_3955_, v_tail_3964_, v_sz_3977_, v___x_3978_, v___x_3976_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3993_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3982_ = v___x_3979_;
v_isShared_3983_ = v_isSharedCheck_3993_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3979_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3993_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v_fst_3984_; 
v_fst_3984_ = lean_ctor_get(v_a_3980_, 0);
if (lean_obj_tag(v_fst_3984_) == 0)
{
lean_object* v_snd_3985_; lean_object* v___x_3987_; 
v_snd_3985_ = lean_ctor_get(v_a_3980_, 1);
lean_inc(v_snd_3985_);
lean_dec(v_a_3980_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v_snd_3985_);
v___x_3987_ = v___x_3982_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_snd_3985_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
else
{
lean_object* v_val_3989_; lean_object* v___x_3991_; 
lean_inc_ref(v_fst_3984_);
lean_dec(v_a_3980_);
v_val_3989_ = lean_ctor_get(v_fst_3984_, 0);
lean_inc(v_val_3989_);
lean_dec_ref_known(v_fst_3984_, 1);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v_val_3989_);
v___x_3991_ = v___x_3982_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_val_3989_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
else
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
v_a_3994_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3979_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3979_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
}
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
v_a_4003_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___x_3965_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_3965_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0___boxed(lean_object* v_elimTrivial_4011_, lean_object* v_t_4012_, lean_object* v_init_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
uint8_t v_elimTrivial_boxed_4019_; lean_object* v_res_4020_; 
v_elimTrivial_boxed_4019_ = lean_unbox(v_elimTrivial_4011_);
v_res_4020_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_boxed_4019_, v_t_4012_, v_init_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
lean_dec_ref(v_t_4012_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(lean_object* v_as_4021_, size_t v_sz_4022_, size_t v_i_4023_, lean_object* v_b_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
uint8_t v___x_4030_; 
v___x_4030_ = lean_usize_dec_lt(v_i_4023_, v_sz_4022_);
if (v___x_4030_ == 0)
{
lean_object* v___x_4031_; 
v___x_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4031_, 0, v_b_4024_);
return v___x_4031_;
}
else
{
lean_object* v_a_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v_a_4032_ = lean_array_uget_borrowed(v_as_4021_, v_i_4023_);
v___x_4033_ = l_Lean_Expr_fvarId_x21(v_a_4032_);
v___x_4034_ = l_Lean_MVarId_tryClear(v_b_4024_, v___x_4033_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; size_t v___x_4036_; size_t v___x_4037_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_a_4035_);
lean_dec_ref_known(v___x_4034_, 1);
v___x_4036_ = ((size_t)1ULL);
v___x_4037_ = lean_usize_add(v_i_4023_, v___x_4036_);
v_i_4023_ = v___x_4037_;
v_b_4024_ = v_a_4035_;
goto _start;
}
else
{
return v___x_4034_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2___boxed(lean_object* v_as_4039_, lean_object* v_sz_4040_, lean_object* v_i_4041_, lean_object* v_b_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
size_t v_sz_boxed_4048_; size_t v_i_boxed_4049_; lean_object* v_res_4050_; 
v_sz_boxed_4048_ = lean_unbox_usize(v_sz_4040_);
lean_dec(v_sz_4040_);
v_i_boxed_4049_ = lean_unbox_usize(v_i_4041_);
lean_dec(v_i_4041_);
v_res_4050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_as_4039_, v_sz_boxed_4048_, v_i_boxed_4049_, v_b_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec_ref(v_as_4039_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(lean_object* v_x_4051_, lean_object* v_x_4052_, lean_object* v_x_4053_, lean_object* v_x_4054_){
_start:
{
lean_object* v_ks_4055_; lean_object* v_vs_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4080_; 
v_ks_4055_ = lean_ctor_get(v_x_4051_, 0);
v_vs_4056_ = lean_ctor_get(v_x_4051_, 1);
v_isSharedCheck_4080_ = !lean_is_exclusive(v_x_4051_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4058_ = v_x_4051_;
v_isShared_4059_ = v_isSharedCheck_4080_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_vs_4056_);
lean_inc(v_ks_4055_);
lean_dec(v_x_4051_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4080_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4060_; uint8_t v___x_4061_; 
v___x_4060_ = lean_array_get_size(v_ks_4055_);
v___x_4061_ = lean_nat_dec_lt(v_x_4052_, v___x_4060_);
if (v___x_4061_ == 0)
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4065_; 
lean_dec(v_x_4052_);
v___x_4062_ = lean_array_push(v_ks_4055_, v_x_4053_);
v___x_4063_ = lean_array_push(v_vs_4056_, v_x_4054_);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 1, v___x_4063_);
lean_ctor_set(v___x_4058_, 0, v___x_4062_);
v___x_4065_ = v___x_4058_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4062_);
lean_ctor_set(v_reuseFailAlloc_4066_, 1, v___x_4063_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
else
{
lean_object* v_k_x27_4067_; uint8_t v___x_4068_; 
v_k_x27_4067_ = lean_array_fget_borrowed(v_ks_4055_, v_x_4052_);
v___x_4068_ = l_Lean_instBEqMVarId_beq(v_x_4053_, v_k_x27_4067_);
if (v___x_4068_ == 0)
{
lean_object* v___x_4070_; 
if (v_isShared_4059_ == 0)
{
v___x_4070_ = v___x_4058_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_ks_4055_);
lean_ctor_set(v_reuseFailAlloc_4074_, 1, v_vs_4056_);
v___x_4070_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = lean_unsigned_to_nat(1u);
v___x_4072_ = lean_nat_add(v_x_4052_, v___x_4071_);
lean_dec(v_x_4052_);
v_x_4051_ = v___x_4070_;
v_x_4052_ = v___x_4072_;
goto _start;
}
}
else
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4078_; 
v___x_4075_ = lean_array_fset(v_ks_4055_, v_x_4052_, v_x_4053_);
v___x_4076_ = lean_array_fset(v_vs_4056_, v_x_4052_, v_x_4054_);
lean_dec(v_x_4052_);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 1, v___x_4076_);
lean_ctor_set(v___x_4058_, 0, v___x_4075_);
v___x_4078_ = v___x_4058_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v___x_4075_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v___x_4076_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(lean_object* v_n_4081_, lean_object* v_k_4082_, lean_object* v_v_4083_){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4084_ = lean_unsigned_to_nat(0u);
v___x_4085_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_n_4081_, v___x_4084_, v_k_4082_, v_v_4083_);
return v___x_4085_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_4086_; 
v___x_4086_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(lean_object* v_x_4087_, size_t v_x_4088_, size_t v_x_4089_, lean_object* v_x_4090_, lean_object* v_x_4091_){
_start:
{
if (lean_obj_tag(v_x_4087_) == 0)
{
lean_object* v_es_4092_; size_t v___x_4093_; size_t v___x_4094_; lean_object* v_j_4095_; lean_object* v___x_4096_; uint8_t v___x_4097_; 
v_es_4092_ = lean_ctor_get(v_x_4087_, 0);
v___x_4093_ = ((size_t)31ULL);
v___x_4094_ = lean_usize_land(v_x_4088_, v___x_4093_);
v_j_4095_ = lean_usize_to_nat(v___x_4094_);
v___x_4096_ = lean_array_get_size(v_es_4092_);
v___x_4097_ = lean_nat_dec_lt(v_j_4095_, v___x_4096_);
if (v___x_4097_ == 0)
{
lean_dec(v_j_4095_);
lean_dec(v_x_4091_);
lean_dec(v_x_4090_);
return v_x_4087_;
}
else
{
lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4136_; 
lean_inc_ref(v_es_4092_);
v_isSharedCheck_4136_ = !lean_is_exclusive(v_x_4087_);
if (v_isSharedCheck_4136_ == 0)
{
lean_object* v_unused_4137_; 
v_unused_4137_ = lean_ctor_get(v_x_4087_, 0);
lean_dec(v_unused_4137_);
v___x_4099_ = v_x_4087_;
v_isShared_4100_ = v_isSharedCheck_4136_;
goto v_resetjp_4098_;
}
else
{
lean_dec(v_x_4087_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4136_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v_v_4101_; lean_object* v___x_4102_; lean_object* v_xs_x27_4103_; lean_object* v___y_4105_; 
v_v_4101_ = lean_array_fget(v_es_4092_, v_j_4095_);
v___x_4102_ = lean_box(0);
v_xs_x27_4103_ = lean_array_fset(v_es_4092_, v_j_4095_, v___x_4102_);
switch(lean_obj_tag(v_v_4101_))
{
case 0:
{
lean_object* v_key_4110_; lean_object* v_val_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4121_; 
v_key_4110_ = lean_ctor_get(v_v_4101_, 0);
v_val_4111_ = lean_ctor_get(v_v_4101_, 1);
v_isSharedCheck_4121_ = !lean_is_exclusive(v_v_4101_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4113_ = v_v_4101_;
v_isShared_4114_ = v_isSharedCheck_4121_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_val_4111_);
lean_inc(v_key_4110_);
lean_dec(v_v_4101_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4121_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
uint8_t v___x_4115_; 
v___x_4115_ = l_Lean_instBEqMVarId_beq(v_x_4090_, v_key_4110_);
if (v___x_4115_ == 0)
{
lean_object* v___x_4116_; lean_object* v___x_4117_; 
lean_del_object(v___x_4113_);
v___x_4116_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4110_, v_val_4111_, v_x_4090_, v_x_4091_);
v___x_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4116_);
v___y_4105_ = v___x_4117_;
goto v___jp_4104_;
}
else
{
lean_object* v___x_4119_; 
lean_dec(v_val_4111_);
lean_dec(v_key_4110_);
if (v_isShared_4114_ == 0)
{
lean_ctor_set(v___x_4113_, 1, v_x_4091_);
lean_ctor_set(v___x_4113_, 0, v_x_4090_);
v___x_4119_ = v___x_4113_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_x_4090_);
lean_ctor_set(v_reuseFailAlloc_4120_, 1, v_x_4091_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
v___y_4105_ = v___x_4119_;
goto v___jp_4104_;
}
}
}
}
case 1:
{
lean_object* v_node_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4134_; 
v_node_4122_ = lean_ctor_get(v_v_4101_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v_v_4101_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4124_ = v_v_4101_;
v_isShared_4125_ = v_isSharedCheck_4134_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_node_4122_);
lean_dec(v_v_4101_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4134_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
size_t v___x_4126_; size_t v___x_4127_; size_t v___x_4128_; size_t v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4132_; 
v___x_4126_ = ((size_t)5ULL);
v___x_4127_ = lean_usize_shift_right(v_x_4088_, v___x_4126_);
v___x_4128_ = ((size_t)1ULL);
v___x_4129_ = lean_usize_add(v_x_4089_, v___x_4128_);
v___x_4130_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_node_4122_, v___x_4127_, v___x_4129_, v_x_4090_, v_x_4091_);
if (v_isShared_4125_ == 0)
{
lean_ctor_set(v___x_4124_, 0, v___x_4130_);
v___x_4132_ = v___x_4124_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4130_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
v___y_4105_ = v___x_4132_;
goto v___jp_4104_;
}
}
}
default: 
{
lean_object* v___x_4135_; 
v___x_4135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4135_, 0, v_x_4090_);
lean_ctor_set(v___x_4135_, 1, v_x_4091_);
v___y_4105_ = v___x_4135_;
goto v___jp_4104_;
}
}
v___jp_4104_:
{
lean_object* v___x_4106_; lean_object* v___x_4108_; 
v___x_4106_ = lean_array_fset(v_xs_x27_4103_, v_j_4095_, v___y_4105_);
lean_dec(v_j_4095_);
if (v_isShared_4100_ == 0)
{
lean_ctor_set(v___x_4099_, 0, v___x_4106_);
v___x_4108_ = v___x_4099_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v___x_4106_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
}
else
{
lean_object* v_ks_4138_; lean_object* v_vs_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4159_; 
v_ks_4138_ = lean_ctor_get(v_x_4087_, 0);
v_vs_4139_ = lean_ctor_get(v_x_4087_, 1);
v_isSharedCheck_4159_ = !lean_is_exclusive(v_x_4087_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4141_ = v_x_4087_;
v_isShared_4142_ = v_isSharedCheck_4159_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_vs_4139_);
lean_inc(v_ks_4138_);
lean_dec(v_x_4087_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4159_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4142_ == 0)
{
v___x_4144_ = v___x_4141_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_ks_4138_);
lean_ctor_set(v_reuseFailAlloc_4158_, 1, v_vs_4139_);
v___x_4144_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
lean_object* v_newNode_4145_; uint8_t v___y_4147_; size_t v___x_4153_; uint8_t v___x_4154_; 
v_newNode_4145_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v___x_4144_, v_x_4090_, v_x_4091_);
v___x_4153_ = ((size_t)7ULL);
v___x_4154_ = lean_usize_dec_le(v___x_4153_, v_x_4089_);
if (v___x_4154_ == 0)
{
lean_object* v___x_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; 
v___x_4155_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4145_);
v___x_4156_ = lean_unsigned_to_nat(4u);
v___x_4157_ = lean_nat_dec_lt(v___x_4155_, v___x_4156_);
lean_dec(v___x_4155_);
v___y_4147_ = v___x_4157_;
goto v___jp_4146_;
}
else
{
v___y_4147_ = v___x_4154_;
goto v___jp_4146_;
}
v___jp_4146_:
{
if (v___y_4147_ == 0)
{
lean_object* v_ks_4148_; lean_object* v_vs_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v_ks_4148_ = lean_ctor_get(v_newNode_4145_, 0);
lean_inc_ref(v_ks_4148_);
v_vs_4149_ = lean_ctor_get(v_newNode_4145_, 1);
lean_inc_ref(v_vs_4149_);
lean_dec_ref(v_newNode_4145_);
v___x_4150_ = lean_unsigned_to_nat(0u);
v___x_4151_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___closed__0);
v___x_4152_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_x_4089_, v_ks_4148_, v_vs_4149_, v___x_4150_, v___x_4151_);
lean_dec_ref(v_vs_4149_);
lean_dec_ref(v_ks_4148_);
return v___x_4152_;
}
else
{
return v_newNode_4145_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(size_t v_depth_4160_, lean_object* v_keys_4161_, lean_object* v_vals_4162_, lean_object* v_i_4163_, lean_object* v_entries_4164_){
_start:
{
lean_object* v___x_4165_; uint8_t v___x_4166_; 
v___x_4165_ = lean_array_get_size(v_keys_4161_);
v___x_4166_ = lean_nat_dec_lt(v_i_4163_, v___x_4165_);
if (v___x_4166_ == 0)
{
lean_dec(v_i_4163_);
return v_entries_4164_;
}
else
{
lean_object* v_k_4167_; lean_object* v_v_4168_; uint64_t v___x_4169_; size_t v_h_4170_; size_t v___x_4171_; lean_object* v___x_4172_; size_t v___x_4173_; size_t v___x_4174_; size_t v___x_4175_; size_t v_h_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v_k_4167_ = lean_array_fget_borrowed(v_keys_4161_, v_i_4163_);
v_v_4168_ = lean_array_fget_borrowed(v_vals_4162_, v_i_4163_);
v___x_4169_ = l_Lean_instHashableMVarId_hash(v_k_4167_);
v_h_4170_ = lean_uint64_to_usize(v___x_4169_);
v___x_4171_ = ((size_t)5ULL);
v___x_4172_ = lean_unsigned_to_nat(1u);
v___x_4173_ = ((size_t)1ULL);
v___x_4174_ = lean_usize_sub(v_depth_4160_, v___x_4173_);
v___x_4175_ = lean_usize_mul(v___x_4171_, v___x_4174_);
v_h_4176_ = lean_usize_shift_right(v_h_4170_, v___x_4175_);
v___x_4177_ = lean_nat_add(v_i_4163_, v___x_4172_);
lean_dec(v_i_4163_);
lean_inc(v_v_4168_);
lean_inc(v_k_4167_);
v___x_4178_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_entries_4164_, v_h_4176_, v_depth_4160_, v_k_4167_, v_v_4168_);
v_i_4163_ = v___x_4177_;
v_entries_4164_ = v___x_4178_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg___boxed(lean_object* v_depth_4180_, lean_object* v_keys_4181_, lean_object* v_vals_4182_, lean_object* v_i_4183_, lean_object* v_entries_4184_){
_start:
{
size_t v_depth_boxed_4185_; lean_object* v_res_4186_; 
v_depth_boxed_4185_ = lean_unbox_usize(v_depth_4180_);
lean_dec(v_depth_4180_);
v_res_4186_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_boxed_4185_, v_keys_4181_, v_vals_4182_, v_i_4183_, v_entries_4184_);
lean_dec_ref(v_vals_4182_);
lean_dec_ref(v_keys_4181_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_x_4187_, lean_object* v_x_4188_, lean_object* v_x_4189_, lean_object* v_x_4190_, lean_object* v_x_4191_){
_start:
{
size_t v_x_7962__boxed_4192_; size_t v_x_7963__boxed_4193_; lean_object* v_res_4194_; 
v_x_7962__boxed_4192_ = lean_unbox_usize(v_x_4188_);
lean_dec(v_x_4188_);
v_x_7963__boxed_4193_ = lean_unbox_usize(v_x_4189_);
lean_dec(v_x_4189_);
v_res_4194_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4187_, v_x_7962__boxed_4192_, v_x_7963__boxed_4193_, v_x_4190_, v_x_4191_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(lean_object* v_x_4195_, lean_object* v_x_4196_, lean_object* v_x_4197_){
_start:
{
uint64_t v___x_4198_; size_t v___x_4199_; size_t v___x_4200_; lean_object* v___x_4201_; 
v___x_4198_ = l_Lean_instHashableMVarId_hash(v_x_4196_);
v___x_4199_ = lean_uint64_to_usize(v___x_4198_);
v___x_4200_ = ((size_t)1ULL);
v___x_4201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4195_, v___x_4199_, v___x_4200_, v_x_4196_, v_x_4197_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(lean_object* v_mvarId_4202_, lean_object* v_val_4203_, lean_object* v___y_4204_){
_start:
{
lean_object* v___x_4206_; lean_object* v_mctx_4207_; lean_object* v_cache_4208_; lean_object* v_zetaDeltaFVarIds_4209_; lean_object* v_postponed_4210_; lean_object* v_diag_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4240_; 
v___x_4206_ = lean_st_ref_take(v___y_4204_);
v_mctx_4207_ = lean_ctor_get(v___x_4206_, 0);
v_cache_4208_ = lean_ctor_get(v___x_4206_, 1);
v_zetaDeltaFVarIds_4209_ = lean_ctor_get(v___x_4206_, 2);
v_postponed_4210_ = lean_ctor_get(v___x_4206_, 3);
v_diag_4211_ = lean_ctor_get(v___x_4206_, 4);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4213_ = v___x_4206_;
v_isShared_4214_ = v_isSharedCheck_4240_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_diag_4211_);
lean_inc(v_postponed_4210_);
lean_inc(v_zetaDeltaFVarIds_4209_);
lean_inc(v_cache_4208_);
lean_inc(v_mctx_4207_);
lean_dec(v___x_4206_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4240_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v_depth_4215_; lean_object* v_levelAssignDepth_4216_; lean_object* v_lmvarCounter_4217_; lean_object* v_mvarCounter_4218_; lean_object* v_lDecls_4219_; lean_object* v_decls_4220_; lean_object* v_userNames_4221_; lean_object* v_lAssignment_4222_; lean_object* v_eAssignment_4223_; lean_object* v_dAssignment_4224_; lean_object* v_instanceTypedMVars_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4239_; 
v_depth_4215_ = lean_ctor_get(v_mctx_4207_, 0);
v_levelAssignDepth_4216_ = lean_ctor_get(v_mctx_4207_, 1);
v_lmvarCounter_4217_ = lean_ctor_get(v_mctx_4207_, 2);
v_mvarCounter_4218_ = lean_ctor_get(v_mctx_4207_, 3);
v_lDecls_4219_ = lean_ctor_get(v_mctx_4207_, 4);
v_decls_4220_ = lean_ctor_get(v_mctx_4207_, 5);
v_userNames_4221_ = lean_ctor_get(v_mctx_4207_, 6);
v_lAssignment_4222_ = lean_ctor_get(v_mctx_4207_, 7);
v_eAssignment_4223_ = lean_ctor_get(v_mctx_4207_, 8);
v_dAssignment_4224_ = lean_ctor_get(v_mctx_4207_, 9);
v_instanceTypedMVars_4225_ = lean_ctor_get(v_mctx_4207_, 10);
v_isSharedCheck_4239_ = !lean_is_exclusive(v_mctx_4207_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4227_ = v_mctx_4207_;
v_isShared_4228_ = v_isSharedCheck_4239_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_instanceTypedMVars_4225_);
lean_inc(v_dAssignment_4224_);
lean_inc(v_eAssignment_4223_);
lean_inc(v_lAssignment_4222_);
lean_inc(v_userNames_4221_);
lean_inc(v_decls_4220_);
lean_inc(v_lDecls_4219_);
lean_inc(v_mvarCounter_4218_);
lean_inc(v_lmvarCounter_4217_);
lean_inc(v_levelAssignDepth_4216_);
lean_inc(v_depth_4215_);
lean_dec(v_mctx_4207_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4239_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4229_; lean_object* v___x_4231_; 
v___x_4229_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_eAssignment_4223_, v_mvarId_4202_, v_val_4203_);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 8, v___x_4229_);
v___x_4231_ = v___x_4227_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_depth_4215_);
lean_ctor_set(v_reuseFailAlloc_4238_, 1, v_levelAssignDepth_4216_);
lean_ctor_set(v_reuseFailAlloc_4238_, 2, v_lmvarCounter_4217_);
lean_ctor_set(v_reuseFailAlloc_4238_, 3, v_mvarCounter_4218_);
lean_ctor_set(v_reuseFailAlloc_4238_, 4, v_lDecls_4219_);
lean_ctor_set(v_reuseFailAlloc_4238_, 5, v_decls_4220_);
lean_ctor_set(v_reuseFailAlloc_4238_, 6, v_userNames_4221_);
lean_ctor_set(v_reuseFailAlloc_4238_, 7, v_lAssignment_4222_);
lean_ctor_set(v_reuseFailAlloc_4238_, 8, v___x_4229_);
lean_ctor_set(v_reuseFailAlloc_4238_, 9, v_dAssignment_4224_);
lean_ctor_set(v_reuseFailAlloc_4238_, 10, v_instanceTypedMVars_4225_);
v___x_4231_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
lean_object* v___x_4233_; 
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 0, v___x_4231_);
v___x_4233_ = v___x_4213_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4231_);
lean_ctor_set(v_reuseFailAlloc_4237_, 1, v_cache_4208_);
lean_ctor_set(v_reuseFailAlloc_4237_, 2, v_zetaDeltaFVarIds_4209_);
lean_ctor_set(v_reuseFailAlloc_4237_, 3, v_postponed_4210_);
lean_ctor_set(v_reuseFailAlloc_4237_, 4, v_diag_4211_);
v___x_4233_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
v___x_4234_ = lean_st_ref_put(v___y_4204_, v___x_4233_);
v___x_4235_ = lean_box(0);
v___x_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4236_, 0, v___x_4235_);
return v___x_4236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg___boxed(lean_object* v_mvarId_4241_, lean_object* v_val_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4241_, v_val_4242_, v___y_4243_);
lean_dec(v___y_4243_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0(lean_object* v_mvar_4248_, uint8_t v_elimTrivial_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
lean_object* v___x_4255_; 
lean_inc(v_mvar_4248_);
v___x_4255_ = l_Lean_MVarId_getType(v_mvar_4248_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
if (lean_obj_tag(v___x_4255_) == 0)
{
lean_object* v_a_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_a_4256_);
lean_dec_ref_known(v___x_4255_, 1);
v___x_4257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_PersistentArray_foldrM___at___00Lean_LocalContext_foldrM___at___00Lean_Elab_Tactic_Do_countUsesLCtx_spec__0_spec__0_spec__2___closed__0));
v___x_4258_ = l_Lean_Elab_Tactic_Do_countUses(v_a_4256_, v___x_4257_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
if (lean_obj_tag(v___x_4258_) == 0)
{
lean_object* v_a_4259_; lean_object* v_fst_4260_; lean_object* v_snd_4261_; lean_object* v_lctx_4262_; lean_object* v___x_4263_; 
v_a_4259_ = lean_ctor_get(v___x_4258_, 0);
lean_inc(v_a_4259_);
lean_dec_ref_known(v___x_4258_, 1);
v_fst_4260_ = lean_ctor_get(v_a_4259_, 0);
lean_inc(v_fst_4260_);
v_snd_4261_ = lean_ctor_get(v_a_4259_, 1);
lean_inc(v_snd_4261_);
lean_dec(v_a_4259_);
v_lctx_4262_ = lean_ctor_get(v___y_4250_, 2);
lean_inc_ref(v_lctx_4262_);
v___x_4263_ = l_Lean_Elab_Tactic_Do_countUsesLCtx(v_lctx_4262_, v_snd_4261_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
if (lean_obj_tag(v___x_4263_) == 0)
{
lean_object* v_a_4264_; lean_object* v___x_4265_; lean_object* v_decls_4266_; lean_object* v___x_4267_; 
v_a_4264_ = lean_ctor_get(v___x_4263_, 0);
lean_inc(v_a_4264_);
lean_dec_ref_known(v___x_4263_, 1);
v___x_4265_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___closed__0));
v_decls_4266_ = lean_ctor_get(v_a_4264_, 1);
lean_inc_ref(v_decls_4266_);
lean_dec(v_a_4264_);
v___x_4267_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0(v_elimTrivial_4249_, v_decls_4266_, v___x_4265_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
lean_dec_ref(v_decls_4266_);
if (lean_obj_tag(v___x_4267_) == 0)
{
lean_object* v_a_4268_; lean_object* v_fst_4269_; lean_object* v_snd_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v_a_4268_ = lean_ctor_get(v___x_4267_, 0);
lean_inc(v_a_4268_);
lean_dec_ref_known(v___x_4267_, 1);
v_fst_4269_ = lean_ctor_get(v_a_4268_, 0);
lean_inc(v_fst_4269_);
v_snd_4270_ = lean_ctor_get(v_a_4268_, 1);
lean_inc(v_snd_4270_);
lean_dec(v_a_4268_);
v___x_4271_ = l_Lean_Expr_replaceFVars(v_fst_4260_, v_fst_4269_, v_snd_4270_);
lean_dec(v_snd_4270_);
lean_dec(v_fst_4260_);
v___x_4272_ = l_Lean_Elab_Tactic_Do_elimLetsCore(v___x_4271_, v_elimTrivial_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v_a_4273_; lean_object* v___x_4274_; 
v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
lean_inc(v_a_4273_);
lean_dec_ref_known(v___x_4272_, 1);
lean_inc(v_mvar_4248_);
v___x_4274_ = l_Lean_MVarId_getTag(v_mvar_4248_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v_a_4275_; lean_object* v___x_4276_; 
v_a_4275_ = lean_ctor_get(v___x_4274_, 0);
lean_inc(v_a_4275_);
lean_dec_ref_known(v___x_4274_, 1);
v___x_4276_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4273_, v_a_4275_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_object* v_a_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; size_t v_sz_4280_; size_t v___x_4281_; lean_object* v___x_4282_; 
v_a_4277_ = lean_ctor_get(v___x_4276_, 0);
lean_inc_n(v_a_4277_, 2);
lean_dec_ref_known(v___x_4276_, 1);
v___x_4278_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvar_4248_, v_a_4277_, v___y_4251_);
lean_dec_ref(v___x_4278_);
v___x_4279_ = l_Lean_Expr_mvarId_x21(v_a_4277_);
lean_dec(v_a_4277_);
v_sz_4280_ = lean_array_size(v_fst_4269_);
v___x_4281_ = ((size_t)0ULL);
v___x_4282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_elimLets_spec__2(v_fst_4269_, v_sz_4280_, v___x_4281_, v___x_4279_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
lean_dec_ref(v___y_4250_);
lean_dec(v_fst_4269_);
return v___x_4282_;
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
lean_dec(v_fst_4269_);
lean_dec_ref(v___y_4250_);
lean_dec(v_mvar_4248_);
v_a_4283_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4276_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4276_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4298_; 
lean_dec(v_a_4273_);
lean_dec(v_fst_4269_);
lean_dec_ref(v___y_4250_);
lean_dec(v_mvar_4248_);
v_a_4291_ = lean_ctor_get(v___x_4274_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4293_ = v___x_4274_;
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4274_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4294_ == 0)
{
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4291_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
}
}
else
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
lean_dec(v_fst_4269_);
lean_dec_ref(v___y_4250_);
lean_dec(v_mvar_4248_);
v_a_4299_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4301_ = v___x_4272_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4272_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4302_ == 0)
{
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_a_4299_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
}
}
else
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4314_; 
lean_dec(v_fst_4260_);
lean_dec_ref(v___y_4250_);
lean_dec(v_mvar_4248_);
v_a_4307_ = lean_ctor_get(v___x_4267_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4267_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4309_ = v___x_4267_;
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4267_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_a_4307_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
}
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4322_; 
lean_dec(v_fst_4260_);
lean_dec_ref(v___y_4250_);
lean_dec(v_mvar_4248_);
v_a_4315_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4317_ = v___x_4263_;
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4263_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4320_; 
if (v_isShared_4318_ == 0)
{
v___x_4320_ = v___x_4317_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4315_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
return v___x_4320_;
}
}
}
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
lean_dec_ref(v___y_4250_);
lean_dec(v_mvar_4248_);
v_a_4323_ = lean_ctor_get(v___x_4258_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4258_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4258_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4258_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
lean_dec_ref(v___y_4250_);
lean_dec(v_mvar_4248_);
v_a_4331_ = lean_ctor_get(v___x_4255_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4255_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4255_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4255_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed(lean_object* v_mvar_4339_, lean_object* v_elimTrivial_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
uint8_t v_elimTrivial_boxed_4346_; lean_object* v_res_4347_; 
v_elimTrivial_boxed_4346_ = lean_unbox(v_elimTrivial_4340_);
v_res_4347_ = l_Lean_Elab_Tactic_Do_elimLets___lam__0(v_mvar_4339_, v_elimTrivial_boxed_4346_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v___y_4342_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets(lean_object* v_mvar_4348_, uint8_t v_elimTrivial_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_){
_start:
{
lean_object* v___x_4355_; lean_object* v___f_4356_; lean_object* v___x_4357_; 
v___x_4355_ = lean_box(v_elimTrivial_4349_);
lean_inc(v_mvar_4348_);
v___f_4356_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elimLets___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4356_, 0, v_mvar_4348_);
lean_closure_set(v___f_4356_, 1, v___x_4355_);
v___x_4357_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_elimLets_spec__3___redArg(v_mvar_4348_, v___f_4356_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_elimLets___boxed(lean_object* v_mvar_4358_, lean_object* v_elimTrivial_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_){
_start:
{
uint8_t v_elimTrivial_boxed_4365_; lean_object* v_res_4366_; 
v_elimTrivial_boxed_4365_ = lean_unbox(v_elimTrivial_4359_);
v_res_4366_ = l_Lean_Elab_Tactic_Do_elimLets(v_mvar_4358_, v_elimTrivial_boxed_4365_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_);
lean_dec(v_a_4363_);
lean_dec_ref(v_a_4362_);
lean_dec(v_a_4361_);
lean_dec_ref(v_a_4360_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(lean_object* v_mvarId_4367_, lean_object* v_val_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v___x_4374_; 
v___x_4374_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___redArg(v_mvarId_4367_, v_val_4368_, v___y_4370_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1___boxed(lean_object* v_mvarId_4375_, lean_object* v_val_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v_res_4382_; 
v_res_4382_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1(v_mvarId_4375_, v_val_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
return v_res_4382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3(lean_object* v_00_u03b2_4383_, lean_object* v_x_4384_, lean_object* v_x_4385_, lean_object* v_x_4386_){
_start:
{
lean_object* v___x_4387_; 
v___x_4387_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3___redArg(v_x_4384_, v_x_4385_, v_x_4386_);
return v___x_4387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(uint8_t v_elimTrivial_4388_, lean_object* v_as_4389_, size_t v_sz_4390_, size_t v_i_4391_, lean_object* v_b_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
lean_object* v___x_4398_; 
v___x_4398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___redArg(v_elimTrivial_4388_, v_as_4389_, v_sz_4390_, v_i_4391_, v_b_4392_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5___boxed(lean_object* v_elimTrivial_4399_, lean_object* v_as_4400_, lean_object* v_sz_4401_, lean_object* v_i_4402_, lean_object* v_b_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
uint8_t v_elimTrivial_boxed_4409_; size_t v_sz_boxed_4410_; size_t v_i_boxed_4411_; lean_object* v_res_4412_; 
v_elimTrivial_boxed_4409_ = lean_unbox(v_elimTrivial_4399_);
v_sz_boxed_4410_ = lean_unbox_usize(v_sz_4401_);
lean_dec(v_sz_4401_);
v_i_boxed_4411_ = lean_unbox_usize(v_i_4402_);
lean_dec(v_i_4402_);
v_res_4412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__1_spec__5(v_elimTrivial_boxed_4409_, v_as_4400_, v_sz_boxed_4410_, v_i_boxed_4411_, v_b_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec_ref(v_as_4400_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_4413_, lean_object* v_x_4414_, size_t v_x_4415_, size_t v_x_4416_, lean_object* v_x_4417_, lean_object* v_x_4418_){
_start:
{
lean_object* v___x_4419_; 
v___x_4419_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___redArg(v_x_4414_, v_x_4415_, v_x_4416_, v_x_4417_, v_x_4418_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_4420_, lean_object* v_x_4421_, lean_object* v_x_4422_, lean_object* v_x_4423_, lean_object* v_x_4424_, lean_object* v_x_4425_){
_start:
{
size_t v_x_8412__boxed_4426_; size_t v_x_8413__boxed_4427_; lean_object* v_res_4428_; 
v_x_8412__boxed_4426_ = lean_unbox_usize(v_x_4422_);
lean_dec(v_x_4422_);
v_x_8413__boxed_4427_ = lean_unbox_usize(v_x_4423_);
lean_dec(v_x_4423_);
v_res_4428_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8(v_00_u03b2_4420_, v_x_4421_, v_x_8412__boxed_4426_, v_x_8413__boxed_4427_, v_x_4424_, v_x_4425_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(uint8_t v_elimTrivial_4429_, lean_object* v_as_4430_, size_t v_sz_4431_, size_t v_i_4432_, lean_object* v_b_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v___x_4439_; 
v___x_4439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___redArg(v_elimTrivial_4429_, v_as_4430_, v_sz_4431_, v_i_4432_, v_b_4433_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6___boxed(lean_object* v_elimTrivial_4440_, lean_object* v_as_4441_, lean_object* v_sz_4442_, lean_object* v_i_4443_, lean_object* v_b_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
uint8_t v_elimTrivial_boxed_4450_; size_t v_sz_boxed_4451_; size_t v_i_boxed_4452_; lean_object* v_res_4453_; 
v_elimTrivial_boxed_4450_ = lean_unbox(v_elimTrivial_4440_);
v_sz_boxed_4451_ = lean_unbox_usize(v_sz_4442_);
lean_dec(v_sz_4442_);
v_i_boxed_4452_ = lean_unbox_usize(v_i_4443_);
lean_dec(v_i_4443_);
v_res_4453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_Do_elimLets_spec__0_spec__0_spec__3_spec__6(v_elimTrivial_boxed_4450_, v_as_4441_, v_sz_boxed_4451_, v_i_boxed_4452_, v_b_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
lean_dec_ref(v_as_4441_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11(lean_object* v_00_u03b2_4454_, lean_object* v_n_4455_, lean_object* v_k_4456_, lean_object* v_v_4457_){
_start:
{
lean_object* v___x_4458_; 
v___x_4458_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11___redArg(v_n_4455_, v_k_4456_, v_v_4457_);
return v___x_4458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(lean_object* v_00_u03b2_4459_, size_t v_depth_4460_, lean_object* v_keys_4461_, lean_object* v_vals_4462_, lean_object* v_heq_4463_, lean_object* v_i_4464_, lean_object* v_entries_4465_){
_start:
{
lean_object* v___x_4466_; 
v___x_4466_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___redArg(v_depth_4460_, v_keys_4461_, v_vals_4462_, v_i_4464_, v_entries_4465_);
return v___x_4466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12___boxed(lean_object* v_00_u03b2_4467_, lean_object* v_depth_4468_, lean_object* v_keys_4469_, lean_object* v_vals_4470_, lean_object* v_heq_4471_, lean_object* v_i_4472_, lean_object* v_entries_4473_){
_start:
{
size_t v_depth_boxed_4474_; lean_object* v_res_4475_; 
v_depth_boxed_4474_ = lean_unbox_usize(v_depth_4468_);
lean_dec(v_depth_4468_);
v_res_4475_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__12(v_00_u03b2_4467_, v_depth_boxed_4474_, v_keys_4469_, v_vals_4470_, v_heq_4471_, v_i_4472_, v_entries_4473_);
lean_dec_ref(v_vals_4470_);
lean_dec_ref(v_keys_4469_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_4476_, lean_object* v_x_4477_, lean_object* v_x_4478_, lean_object* v_x_4479_, lean_object* v_x_4480_){
_start:
{
lean_object* v___x_4481_; 
v___x_4481_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_elimLets_spec__1_spec__3_spec__8_spec__11_spec__12___redArg(v_x_4477_, v_x_4478_, v_x_4479_, v_x_4480_);
return v___x_4481_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_LetElim(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Do_instInhabitedUses_default = _init_l_Lean_Elab_Tactic_Do_instInhabitedUses_default();
l_Lean_Elab_Tactic_Do_instInhabitedUses = _init_l_Lean_Elab_Tactic_Do_instInhabitedUses();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_LetElim(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1 = _init_l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_BVarUses_single___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_LetElim(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_LetElim(builtin);
}
#ifdef __cplusplus
}
#endif
